// Lean compiler output
// Module: Init.Internal.Order.MonadTail
// Imports: Init.Internal.Order.Basic Init.System.ST
use crate::r#gen::Init::Internal::Order::Basic::{
    initialize_Init_Internal_Order_Basic, runtime_initialize_Init_Internal_Order_Basic,
};
use crate::r#gen::Init::System::ST::{
    initialize_Init_System_ST, runtime_initialize_Init_System_ST,
};
pub static l_Lean_Order_instMonadTailId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Order_instMonadTailId___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Order_instMonadTailId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Order_instMonadTailId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailStateTOfNonempty___closed__0_value:
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
    m_fun: l_Lean_Order_instMonadTailStateTOfNonempty___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Order_instMonadTailStateTOfNonempty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailStateTOfNonempty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailExcept___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Order_instMonadTailExcept___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Order_instMonadTailExcept___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailExcept___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailOption___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Order_instMonadTailOption___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Order_instMonadTailOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Order_instMonadTailOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailReaderT___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Order_instMonadTailStateTOfNonempty___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Order_instMonadTailReaderT___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailReaderT___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailST___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Order_instMonadTailST___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Order_instMonadTailST___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailST___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailBaseIO___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Order_instMonadTailBaseIO___aux__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Order_instMonadTailBaseIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailBaseIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Order_instMonadTailBaseIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailBaseIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailESTOfNonempty___closed__0_value:
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
    m_fun: l_Lean_Order_instMonadTailESTOfNonempty___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Order_instMonadTailESTOfNonempty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailESTOfNonempty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailEIOOfNonempty___closed__0_value:
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
    m_fun: l_Lean_Order_instMonadTailEIOOfNonempty___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Order_instMonadTailEIOOfNonempty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailEIOOfNonempty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_instMonadTailIO___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Order_instMonadTailEIOOfNonempty___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Order_instMonadTailIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Order_instMonadTailIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_instMonadTailIO___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Order_instMonadTailId___lam__0(
    mut v_x_127_: *mut leanh::LeanObject,
    mut v_inst_128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_129_ = leanh::lean_box(0);
    return v___x_129_;
}
pub unsafe fn l_Lean_Order_instMonadTailStateTOfNonempty___lam__0(
    mut v_00_u03b1_132_: *mut leanh::LeanObject,
    mut v_inst_133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = leanh::lean_box(0);
    return v___x_134_;
}
pub unsafe fn l_Lean_Order_instMonadTailStateTOfNonempty(
    mut v_00_u03c3_136_: *mut leanh::LeanObject,
    mut v_m_137_: *mut leanh::LeanObject,
    mut v_inst_138_: *mut leanh::LeanObject,
    mut v_inst_139_: *mut leanh::LeanObject,
    mut v_inst_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_141_ = l_Lean_Order_instMonadTailStateTOfNonempty___closed__0;
    return v___f_141_;
}
pub unsafe fn l_Lean_Order_instMonadTailStateTOfNonempty___boxed(
    mut v_00_u03c3_142_: *mut leanh::LeanObject,
    mut v_m_143_: *mut leanh::LeanObject,
    mut v_inst_144_: *mut leanh::LeanObject,
    mut v_inst_145_: *mut leanh::LeanObject,
    mut v_inst_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Lean_Order_instMonadTailStateTOfNonempty(
        v_00_u03c3_142_,
        v_m_143_,
        v_inst_144_,
        v_inst_145_,
        v_inst_146_,
    );
    leanh::lean_dec_ref(v_inst_145_);
    leanh::lean_dec_ref(v_inst_144_);
    return v_res_147_;
}
pub unsafe fn l_Lean_Order_instMonadTailExceptT___redArg___lam__0(
    mut v_inst_148_: *mut leanh::LeanObject,
    mut v_00_u03b2_149_: *mut leanh::LeanObject,
    mut v_inst_150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_151_ = leanh::lean_apply_2(
        v_inst_148_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_151_;
}
pub unsafe fn l_Lean_Order_instMonadTailExceptT___redArg(
    mut v_inst_152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_153_ = leanh::lean_alloc_closure(
        l_Lean_Order_instMonadTailExceptT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_153_, 0, v_inst_152_);
    return v___f_153_;
}
pub unsafe fn l_Lean_Order_instMonadTailExceptT(
    mut v_00_u03b5_154_: *mut leanh::LeanObject,
    mut v_m_155_: *mut leanh::LeanObject,
    mut v_inst_156_: *mut leanh::LeanObject,
    mut v_inst_157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_158_ = leanh::lean_alloc_closure(
        l_Lean_Order_instMonadTailExceptT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_158_, 0, v_inst_157_);
    return v___f_158_;
}
pub unsafe fn l_Lean_Order_instMonadTailExceptT___boxed(
    mut v_00_u03b5_159_: *mut leanh::LeanObject,
    mut v_m_160_: *mut leanh::LeanObject,
    mut v_inst_161_: *mut leanh::LeanObject,
    mut v_inst_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_163_ =
        l_Lean_Order_instMonadTailExceptT(v_00_u03b5_159_, v_m_160_, v_inst_161_, v_inst_162_);
    leanh::lean_dec_ref(v_inst_161_);
    return v_res_163_;
}
pub unsafe fn l_Lean_Order_instMonadTailExcept___lam__0(
    mut v_00_u03b2_164_: *mut leanh::LeanObject,
    mut v_inst_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = leanh::lean_box(0);
    return v___x_166_;
}
pub unsafe fn l_Lean_Order_instMonadTailExcept(
    mut v_00_u03b5_168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_169_ = l_Lean_Order_instMonadTailExcept___closed__0;
    return v___f_169_;
}
pub unsafe fn l_Lean_Order_instMonadTailOptionT___redArg(
    mut v_inst_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_171_ = leanh::lean_alloc_closure(
        l_Lean_Order_instMonadTailExceptT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_171_, 0, v_inst_170_);
    return v___f_171_;
}
pub unsafe fn l_Lean_Order_instMonadTailOptionT(
    mut v_m_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_inst_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_175_ = leanh::lean_alloc_closure(
        l_Lean_Order_instMonadTailExceptT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_175_, 0, v_inst_174_);
    return v___f_175_;
}
pub unsafe fn l_Lean_Order_instMonadTailOptionT___boxed(
    mut v_m_176_: *mut leanh::LeanObject,
    mut v_inst_177_: *mut leanh::LeanObject,
    mut v_inst_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_179_ = l_Lean_Order_instMonadTailOptionT(v_m_176_, v_inst_177_, v_inst_178_);
    leanh::lean_dec_ref(v_inst_177_);
    return v_res_179_;
}
pub unsafe fn l_Lean_Order_instMonadTailOption___lam__0(
    mut v_x_180_: *mut leanh::LeanObject,
    mut v_inst_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = leanh::lean_box(0);
    return v___x_182_;
}
pub unsafe fn l_Lean_Order_instMonadTailReaderT(
    mut v_00_u03c1_186_: *mut leanh::LeanObject,
    mut v_m_187_: *mut leanh::LeanObject,
    mut v_inst_188_: *mut leanh::LeanObject,
    mut v_inst_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_190_ = l_Lean_Order_instMonadTailReaderT___closed__0;
    return v___f_190_;
}
pub unsafe fn l_Lean_Order_instMonadTailReaderT___boxed(
    mut v_00_u03c1_191_: *mut leanh::LeanObject,
    mut v_m_192_: *mut leanh::LeanObject,
    mut v_inst_193_: *mut leanh::LeanObject,
    mut v_inst_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_195_ =
        l_Lean_Order_instMonadTailReaderT(v_00_u03c1_191_, v_m_192_, v_inst_193_, v_inst_194_);
    leanh::lean_dec_ref(v_inst_194_);
    leanh::lean_dec_ref(v_inst_193_);
    return v_res_195_;
}
pub unsafe fn l_Lean_Order_instCCPOSTOfNonempty(
    mut v_00_u03b1_196_: *mut leanh::LeanObject,
    mut v_00_u03c3_197_: *mut leanh::LeanObject,
    mut v_inst_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_199_ = leanh::lean_box(0);
    return v___x_199_;
}
pub unsafe fn l_Lean_Order_instMonadTailST___lam__0(
    mut v_x_200_: *mut leanh::LeanObject,
    mut v_inst_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_202_ = leanh::lean_box(0);
    return v___x_202_;
}
pub unsafe fn l_Lean_Order_instMonadTailST(
    mut v_00_u03c3_204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_205_ = l_Lean_Order_instMonadTailST___closed__0;
    return v___f_205_;
}
pub unsafe fn l_Lean_Order_instMonadTailBaseIO___aux__1(
    mut v_x_206_: *mut leanh::LeanObject,
    mut v_inst_207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = leanh::lean_box(0);
    return v___x_208_;
}
pub unsafe fn l_Lean_Order_instMonadTailESTOfNonempty___lam__0(
    mut v_x_211_: *mut leanh::LeanObject,
    mut v_inst_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_213_ = leanh::lean_box(0);
    return v___x_213_;
}
pub unsafe fn l_Lean_Order_instMonadTailESTOfNonempty(
    mut v_00_u03b5_215_: *mut leanh::LeanObject,
    mut v_00_u03c3_216_: *mut leanh::LeanObject,
    mut v_inst_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_218_ = l_Lean_Order_instMonadTailESTOfNonempty___closed__0;
    return v___f_218_;
}
pub unsafe fn l_Lean_Order_instMonadTailEIOOfNonempty___lam__0(
    mut v_00_u03b2_219_: *mut leanh::LeanObject,
    mut v_inst_220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_221_ = leanh::lean_box(0);
    return v___x_221_;
}
pub unsafe fn l_Lean_Order_instMonadTailEIOOfNonempty(
    mut v_00_u03b5_223_: *mut leanh::LeanObject,
    mut v_inst_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_225_ = l_Lean_Order_instMonadTailEIOOfNonempty___closed__0;
    return v___f_225_;
}
pub unsafe fn l_Lean_Order_instMonadTailStateRefT_x27___aux__1(
    mut v_00_u03c9_228_: *mut leanh::LeanObject,
    mut v_00_u03c3_229_: *mut leanh::LeanObject,
    mut v_m_230_: *mut leanh::LeanObject,
    mut v_inst_231_: *mut leanh::LeanObject,
    mut v_inst_232_: *mut leanh::LeanObject,
    mut v_00_u03b1_233_: *mut leanh::LeanObject,
    mut v_inst_234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_235_ = leanh::lean_box(0);
    return v___x_235_;
}
pub unsafe fn l_Lean_Order_instMonadTailStateRefT_x27___aux__1___boxed(
    mut v_00_u03c9_236_: *mut leanh::LeanObject,
    mut v_00_u03c3_237_: *mut leanh::LeanObject,
    mut v_m_238_: *mut leanh::LeanObject,
    mut v_inst_239_: *mut leanh::LeanObject,
    mut v_inst_240_: *mut leanh::LeanObject,
    mut v_00_u03b1_241_: *mut leanh::LeanObject,
    mut v_inst_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_243_ = l_Lean_Order_instMonadTailStateRefT_x27___aux__1(
        v_00_u03c9_236_,
        v_00_u03c3_237_,
        v_m_238_,
        v_inst_239_,
        v_inst_240_,
        v_00_u03b1_241_,
        v_inst_242_,
    );
    leanh::lean_dec_ref(v_inst_240_);
    leanh::lean_dec_ref(v_inst_239_);
    return v_res_243_;
}
pub unsafe fn l_Lean_Order_instMonadTailStateRefT_x27___redArg(
    mut v_inst_244_: *mut leanh::LeanObject,
    mut v_inst_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_246_ = leanh::lean_alloc_closure(
        l_Lean_Order_instMonadTailStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___x_246_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_246_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_246_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_246_, 3, v_inst_244_);
    leanh::lean_closure_set(v___x_246_, 4, v_inst_245_);
    return v___x_246_;
}
pub unsafe fn l_Lean_Order_instMonadTailStateRefT_x27(
    mut v_00_u03c9_247_: *mut leanh::LeanObject,
    mut v_00_u03c3_248_: *mut leanh::LeanObject,
    mut v_m_249_: *mut leanh::LeanObject,
    mut v_inst_250_: *mut leanh::LeanObject,
    mut v_inst_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = leanh::lean_alloc_closure(
        l_Lean_Order_instMonadTailStateRefT_x27___aux__1___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___x_252_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_252_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_252_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_252_, 3, v_inst_250_);
    leanh::lean_closure_set(v___x_252_, 4, v_inst_251_);
    return v___x_252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Internal_Order_MonadTail(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_ST(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Internal_Order_MonadTail(
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
pub unsafe fn initialize_Init_Internal_Order_MonadTail(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Internal_Order_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_ST(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_MonadTail(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Internal_Order_MonadTail(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Internal_Order_MonadTail(builtin);
}
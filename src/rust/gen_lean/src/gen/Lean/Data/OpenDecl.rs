// Lean compiler output
// Module: Lean.Data.OpenDecl
// Imports: Init.Data.ToString.Name Init.Data.ToString.Extra
use crate::ffi::{lean_name_eq, lean_string_append};
use crate::r#gen::Init::Data::List::Basic::l_List_beq___redArg;
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, l_List_toString___redArg,
    runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_instToString___lam__0,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_replacePrefix;
use crate::r#gen::Init::Prelude::l_Lean_Name_beq___boxed;
pub static l_Lean_instBEqOpenDecl___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqOpenDecl_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqOpenDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqOpenDecl___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqOpenDecl: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqOpenDecl___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_OpenDecl_instInhabited___closed__0_value: leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_OpenDecl_instInhabited___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instInhabited___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_OpenDecl_instInhabited: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instInhabited___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___lam__0___closed__0_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [32, 104, 105, 100, 105, 110, 103, 32, 0],
};
static mut l_Lean_OpenDecl_instToString___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___lam__0___closed__1_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 134, 146, 32, 0],
};
static mut l_Lean_OpenDecl_instToString___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_OpenDecl_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_OpenDecl_instToString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___closed__2_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_OpenDecl_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_OpenDecl_instToString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_OpenDecl_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_rootNamespace___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [95, 114, 111, 111, 116, 95, 0],
    };
static mut l_Lean_rootNamespace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rootNamespace___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_rootNamespace___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_rootNamespace___closed__0_value)
                as *mut leanh::LeanObject,
            626731335300788152 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_rootNamespace___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rootNamespace___closed__1_value) as *mut leanh::LeanObject;
pub static mut l_Lean_rootNamespace: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rootNamespace___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_OpenDecl_ctorIdx(
    mut v_x_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_117_) == 0 {
        let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_118_ = leanh::lean_unsigned_to_nat(0);
        return v___x_118_;
    } else {
        let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_119_ = leanh::lean_unsigned_to_nat(1);
        return v___x_119_;
    }
}
pub unsafe fn l_Lean_OpenDecl_ctorIdx___boxed(
    mut v_x_120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_121_ = l_Lean_OpenDecl_ctorIdx(v_x_120_);
    leanh::lean_dec_ref(v_x_120_);
    return v_res_121_;
}
pub unsafe fn l_Lean_OpenDecl_ctorElim___redArg(
    mut v_t_122_: *mut leanh::LeanObject,
    mut v_k_123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ns_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_except_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ns_124_ = leanh::lean_ctor_get(v_t_122_, 0);
    leanh::lean_inc(v_ns_124_);
    v_except_125_ = leanh::lean_ctor_get(v_t_122_, 1);
    leanh::lean_inc(v_except_125_);
    leanh::lean_dec_ref(v_t_122_);
    v___x_126_ = leanh::lean_apply_2(v_k_123_, v_ns_124_, v_except_125_);
    return v___x_126_;
}
pub unsafe fn l_Lean_OpenDecl_ctorElim(
    mut v_motive_127_: *mut leanh::LeanObject,
    mut v_ctorIdx_128_: *mut leanh::LeanObject,
    mut v_t_129_: *mut leanh::LeanObject,
    mut v_h_130_: *mut leanh::LeanObject,
    mut v_k_131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_132_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_129_, v_k_131_);
    return v___x_132_;
}
pub unsafe fn l_Lean_OpenDecl_ctorElim___boxed(
    mut v_motive_133_: *mut leanh::LeanObject,
    mut v_ctorIdx_134_: *mut leanh::LeanObject,
    mut v_t_135_: *mut leanh::LeanObject,
    mut v_h_136_: *mut leanh::LeanObject,
    mut v_k_137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_138_ =
        l_Lean_OpenDecl_ctorElim(v_motive_133_, v_ctorIdx_134_, v_t_135_, v_h_136_, v_k_137_);
    leanh::lean_dec(v_ctorIdx_134_);
    return v_res_138_;
}
pub unsafe fn l_Lean_OpenDecl_simple_elim___redArg(
    mut v_t_139_: *mut leanh::LeanObject,
    mut v_simple_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_139_, v_simple_140_);
    return v___x_141_;
}
pub unsafe fn l_Lean_OpenDecl_simple_elim(
    mut v_motive_142_: *mut leanh::LeanObject,
    mut v_t_143_: *mut leanh::LeanObject,
    mut v_h_144_: *mut leanh::LeanObject,
    mut v_simple_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_146_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_143_, v_simple_145_);
    return v___x_146_;
}
pub unsafe fn l_Lean_OpenDecl_explicit_elim___redArg(
    mut v_t_147_: *mut leanh::LeanObject,
    mut v_explicit_148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_147_, v_explicit_148_);
    return v___x_149_;
}
pub unsafe fn l_Lean_OpenDecl_explicit_elim(
    mut v_motive_150_: *mut leanh::LeanObject,
    mut v_t_151_: *mut leanh::LeanObject,
    mut v_h_152_: *mut leanh::LeanObject,
    mut v_explicit_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_154_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_151_, v_explicit_153_);
    return v___x_154_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(
    mut v_x_155_: *mut leanh::LeanObject,
    mut v_x_156_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_157_: u8 = 0;
    let mut v___x_158_: u8 = 0;
    let mut v___x_159_: u8 = 0;
    let mut v_head_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_155_) == 0 {
                    if leanh::lean_obj_tag(v_x_156_) == 0 {
                        v___x_157_ = 1;
                        return v___x_157_;
                    } else {
                        v___x_158_ = 0;
                        return v___x_158_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_156_) == 0 {
                        v___x_159_ = 0;
                        return v___x_159_;
                    } else {
                        v_head_160_ = leanh::lean_ctor_get(v_x_155_, 0);
                        v_tail_161_ = leanh::lean_ctor_get(v_x_155_, 1);
                        v_head_162_ = leanh::lean_ctor_get(v_x_156_, 0);
                        v_tail_163_ = leanh::lean_ctor_get(v_x_156_, 1);
                        v___x_164_ = lean_name_eq(v_head_160_, v_head_162_);
                        if v___x_164_ == 0 {
                            return v___x_164_;
                        } else {
                            v_x_155_ = v_tail_161_;
                            v_x_156_ = v_tail_163_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0___boxed(
    mut v_x_166_: *mut leanh::LeanObject,
    mut v_x_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_168_: u8 = 0;
    let mut v_r_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(v_x_166_, v_x_167_);
    leanh::lean_dec(v_x_167_);
    leanh::lean_dec(v_x_166_);
    v_r_169_ = leanh::lean_box((v_res_168_) as usize);
    return v_r_169_;
}
pub unsafe fn l_Lean_instBEqOpenDecl_beq(
    mut v_x_170_: *mut leanh::LeanObject,
    mut v_x_171_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_170_) == 0 {
        if leanh::lean_obj_tag(v_x_171_) == 0 {
            let mut v_ns_172_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_except_173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ns_174_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_except_175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_176_: u8 = 0;
            v_ns_172_ = leanh::lean_ctor_get(v_x_170_, 0);
            v_except_173_ = leanh::lean_ctor_get(v_x_170_, 1);
            v_ns_174_ = leanh::lean_ctor_get(v_x_171_, 0);
            v_except_175_ = leanh::lean_ctor_get(v_x_171_, 1);
            v___x_176_ = lean_name_eq(v_ns_172_, v_ns_174_);
            if v___x_176_ == 0 {
                return v___x_176_;
            } else {
                let mut v___x_177_: u8 = 0;
                v___x_177_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(
                    v_except_173_,
                    v_except_175_,
                );
                return v___x_177_;
            }
        } else {
            let mut v___x_178_: u8 = 0;
            v___x_178_ = 0;
            return v___x_178_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_171_) == 1 {
            let mut v_id_179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_declName_180_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_181_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_declName_182_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_183_: u8 = 0;
            v_id_179_ = leanh::lean_ctor_get(v_x_170_, 0);
            v_declName_180_ = leanh::lean_ctor_get(v_x_170_, 1);
            v_id_181_ = leanh::lean_ctor_get(v_x_171_, 0);
            v_declName_182_ = leanh::lean_ctor_get(v_x_171_, 1);
            v___x_183_ = lean_name_eq(v_id_179_, v_id_181_);
            if v___x_183_ == 0 {
                return v___x_183_;
            } else {
                let mut v___x_184_: u8 = 0;
                v___x_184_ = lean_name_eq(v_declName_180_, v_declName_182_);
                return v___x_184_;
            }
        } else {
            let mut v___x_185_: u8 = 0;
            v___x_185_ = 0;
            return v___x_185_;
        }
    }
}
pub unsafe fn l_Lean_instBEqOpenDecl_beq___boxed(
    mut v_x_186_: *mut leanh::LeanObject,
    mut v_x_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_188_: u8 = 0;
    let mut v_r_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_188_ = l_Lean_instBEqOpenDecl_beq(v_x_186_, v_x_187_);
    leanh::lean_dec_ref(v_x_187_);
    leanh::lean_dec_ref(v_x_186_);
    v_r_189_ = leanh::lean_box((v_res_188_) as usize);
    return v_r_189_;
}
pub unsafe fn l_Lean_OpenDecl_instToString___lam__0(
    mut v___x_198_: *mut leanh::LeanObject,
    mut v___f_199_: *mut leanh::LeanObject,
    mut v_decl_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_decl_200_) == 0 {
        let mut v_ns_201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_except_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_203_: u8 = 0;
        let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_206_: u8 = 0;
        v_ns_201_ = leanh::lean_ctor_get(v_decl_200_, 0);
        leanh::lean_inc(v_ns_201_);
        v_except_202_ = leanh::lean_ctor_get(v_decl_200_, 1);
        leanh::lean_inc_n(v_except_202_, 2);
        leanh::lean_dec_ref_known(v_decl_200_, 2);
        v___x_203_ = 1;
        v___x_204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_ns_201_, v___x_203_,
        );
        v___x_205_ = leanh::lean_box(0);
        v___x_206_ = l_List_beq___redArg(v___x_198_, v_except_202_, v___x_205_);
        if v___x_206_ == 0 {
            let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_207_ = l_Lean_OpenDecl_instToString___lam__0___closed__0;
            v___x_208_ = l_List_toString___redArg(v___f_199_, v_except_202_);
            v___x_209_ = lean_string_append(v___x_207_, v___x_208_);
            leanh::lean_dec_ref(v___x_208_);
            v___x_210_ = lean_string_append(v___x_204_, v___x_209_);
            leanh::lean_dec_ref(v___x_209_);
            return v___x_210_;
        } else {
            leanh::lean_dec(v_except_202_);
            leanh::lean_dec_ref(v___f_199_);
            return v___x_204_;
        }
    } else {
        let mut v_id_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_213_: u8 = 0;
        let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_199_);
        leanh::lean_dec_ref(v___x_198_);
        v_id_211_ = leanh::lean_ctor_get(v_decl_200_, 0);
        leanh::lean_inc(v_id_211_);
        v_declName_212_ = leanh::lean_ctor_get(v_decl_200_, 1);
        leanh::lean_inc(v_declName_212_);
        leanh::lean_dec_ref_known(v_decl_200_, 2);
        v___x_213_ = 1;
        v___x_214_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_id_211_, v___x_213_,
        );
        v___x_215_ = l_Lean_OpenDecl_instToString___lam__0___closed__1;
        v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
        v___x_217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_declName_212_,
            v___x_213_,
        );
        v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
        leanh::lean_dec_ref(v___x_217_);
        return v___x_218_;
    }
}
pub unsafe fn l_Lean_removeRoot(
    mut v_n_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = l_Lean_rootNamespace;
    v___x_231_ = leanh::lean_box(0);
    v___x_232_ = l_Lean_Name_replacePrefix(v_n_229_, v___x_230_, v___x_231_);
    return v___x_232_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_OpenDecl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_OpenDecl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_OpenDecl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_OpenDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_OpenDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_OpenDecl(builtin);
}
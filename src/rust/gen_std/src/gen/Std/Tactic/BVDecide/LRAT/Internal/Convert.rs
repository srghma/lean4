// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Convert
// Imports: Std.Sat.CNF.RelabelFin Std.Tactic.BVDecide.LRAT.Internal.Formula Init.Data.Array.Bootstrap
use crate::ffi::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_uget_borrowed, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Std::Sat::CNF::Relabel::l_Std_Sat_CNF_relabel___redArg;
use crate::r#gen::Std::Sat::CNF::RelabelFin::{
    initialize_Std_Sat_CNF_RelabelFin, l_Std_Sat_CNF_numLiterals, l_Std_Sat_CNF_relabelFin,
    runtime_initialize_Std_Sat_CNF_RelabelFin,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Clause::l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Implementation::l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula,
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0_value:
    crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0(
    mut v_lit_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_128_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_129_ = lean_nat_add(v_lit_127_, v___x_128_);
    return v___x_129_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0___boxed(
    mut v_lit_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_131_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0(v_lit_130_);
    crate::leanh::lean_dec(v_lit_130_);
    return v_res_131_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(
    mut v_cnf_133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cnf_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_134_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0;
    v_cnf_135_ = l_Std_Sat_CNF_relabelFin(v_cnf_133_);
    v___x_136_ = l_Std_Sat_CNF_relabel___redArg(v___f_134_, v_cnf_135_);
    return v___x_136_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(
    mut v_n_137_: *mut crate::leanh::LeanObject,
    mut v_clause_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_139_ = lean_array_mk(v_clause_138_);
    v___x_140_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_137_, v___x_139_);
    crate::leanh::lean_dec_ref(v___x_139_);
    return v___x_140_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27___boxed(
    mut v_n_141_: *mut crate::leanh::LeanObject,
    mut v_clause_142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_143_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(v_n_141_, v_clause_142_);
    crate::leanh::lean_dec(v_n_141_);
    return v_res_143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(
    mut v_n_144_: *mut crate::leanh::LeanObject,
    mut v_as_145_: *mut crate::leanh::LeanObject,
    mut v_i_146_: usize,
    mut v_stop_147_: usize,
    mut v_b_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: usize = 0;
    let mut v___x_152_: usize = 0;
    let mut v___x_154_: u8 = 0;
    let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_154_ = lean_usize_dec_eq(v_i_146_, v_stop_147_);
                if v___x_154_ == 0 {
                    v___x_155_ = lean_array_uget_borrowed(v_as_145_, v_i_146_);
                    crate::leanh::lean_inc(v___x_155_);
                    v___x_156_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(
                        v_n_144_, v___x_155_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_156_) == 0 {
                        v___y_150_ = v_b_148_;
                        state = 1;
                        continue;
                    } else {
                        v___x_157_ = lean_array_push(v_b_148_, v___x_156_);
                        v___y_150_ = v___x_157_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_148_;
                }
            }
            1 => {
                v___x_151_ = 1usize;
                v___x_152_ = lean_usize_add(v_i_146_, v___x_151_);
                v_i_146_ = v___x_152_;
                v_b_148_ = v___y_150_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0___boxed(
    mut v_n_158_: *mut crate::leanh::LeanObject,
    mut v_as_159_: *mut crate::leanh::LeanObject,
    mut v_i_160_: *mut crate::leanh::LeanObject,
    mut v_stop_161_: *mut crate::leanh::LeanObject,
    mut v_b_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_163_: usize = 0;
    let mut v_stop_boxed_164_: usize = 0;
    let mut v_res_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_163_ = crate::leanh::lean_unbox_usize(v_i_160_);
    crate::leanh::lean_dec(v_i_160_);
    v_stop_boxed_164_ = crate::leanh::lean_unbox_usize(v_stop_161_);
    crate::leanh::lean_dec(v_stop_161_);
    v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(v_n_158_, v_as_159_, v_i_boxed_163_, v_stop_boxed_164_, v_b_162_);
    crate::leanh::lean_dec_ref(v_as_159_);
    crate::leanh::lean_dec(v_n_158_);
    return v_res_165_;
}
pub unsafe fn l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0(
    mut v_n_168_: *mut crate::leanh::LeanObject,
    mut v_as_169_: *mut crate::leanh::LeanObject,
    mut v_start_170_: *mut crate::leanh::LeanObject,
    mut v_stop_171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: u8 = 0;
    v___x_172_ = l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0;
    v___x_173_ = lean_nat_dec_lt(v_start_170_, v_stop_171_);
    if v___x_173_ == 0 {
        return v___x_172_;
    } else {
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_175_: u8 = 0;
        v___x_174_ = lean_array_get_size(v_as_169_);
        v___x_175_ = lean_nat_dec_le(v_stop_171_, v___x_174_);
        if v___x_175_ == 0 {
            let mut v___x_176_: u8 = 0;
            v___x_176_ = lean_nat_dec_lt(v_start_170_, v___x_174_);
            if v___x_176_ == 0 {
                return v___x_172_;
            } else {
                let mut v___x_177_: usize = 0;
                let mut v___x_178_: usize = 0;
                let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_177_ = lean_usize_of_nat(v_start_170_);
                v___x_178_ = lean_usize_of_nat(v___x_174_);
                v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(v_n_168_, v_as_169_, v___x_177_, v___x_178_, v___x_172_);
                return v___x_179_;
            }
        } else {
            let mut v___x_180_: usize = 0;
            let mut v___x_181_: usize = 0;
            let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_180_ = lean_usize_of_nat(v_start_170_);
            v___x_181_ = lean_usize_of_nat(v_stop_171_);
            v___x_182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(v_n_168_, v_as_169_, v___x_180_, v___x_181_, v___x_172_);
            return v___x_182_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___boxed(
    mut v_n_183_: *mut crate::leanh::LeanObject,
    mut v_as_184_: *mut crate::leanh::LeanObject,
    mut v_start_185_: *mut crate::leanh::LeanObject,
    mut v_stop_186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_187_ =
        l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0(
            v_n_183_,
            v_as_184_,
            v_start_185_,
            v_stop_186_,
        );
    crate::leanh::lean_dec(v_stop_186_);
    crate::leanh::lean_dec(v_start_185_);
    crate::leanh::lean_dec_ref(v_as_184_);
    crate::leanh::lean_dec(v_n_183_);
    return v_res_187_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(
    mut v_n_188_: *mut crate::leanh::LeanObject,
    mut v_clauses_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_191_ = lean_array_get_size(v_clauses_189_);
    v___x_192_ =
        l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0(
            v_n_188_,
            v_clauses_189_,
            v___x_190_,
            v___x_191_,
        );
    return v___x_192_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___boxed(
    mut v_n_193_: *mut crate::leanh::LeanObject,
    mut v_clauses_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_195_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(v_n_193_, v_clauses_194_);
    crate::leanh::lean_dec_ref(v_clauses_194_);
    crate::leanh::lean_dec(v_n_193_);
    return v_res_195_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(
    mut v_acc_196_: *mut crate::leanh::LeanObject,
    mut v_h__1_197_: *mut crate::leanh::LeanObject,
    mut v_h__2_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_acc_196_) == 0 {
        let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_198_);
        v___x_199_ = crate::leanh::lean_box(0);
        v___x_200_ = crate::leanh::lean_apply_1(v_h__1_197_, v___x_199_);
        return v___x_200_;
    } else {
        let mut v_val_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_197_);
        v_val_201_ = crate::leanh::lean_ctor_get(v_acc_196_, 0);
        crate::leanh::lean_inc(v_val_201_);
        crate::leanh::lean_dec_ref_known(v_acc_196_, 1);
        v___x_202_ = crate::leanh::lean_apply_1(v_h__2_198_, v_val_201_);
        return v___x_202_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(
    mut v_n_203_: *mut crate::leanh::LeanObject,
    mut v_motive_204_: *mut crate::leanh::LeanObject,
    mut v_acc_205_: *mut crate::leanh::LeanObject,
    mut v_h__1_206_: *mut crate::leanh::LeanObject,
    mut v_h__2_207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_acc_205_) == 0 {
        let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_207_);
        v___x_208_ = crate::leanh::lean_box(0);
        v___x_209_ = crate::leanh::lean_apply_1(v_h__1_206_, v___x_208_);
        return v___x_209_;
    } else {
        let mut v_val_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_206_);
        v_val_210_ = crate::leanh::lean_ctor_get(v_acc_205_, 0);
        crate::leanh::lean_inc(v_val_210_);
        crate::leanh::lean_dec_ref_known(v_acc_205_, 1);
        v___x_211_ = crate::leanh::lean_apply_1(v_h__2_207_, v_val_210_);
        return v___x_211_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(
    mut v_n_212_: *mut crate::leanh::LeanObject,
    mut v_motive_213_: *mut crate::leanh::LeanObject,
    mut v_acc_214_: *mut crate::leanh::LeanObject,
    mut v_h__1_215_: *mut crate::leanh::LeanObject,
    mut v_h__2_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_217_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(v_n_212_, v_motive_213_, v_acc_214_, v_h__1_215_, v_h__2_216_);
    crate::leanh::lean_dec(v_n_212_);
    return v_res_217_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(
    mut v_cnf_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lifted_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lratCnf_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_cnf_222_);
    v_lifted_223_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(v_cnf_222_);
    v___x_224_ = l_Std_Sat_CNF_numLiterals(v_cnf_222_);
    crate::leanh::lean_dec_ref(v_cnf_222_);
    v___x_225_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_226_ = lean_nat_add(v___x_224_, v___x_225_);
    crate::leanh::lean_dec(v___x_224_);
    v_lratCnf_227_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(v___x_226_, v_lifted_223_);
    crate::leanh::lean_dec_ref(v_lifted_223_);
    v___x_228_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0;
    v___x_229_ = l_Array_append___redArg(v___x_228_, v_lratCnf_227_);
    crate::leanh::lean_dec_ref(v_lratCnf_227_);
    v___x_230_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(v___x_226_, v___x_229_);
    return v___x_230_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___redArg(
    mut v_x_231_: *mut crate::leanh::LeanObject,
    mut v_h__1_232_: *mut crate::leanh::LeanObject,
    mut v_h__2_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_231_) == 0 {
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_232_);
        v___x_234_ = crate::leanh::lean_box(0);
        v___x_235_ = crate::leanh::lean_apply_1(v_h__2_233_, v___x_234_);
        return v___x_235_;
    } else {
        let mut v_val_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_233_);
        v_val_236_ = crate::leanh::lean_ctor_get(v_x_231_, 0);
        crate::leanh::lean_inc(v_val_236_);
        crate::leanh::lean_dec_ref_known(v_x_231_, 1);
        v___x_237_ = crate::leanh::lean_apply_1(v_h__1_232_, v_val_236_);
        return v___x_237_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(
    mut v_n_238_: *mut crate::leanh::LeanObject,
    mut v_motive_239_: *mut crate::leanh::LeanObject,
    mut v_x_240_: *mut crate::leanh::LeanObject,
    mut v_h__1_241_: *mut crate::leanh::LeanObject,
    mut v_h__2_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_240_) == 0 {
        let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_241_);
        v___x_243_ = crate::leanh::lean_box(0);
        v___x_244_ = crate::leanh::lean_apply_1(v_h__2_242_, v___x_243_);
        return v___x_244_;
    } else {
        let mut v_val_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_242_);
        v_val_245_ = crate::leanh::lean_ctor_get(v_x_240_, 0);
        crate::leanh::lean_inc(v_val_245_);
        crate::leanh::lean_dec_ref_known(v_x_240_, 1);
        v___x_246_ = crate::leanh::lean_apply_1(v_h__1_241_, v_val_245_);
        return v___x_246_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___boxed(
    mut v_n_247_: *mut crate::leanh::LeanObject,
    mut v_motive_248_: *mut crate::leanh::LeanObject,
    mut v_x_249_: *mut crate::leanh::LeanObject,
    mut v_h__1_250_: *mut crate::leanh::LeanObject,
    mut v_h__2_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_252_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(v_n_247_, v_motive_248_, v_x_249_, v_h__1_250_, v_h__2_251_);
    crate::leanh::lean_dec(v_n_247_);
    return v_res_252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_CNF_RelabelFin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
}

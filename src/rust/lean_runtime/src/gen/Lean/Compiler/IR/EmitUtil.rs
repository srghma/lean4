// Lean compiler output
// Module: Lean.Compiler.IR.EmitUtil
// Imports: Lean.Compiler.InitAttr Lean.Compiler.IR.CompilerM
use crate::r#gen::Lean::Compiler::IR::Basic::{
    l_Lean_IR_Alt_body, l_Lean_IR_Decl_name, l_Lean_IR_FnBody_body, l_Lean_IR_FnBody_isTerminal,
    l_Lean_IR_instBEqJoinPointId_beq, l_Lean_IR_instBEqJoinPointId_beq___boxed,
    l_Lean_IR_instBEqVarId_beq, l_Lean_IR_instBEqVarId_beq___boxed,
    l_Lean_IR_instHashableJoinPointId_hash, l_Lean_IR_instHashableJoinPointId_hash___boxed,
    l_Lean_IR_instHashableVarId_hash, l_Lean_IR_instHashableVarId_hash___boxed,
};
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, lean_get_init_fn_name_for,
    runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_isPrefixOf,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Lean_NameSet_empty;
use crate::r#gen::Lean::Environment::l_Lean_Environment_header;
use crate::r#gen::Lean::Setup::l_Lean_instBEqIRPhases_beq;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insert___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_contains___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_collectUsedDecls___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_IR_collectUsedDecls___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_collectUsedDecls___closed__0_value) as *mut LeanObject;
static mut l_Lean_IR_collectUsedDecls___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_collectUsedDecls___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_CollectMaps_collectVar___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqVarId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectVar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectVar___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_CollectMaps_collectVar___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instHashableVarId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectVar___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectVar___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_CollectMaps_collectJP___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqJoinPointId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectJP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectJP___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_CollectMaps_collectJP___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instHashableJoinPointId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectJP___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectJP___closed__1_value) as *mut LeanObject;
static mut l_Lean_IR_mkVarJPMaps___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_mkVarJPMaps___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_mkVarJPMaps___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_mkVarJPMaps___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_mkVarJPMaps___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_mkVarJPMaps___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_IR_isTailCallTo(
    mut v_g_1103_: *mut LeanObject,
    mut v_b_1104_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_b_1104_) == 0 {
        let mut v_e_1105_: *mut LeanObject = core::ptr::null_mut();
        v_e_1105_ = lean_ctor_get(v_b_1104_, 2);
        if lean_obj_tag(v_e_1105_) == 6 {
            let mut v_b_1106_: *mut LeanObject = core::ptr::null_mut();
            v_b_1106_ = lean_ctor_get(v_b_1104_, 3);
            if lean_obj_tag(v_b_1106_) == 10 {
                let mut v_x_1107_: *mut LeanObject = core::ptr::null_mut();
                v_x_1107_ = lean_ctor_get(v_b_1106_, 0);
                if lean_obj_tag(v_x_1107_) == 0 {
                    let mut v_x_1108_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_c_1109_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_id_1110_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1111_: u8 = 0;
                    v_x_1108_ = lean_ctor_get(v_b_1104_, 0);
                    v_c_1109_ = lean_ctor_get(v_e_1105_, 0);
                    v_id_1110_ = lean_ctor_get(v_x_1107_, 0);
                    v___x_1111_ = l_Lean_IR_instBEqVarId_beq(v_x_1108_, v_id_1110_);
                    if v___x_1111_ == 0 {
                        return v___x_1111_;
                    } else {
                        let mut v___x_1112_: u8 = 0;
                        v___x_1112_ = lean_name_eq(v_c_1109_, v_g_1103_);
                        return v___x_1112_;
                    }
                } else {
                    let mut v___x_1113_: u8 = 0;
                    v___x_1113_ = 0;
                    return v___x_1113_;
                }
            } else {
                let mut v___x_1114_: u8 = 0;
                v___x_1114_ = 0;
                return v___x_1114_;
            }
        } else {
            let mut v___x_1115_: u8 = 0;
            v___x_1115_ = 0;
            return v___x_1115_;
        }
    } else {
        let mut v___x_1116_: u8 = 0;
        v___x_1116_ = 0;
        return v___x_1116_;
    }
}
pub unsafe fn l_Lean_IR_isTailCallTo___boxed(
    mut v_g_1117_: *mut LeanObject,
    mut v_b_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1119_: u8 = 0;
    let mut v_r_1120_: *mut LeanObject = core::ptr::null_mut();
    v_res_1119_ = l_Lean_IR_isTailCallTo(v_g_1117_, v_b_1118_);
    lean_dec(v_b_1118_);
    lean_dec(v_g_1117_);
    v_r_1120_ = lean_box((v_res_1119_) as usize);
    return v_r_1120_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(
    mut v_modulePrefix_1121_: *mut LeanObject,
    mut v_as_1122_: *mut LeanObject,
    mut v_i_1123_: usize,
    mut v_stop_1124_: usize,
) -> u8 {
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_irPhases_1128_: u8 = 0;
    let mut v___x_1129_: u8 = 0;
    let mut v___y_1131_: u8 = 0;
    let mut v___x_1132_: usize = 0;
    let mut v___x_1133_: usize = 0;
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: u8 = 0;
    let mut v_module_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1125_ = lean_usize_dec_eq(v_i_1123_, v_stop_1124_);
                if v___x_1125_ == 0 {
                    v___x_1126_ = lean_array_uget_borrowed(v_as_1122_, v_i_1123_);
                    v_toImport_1127_ = lean_ctor_get(v___x_1126_, 0);
                    v_irPhases_1128_ = lean_ctor_get_uint8(
                        v___x_1126_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_1129_ = 1;
                    v___x_1135_ = 1;
                    v___x_1136_ = l_Lean_instBEqIRPhases_beq(v_irPhases_1128_, v___x_1135_);
                    if v___x_1136_ == 0 {
                        v_module_1137_ = lean_ctor_get(v_toImport_1127_, 0);
                        v___x_1138_ = l_Lean_Name_isPrefixOf(v_modulePrefix_1121_, v_module_1137_);
                        v___y_1131_ = v___x_1138_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1131_ = v___x_1125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1139_ = 0;
                    return v___x_1139_;
                }
            }
            1 => {
                if v___y_1131_ == 0 {
                    v___x_1132_ = 1usize;
                    v___x_1133_ = lean_usize_add(v_i_1123_, v___x_1132_);
                    v_i_1123_ = v___x_1133_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1129_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0___boxed(
    mut v_modulePrefix_1140_: *mut LeanObject,
    mut v_as_1141_: *mut LeanObject,
    mut v_i_1142_: *mut LeanObject,
    mut v_stop_1143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1144_: usize = 0;
    let mut v_stop_boxed_1145_: usize = 0;
    let mut v_res_1146_: u8 = 0;
    let mut v_r_1147_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1144_ = lean_unbox_usize(v_i_1142_);
    lean_dec(v_i_1142_);
    v_stop_boxed_1145_ = lean_unbox_usize(v_stop_1143_);
    lean_dec(v_stop_1143_);
    v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_1140_, v_as_1141_, v_i_boxed_1144_, v_stop_boxed_1145_);
    lean_dec_ref(v_as_1141_);
    lean_dec(v_modulePrefix_1140_);
    v_r_1147_ = lean_box((v_res_1146_) as usize);
    return v_r_1147_;
}
pub unsafe fn l_Lean_IR_usesModuleFrom(
    mut v_env_1148_: *mut LeanObject,
    mut v_modulePrefix_1149_: *mut LeanObject,
) -> u8 {
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: u8 = 0;
    v___x_1150_ = l_Lean_Environment_header(v_env_1148_);
    v_modules_1151_ = lean_ctor_get(v___x_1150_, 3);
    lean_inc_ref(v_modules_1151_);
    lean_dec_ref(v___x_1150_);
    v___x_1152_ = lean_unsigned_to_nat(0);
    v___x_1153_ = lean_array_get_size(v_modules_1151_);
    v___x_1154_ = lean_nat_dec_lt(v___x_1152_, v___x_1153_);
    if v___x_1154_ == 0 {
        lean_dec_ref(v_modules_1151_);
        return v___x_1154_;
    } else {
        if v___x_1154_ == 0 {
            lean_dec_ref(v_modules_1151_);
            return v___x_1154_;
        } else {
            let mut v___x_1155_: usize = 0;
            let mut v___x_1156_: usize = 0;
            let mut v___x_1157_: u8 = 0;
            v___x_1155_ = 0usize;
            v___x_1156_ = lean_usize_of_nat(v___x_1153_);
            v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_1149_, v_modules_1151_, v___x_1155_, v___x_1156_);
            lean_dec_ref(v_modules_1151_);
            return v___x_1157_;
        }
    }
}
pub unsafe fn l_Lean_IR_usesModuleFrom___boxed(
    mut v_env_1158_: *mut LeanObject,
    mut v_modulePrefix_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1160_: u8 = 0;
    let mut v_r_1161_: *mut LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_Lean_IR_usesModuleFrom(v_env_1158_, v_modulePrefix_1159_);
    lean_dec(v_modulePrefix_1159_);
    lean_dec_ref(v_env_1158_);
    v_r_1161_ = lean_box((v_res_1160_) as usize);
    return v_r_1161_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collect___redArg(
    mut v_f_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_set_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1169_: u8 = 0;
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_set_1165_ = lean_ctor_get(v_a_1164_, 0);
                v_order_1166_ = lean_ctor_get(v_a_1164_, 1);
                v_isSharedCheck_1189_ = (!lean_is_exclusive(v_a_1164_)) as u8;
                if v_isSharedCheck_1189_ == 0 {
                    v___x_1168_ = v_a_1164_;
                    v_isShared_1169_ = v_isSharedCheck_1189_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_order_1166_);
                    lean_inc(v_set_1165_);
                    lean_dec(v_a_1164_);
                    v___x_1168_ = lean_box(0);
                    v_isShared_1169_ = v_isSharedCheck_1189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1170_ = lean_box(0);
                v___x_1184_ = l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0;
                lean_inc(v_set_1165_);
                lean_inc(v_f_1163_);
                v___x_1185_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(
                    v___x_1184_,
                    v_f_1163_,
                    v_set_1165_,
                );
                if v___x_1185_ == 0 {
                    lean_inc(v_f_1163_);
                    v___x_1186_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v___x_1184_,
                        v_f_1163_,
                        v___x_1170_,
                        v_set_1165_,
                    );
                    v___x_1187_ = lean_box((v___x_1185_) as usize);
                    v_fst_1172_ = v___x_1187_;
                    v_snd_1173_ = v___x_1186_;
                    state = 2;
                    continue;
                } else {
                    v___x_1188_ = lean_box((v___x_1185_) as usize);
                    v_fst_1172_ = v___x_1188_;
                    v_snd_1173_ = v_set_1165_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1174_ = (lean_unbox(v_fst_1172_) as u8);
                lean_dec(v_fst_1172_);
                if v___x_1174_ == 0 {
                    v___x_1175_ = lean_array_push(v_order_1166_, v_f_1163_);
                    if v_isShared_1169_ == 0 {
                        lean_ctor_set(v___x_1168_, 1, v___x_1175_);
                        lean_ctor_set(v___x_1168_, 0, v_snd_1173_);
                        v___x_1177_ = v___x_1168_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_snd_1173_);
                        lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1175_);
                        v___x_1177_ = v_reuseFailAlloc_1179_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_f_1163_);
                    if v_isShared_1169_ == 0 {
                        lean_ctor_set(v___x_1168_, 0, v_snd_1173_);
                        v___x_1181_ = v___x_1168_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_snd_1173_);
                        lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_order_1166_);
                        v___x_1181_ = v_reuseFailAlloc_1183_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1178_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1178_, 0, v___x_1170_);
                lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                return v___x_1178_;
            }
            4 => {
                v___x_1182_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1182_, 0, v___x_1170_);
                lean_ctor_set(v___x_1182_, 1, v___x_1181_);
                return v___x_1182_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collect(
    mut v_f_1190_: *mut LeanObject,
    mut v_a_1191_: *mut LeanObject,
    mut v_a_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_set_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1197_: u8 = 0;
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: u8 = 0;
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_set_1193_ = lean_ctor_get(v_a_1192_, 0);
                v_order_1194_ = lean_ctor_get(v_a_1192_, 1);
                v_isSharedCheck_1217_ = (!lean_is_exclusive(v_a_1192_)) as u8;
                if v_isSharedCheck_1217_ == 0 {
                    v___x_1196_ = v_a_1192_;
                    v_isShared_1197_ = v_isSharedCheck_1217_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_order_1194_);
                    lean_inc(v_set_1193_);
                    lean_dec(v_a_1192_);
                    v___x_1196_ = lean_box(0);
                    v_isShared_1197_ = v_isSharedCheck_1217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1198_ = lean_box(0);
                v___x_1212_ = l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0;
                lean_inc(v_set_1193_);
                lean_inc(v_f_1190_);
                v___x_1213_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(
                    v___x_1212_,
                    v_f_1190_,
                    v_set_1193_,
                );
                if v___x_1213_ == 0 {
                    lean_inc(v_f_1190_);
                    v___x_1214_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v___x_1212_,
                        v_f_1190_,
                        v___x_1198_,
                        v_set_1193_,
                    );
                    v___x_1215_ = lean_box((v___x_1213_) as usize);
                    v_fst_1200_ = v___x_1215_;
                    v_snd_1201_ = v___x_1214_;
                    state = 2;
                    continue;
                } else {
                    v___x_1216_ = lean_box((v___x_1213_) as usize);
                    v_fst_1200_ = v___x_1216_;
                    v_snd_1201_ = v_set_1193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1202_ = (lean_unbox(v_fst_1200_) as u8);
                lean_dec(v_fst_1200_);
                if v___x_1202_ == 0 {
                    v___x_1203_ = lean_array_push(v_order_1194_, v_f_1190_);
                    if v_isShared_1197_ == 0 {
                        lean_ctor_set(v___x_1196_, 1, v___x_1203_);
                        lean_ctor_set(v___x_1196_, 0, v_snd_1201_);
                        v___x_1205_ = v___x_1196_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_snd_1201_);
                        lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1203_);
                        v___x_1205_ = v_reuseFailAlloc_1207_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_f_1190_);
                    if v_isShared_1197_ == 0 {
                        lean_ctor_set(v___x_1196_, 0, v_snd_1201_);
                        v___x_1209_ = v___x_1196_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_snd_1201_);
                        lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_order_1194_);
                        v___x_1209_ = v_reuseFailAlloc_1211_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1206_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1206_, 0, v___x_1198_);
                lean_ctor_set(v___x_1206_, 1, v___x_1205_);
                return v___x_1206_;
            }
            4 => {
                v___x_1210_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1210_, 0, v___x_1198_);
                lean_ctor_set(v___x_1210_, 1, v___x_1209_);
                return v___x_1210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collect___boxed(
    mut v_f_1218_: *mut LeanObject,
    mut v_a_1219_: *mut LeanObject,
    mut v_a_1220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1221_: *mut LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Lean_IR_CollectUsedDecls_collect(v_f_1218_, v_a_1219_, v_a_1220_);
    lean_dec_ref(v_a_1219_);
    return v_res_1221_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(
    mut v_k_1222_: *mut LeanObject,
    mut v_v_1223_: *mut LeanObject,
    mut v_t_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: u8 = 0;
    let mut v_impl_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1252_: u8 = 0;
    let mut v_size_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1264_: u8 = 0;
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut v_unused_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1304_: u8 = 0;
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut v_unused_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut v_unused_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v_unused_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v_k_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1359_: u8 = 0;
    let mut v_unused_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_unused_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: u8 = 0;
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1392_: u8 = 0;
    let mut v_size_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut v_unused_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1442_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_unused_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_unused_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v_k_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1481_: u8 = 0;
    let mut v_unused_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_unused_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_unused_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1224_) == 0 {
                    v_size_1225_ = lean_ctor_get(v_t_1224_, 0);
                    v_k_1226_ = lean_ctor_get(v_t_1224_, 1);
                    v_v_1227_ = lean_ctor_get(v_t_1224_, 2);
                    v_l_1228_ = lean_ctor_get(v_t_1224_, 3);
                    v_r_1229_ = lean_ctor_get(v_t_1224_, 4);
                    v_isSharedCheck_1509_ = (!lean_is_exclusive(v_t_1224_)) as u8;
                    if v_isSharedCheck_1509_ == 0 {
                        v___x_1231_ = v_t_1224_;
                        v_isShared_1232_ = v_isSharedCheck_1509_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1229_);
                        lean_inc(v_l_1228_);
                        lean_inc(v_v_1227_);
                        lean_inc(v_k_1226_);
                        lean_inc(v_size_1225_);
                        lean_dec(v_t_1224_);
                        v___x_1231_ = lean_box(0);
                        v_isShared_1232_ = v_isSharedCheck_1509_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1510_ = lean_unsigned_to_nat(1);
                    v___x_1511_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1511_, 0, v___x_1510_);
                    lean_ctor_set(v___x_1511_, 1, v_k_1222_);
                    lean_ctor_set(v___x_1511_, 2, v_v_1223_);
                    lean_ctor_set(v___x_1511_, 3, v_t_1224_);
                    lean_ctor_set(v___x_1511_, 4, v_t_1224_);
                    return v___x_1511_;
                }
            }
            1 => {
                v___x_1233_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1222_, v_k_1226_);
                match v___x_1233_ {
                    0 => {
                        lean_dec(v_size_1225_);
                        v_impl_1234_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_1222_, v_v_1223_, v_l_1228_);
                        v___x_1235_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_1229_) == 0 {
                            v_size_1236_ = lean_ctor_get(v_r_1229_, 0);
                            v_size_1237_ = lean_ctor_get(v_impl_1234_, 0);
                            lean_inc(v_size_1237_);
                            v_k_1238_ = lean_ctor_get(v_impl_1234_, 1);
                            lean_inc(v_k_1238_);
                            v_v_1239_ = lean_ctor_get(v_impl_1234_, 2);
                            lean_inc(v_v_1239_);
                            v_l_1240_ = lean_ctor_get(v_impl_1234_, 3);
                            lean_inc(v_l_1240_);
                            v_r_1241_ = lean_ctor_get(v_impl_1234_, 4);
                            lean_inc(v_r_1241_);
                            v___x_1242_ = lean_unsigned_to_nat(3);
                            v___x_1243_ = lean_nat_mul(v___x_1242_, v_size_1236_);
                            v___x_1244_ = lean_nat_dec_lt(v___x_1243_, v_size_1237_);
                            lean_dec(v___x_1243_);
                            if v___x_1244_ == 0 {
                                lean_dec(v_r_1241_);
                                lean_dec(v_l_1240_);
                                lean_dec(v_v_1239_);
                                lean_dec(v_k_1238_);
                                v___x_1245_ = lean_nat_add(v___x_1235_, v_size_1237_);
                                lean_dec(v_size_1237_);
                                v___x_1246_ = lean_nat_add(v___x_1245_, v_size_1236_);
                                lean_dec(v___x_1245_);
                                if v_isShared_1232_ == 0 {
                                    lean_ctor_set(v___x_1231_, 3, v_impl_1234_);
                                    lean_ctor_set(v___x_1231_, 0, v___x_1246_);
                                    v___x_1248_ = v___x_1231_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
                                    lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_k_1226_);
                                    lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_v_1227_);
                                    lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_impl_1234_);
                                    lean_ctor_set(v_reuseFailAlloc_1249_, 4, v_r_1229_);
                                    v___x_1248_ = v_reuseFailAlloc_1249_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1315_ = (!lean_is_exclusive(v_impl_1234_)) as u8;
                                if v_isSharedCheck_1315_ == 0 {
                                    v_unused_1316_ = lean_ctor_get(v_impl_1234_, 4);
                                    lean_dec(v_unused_1316_);
                                    v_unused_1317_ = lean_ctor_get(v_impl_1234_, 3);
                                    lean_dec(v_unused_1317_);
                                    v_unused_1318_ = lean_ctor_get(v_impl_1234_, 2);
                                    lean_dec(v_unused_1318_);
                                    v_unused_1319_ = lean_ctor_get(v_impl_1234_, 1);
                                    lean_dec(v_unused_1319_);
                                    v_unused_1320_ = lean_ctor_get(v_impl_1234_, 0);
                                    lean_dec(v_unused_1320_);
                                    v___x_1251_ = v_impl_1234_;
                                    v_isShared_1252_ = v_isSharedCheck_1315_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1234_);
                                    v___x_1251_ = lean_box(0);
                                    v_isShared_1252_ = v_isSharedCheck_1315_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1321_ = lean_ctor_get(v_impl_1234_, 3);
                            lean_inc(v_l_1321_);
                            if lean_obj_tag(v_l_1321_) == 0 {
                                v_r_1322_ = lean_ctor_get(v_impl_1234_, 4);
                                v_k_1323_ = lean_ctor_get(v_impl_1234_, 1);
                                v_v_1324_ = lean_ctor_get(v_impl_1234_, 2);
                                v_isSharedCheck_1335_ = (!lean_is_exclusive(v_impl_1234_)) as u8;
                                if v_isSharedCheck_1335_ == 0 {
                                    v_unused_1336_ = lean_ctor_get(v_impl_1234_, 3);
                                    lean_dec(v_unused_1336_);
                                    v_unused_1337_ = lean_ctor_get(v_impl_1234_, 0);
                                    lean_dec(v_unused_1337_);
                                    v___x_1326_ = v_impl_1234_;
                                    v_isShared_1327_ = v_isSharedCheck_1335_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_1322_);
                                    lean_inc(v_v_1324_);
                                    lean_inc(v_k_1323_);
                                    lean_dec(v_impl_1234_);
                                    v___x_1326_ = lean_box(0);
                                    v_isShared_1327_ = v_isSharedCheck_1335_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1338_ = lean_ctor_get(v_impl_1234_, 4);
                                lean_inc(v_r_1338_);
                                if lean_obj_tag(v_r_1338_) == 0 {
                                    v_k_1339_ = lean_ctor_get(v_impl_1234_, 1);
                                    v_v_1340_ = lean_ctor_get(v_impl_1234_, 2);
                                    v_isSharedCheck_1363_ =
                                        (!lean_is_exclusive(v_impl_1234_)) as u8;
                                    if v_isSharedCheck_1363_ == 0 {
                                        v_unused_1364_ = lean_ctor_get(v_impl_1234_, 4);
                                        lean_dec(v_unused_1364_);
                                        v_unused_1365_ = lean_ctor_get(v_impl_1234_, 3);
                                        lean_dec(v_unused_1365_);
                                        v_unused_1366_ = lean_ctor_get(v_impl_1234_, 0);
                                        lean_dec(v_unused_1366_);
                                        v___x_1342_ = v_impl_1234_;
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1340_);
                                        lean_inc(v_k_1339_);
                                        lean_dec(v_impl_1234_);
                                        v___x_1342_ = lean_box(0);
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1367_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1232_ == 0 {
                                        lean_ctor_set(v___x_1231_, 4, v_r_1338_);
                                        lean_ctor_set(v___x_1231_, 3, v_impl_1234_);
                                        lean_ctor_set(v___x_1231_, 0, v___x_1367_);
                                        v___x_1369_ = v___x_1231_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
                                        lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_k_1226_);
                                        lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_v_1227_);
                                        lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_impl_1234_);
                                        lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_r_1338_);
                                        v___x_1369_ = v_reuseFailAlloc_1370_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_1227_);
                        lean_dec(v_k_1226_);
                        if v_isShared_1232_ == 0 {
                            lean_ctor_set(v___x_1231_, 2, v_v_1223_);
                            lean_ctor_set(v___x_1231_, 1, v_k_1222_);
                            v___x_1372_ = v___x_1231_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_size_1225_);
                            lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1222_);
                            lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1223_);
                            lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_l_1228_);
                            lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1229_);
                            v___x_1372_ = v_reuseFailAlloc_1373_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_1225_);
                        v_impl_1374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_1222_, v_v_1223_, v_r_1229_);
                        v___x_1375_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_1228_) == 0 {
                            v_size_1376_ = lean_ctor_get(v_l_1228_, 0);
                            v_size_1377_ = lean_ctor_get(v_impl_1374_, 0);
                            lean_inc(v_size_1377_);
                            v_k_1378_ = lean_ctor_get(v_impl_1374_, 1);
                            lean_inc(v_k_1378_);
                            v_v_1379_ = lean_ctor_get(v_impl_1374_, 2);
                            lean_inc(v_v_1379_);
                            v_l_1380_ = lean_ctor_get(v_impl_1374_, 3);
                            lean_inc(v_l_1380_);
                            v_r_1381_ = lean_ctor_get(v_impl_1374_, 4);
                            lean_inc(v_r_1381_);
                            v___x_1382_ = lean_unsigned_to_nat(3);
                            v___x_1383_ = lean_nat_mul(v___x_1382_, v_size_1376_);
                            v___x_1384_ = lean_nat_dec_lt(v___x_1383_, v_size_1377_);
                            lean_dec(v___x_1383_);
                            if v___x_1384_ == 0 {
                                lean_dec(v_r_1381_);
                                lean_dec(v_l_1380_);
                                lean_dec(v_v_1379_);
                                lean_dec(v_k_1378_);
                                v___x_1385_ = lean_nat_add(v___x_1375_, v_size_1376_);
                                v___x_1386_ = lean_nat_add(v___x_1385_, v_size_1377_);
                                lean_dec(v_size_1377_);
                                lean_dec(v___x_1385_);
                                if v_isShared_1232_ == 0 {
                                    lean_ctor_set(v___x_1231_, 4, v_impl_1374_);
                                    lean_ctor_set(v___x_1231_, 0, v___x_1386_);
                                    v___x_1388_ = v___x_1231_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
                                    lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1226_);
                                    lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1227_);
                                    lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_l_1228_);
                                    lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_impl_1374_);
                                    v___x_1388_ = v_reuseFailAlloc_1389_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1453_ = (!lean_is_exclusive(v_impl_1374_)) as u8;
                                if v_isSharedCheck_1453_ == 0 {
                                    v_unused_1454_ = lean_ctor_get(v_impl_1374_, 4);
                                    lean_dec(v_unused_1454_);
                                    v_unused_1455_ = lean_ctor_get(v_impl_1374_, 3);
                                    lean_dec(v_unused_1455_);
                                    v_unused_1456_ = lean_ctor_get(v_impl_1374_, 2);
                                    lean_dec(v_unused_1456_);
                                    v_unused_1457_ = lean_ctor_get(v_impl_1374_, 1);
                                    lean_dec(v_unused_1457_);
                                    v_unused_1458_ = lean_ctor_get(v_impl_1374_, 0);
                                    lean_dec(v_unused_1458_);
                                    v___x_1391_ = v_impl_1374_;
                                    v_isShared_1392_ = v_isSharedCheck_1453_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1374_);
                                    v___x_1391_ = lean_box(0);
                                    v_isShared_1392_ = v_isSharedCheck_1453_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1459_ = lean_ctor_get(v_impl_1374_, 3);
                            lean_inc(v_l_1459_);
                            if lean_obj_tag(v_l_1459_) == 0 {
                                v_r_1460_ = lean_ctor_get(v_impl_1374_, 4);
                                v_k_1461_ = lean_ctor_get(v_impl_1374_, 1);
                                v_v_1462_ = lean_ctor_get(v_impl_1374_, 2);
                                v_isSharedCheck_1485_ = (!lean_is_exclusive(v_impl_1374_)) as u8;
                                if v_isSharedCheck_1485_ == 0 {
                                    v_unused_1486_ = lean_ctor_get(v_impl_1374_, 3);
                                    lean_dec(v_unused_1486_);
                                    v_unused_1487_ = lean_ctor_get(v_impl_1374_, 0);
                                    lean_dec(v_unused_1487_);
                                    v___x_1464_ = v_impl_1374_;
                                    v_isShared_1465_ = v_isSharedCheck_1485_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_1460_);
                                    lean_inc(v_v_1462_);
                                    lean_inc(v_k_1461_);
                                    lean_dec(v_impl_1374_);
                                    v___x_1464_ = lean_box(0);
                                    v_isShared_1465_ = v_isSharedCheck_1485_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1488_ = lean_ctor_get(v_impl_1374_, 4);
                                lean_inc(v_r_1488_);
                                if lean_obj_tag(v_r_1488_) == 0 {
                                    v_k_1489_ = lean_ctor_get(v_impl_1374_, 1);
                                    v_v_1490_ = lean_ctor_get(v_impl_1374_, 2);
                                    v_isSharedCheck_1501_ =
                                        (!lean_is_exclusive(v_impl_1374_)) as u8;
                                    if v_isSharedCheck_1501_ == 0 {
                                        v_unused_1502_ = lean_ctor_get(v_impl_1374_, 4);
                                        lean_dec(v_unused_1502_);
                                        v_unused_1503_ = lean_ctor_get(v_impl_1374_, 3);
                                        lean_dec(v_unused_1503_);
                                        v_unused_1504_ = lean_ctor_get(v_impl_1374_, 0);
                                        lean_dec(v_unused_1504_);
                                        v___x_1492_ = v_impl_1374_;
                                        v_isShared_1493_ = v_isSharedCheck_1501_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1490_);
                                        lean_inc(v_k_1489_);
                                        lean_dec(v_impl_1374_);
                                        v___x_1492_ = lean_box(0);
                                        v_isShared_1493_ = v_isSharedCheck_1501_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1505_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1232_ == 0 {
                                        lean_ctor_set(v___x_1231_, 4, v_impl_1374_);
                                        lean_ctor_set(v___x_1231_, 3, v_r_1488_);
                                        lean_ctor_set(v___x_1231_, 0, v___x_1505_);
                                        v___x_1507_ = v___x_1231_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
                                        lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1226_);
                                        lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1227_);
                                        lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1488_);
                                        lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_impl_1374_);
                                        v___x_1507_ = v_reuseFailAlloc_1508_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1248_;
            }
            3 => {
                v_size_1253_ = lean_ctor_get(v_l_1240_, 0);
                v_size_1254_ = lean_ctor_get(v_r_1241_, 0);
                v_k_1255_ = lean_ctor_get(v_r_1241_, 1);
                v_v_1256_ = lean_ctor_get(v_r_1241_, 2);
                v_l_1257_ = lean_ctor_get(v_r_1241_, 3);
                v_r_1258_ = lean_ctor_get(v_r_1241_, 4);
                v___x_1259_ = lean_unsigned_to_nat(2);
                v___x_1260_ = lean_nat_mul(v___x_1259_, v_size_1253_);
                v___x_1261_ = lean_nat_dec_lt(v_size_1254_, v___x_1260_);
                lean_dec(v___x_1260_);
                if v___x_1261_ == 0 {
                    lean_inc(v_r_1258_);
                    lean_inc(v_l_1257_);
                    lean_inc(v_v_1256_);
                    lean_inc(v_k_1255_);
                    v_isSharedCheck_1290_ = (!lean_is_exclusive(v_r_1241_)) as u8;
                    if v_isSharedCheck_1290_ == 0 {
                        v_unused_1291_ = lean_ctor_get(v_r_1241_, 4);
                        lean_dec(v_unused_1291_);
                        v_unused_1292_ = lean_ctor_get(v_r_1241_, 3);
                        lean_dec(v_unused_1292_);
                        v_unused_1293_ = lean_ctor_get(v_r_1241_, 2);
                        lean_dec(v_unused_1293_);
                        v_unused_1294_ = lean_ctor_get(v_r_1241_, 1);
                        lean_dec(v_unused_1294_);
                        v_unused_1295_ = lean_ctor_get(v_r_1241_, 0);
                        lean_dec(v_unused_1295_);
                        v___x_1263_ = v_r_1241_;
                        v_isShared_1264_ = v_isSharedCheck_1290_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_1241_);
                        v___x_1263_ = lean_box(0);
                        v_isShared_1264_ = v_isSharedCheck_1290_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1231_);
                    v___x_1296_ = lean_nat_add(v___x_1235_, v_size_1237_);
                    lean_dec(v_size_1237_);
                    v___x_1297_ = lean_nat_add(v___x_1296_, v_size_1236_);
                    lean_dec(v___x_1296_);
                    v___x_1298_ = lean_nat_add(v___x_1235_, v_size_1236_);
                    v___x_1299_ = lean_nat_add(v___x_1298_, v_size_1254_);
                    lean_dec(v___x_1298_);
                    lean_inc_ref(v_r_1229_);
                    if v_isShared_1252_ == 0 {
                        lean_ctor_set(v___x_1251_, 4, v_r_1229_);
                        lean_ctor_set(v___x_1251_, 3, v_r_1241_);
                        lean_ctor_set(v___x_1251_, 2, v_v_1227_);
                        lean_ctor_set(v___x_1251_, 1, v_k_1226_);
                        lean_ctor_set(v___x_1251_, 0, v___x_1299_);
                        v___x_1301_ = v___x_1251_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1299_);
                        lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_k_1226_);
                        lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_v_1227_);
                        lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_r_1241_);
                        lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_r_1229_);
                        v___x_1301_ = v_reuseFailAlloc_1314_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1265_ = lean_nat_add(v___x_1235_, v_size_1237_);
                lean_dec(v_size_1237_);
                v___x_1266_ = lean_nat_add(v___x_1265_, v_size_1236_);
                lean_dec(v___x_1265_);
                v___x_1278_ = lean_nat_add(v___x_1235_, v_size_1253_);
                if lean_obj_tag(v_l_1257_) == 0 {
                    v_size_1288_ = lean_ctor_get(v_l_1257_, 0);
                    lean_inc(v_size_1288_);
                    v___y_1280_ = v_size_1288_;
                    state = 8;
                    continue;
                } else {
                    v___x_1289_ = lean_unsigned_to_nat(0);
                    v___y_1280_ = v___x_1289_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1271_ = lean_nat_add(v___y_1268_, v___y_1270_);
                lean_dec(v___y_1270_);
                lean_dec(v___y_1268_);
                if v_isShared_1264_ == 0 {
                    lean_ctor_set(v___x_1263_, 4, v_r_1229_);
                    lean_ctor_set(v___x_1263_, 3, v_r_1258_);
                    lean_ctor_set(v___x_1263_, 2, v_v_1227_);
                    lean_ctor_set(v___x_1263_, 1, v_k_1226_);
                    lean_ctor_set(v___x_1263_, 0, v___x_1271_);
                    v___x_1273_ = v___x_1263_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_r_1258_);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_r_1229_);
                    v___x_1273_ = v_reuseFailAlloc_1277_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1252_ == 0 {
                    lean_ctor_set(v___x_1251_, 4, v___x_1273_);
                    lean_ctor_set(v___x_1251_, 3, v___y_1269_);
                    lean_ctor_set(v___x_1251_, 2, v_v_1256_);
                    lean_ctor_set(v___x_1251_, 1, v_k_1255_);
                    lean_ctor_set(v___x_1251_, 0, v___x_1266_);
                    v___x_1275_ = v___x_1251_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1266_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_k_1255_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_v_1256_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___y_1269_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___x_1273_);
                    v___x_1275_ = v_reuseFailAlloc_1276_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1275_;
            }
            8 => {
                v___x_1281_ = lean_nat_add(v___x_1278_, v___y_1280_);
                lean_dec(v___y_1280_);
                lean_dec(v___x_1278_);
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 4, v_l_1257_);
                    lean_ctor_set(v___x_1231_, 3, v_l_1240_);
                    lean_ctor_set(v___x_1231_, 2, v_v_1239_);
                    lean_ctor_set(v___x_1231_, 1, v_k_1238_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1281_);
                    v___x_1283_ = v___x_1231_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
                    lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1238_);
                    lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1239_);
                    lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_l_1240_);
                    lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_l_1257_);
                    v___x_1283_ = v_reuseFailAlloc_1287_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1284_ = lean_nat_add(v___x_1235_, v_size_1236_);
                if lean_obj_tag(v_r_1258_) == 0 {
                    v_size_1285_ = lean_ctor_get(v_r_1258_, 0);
                    lean_inc(v_size_1285_);
                    v___y_1268_ = v___x_1284_;
                    v___y_1269_ = v___x_1283_;
                    v___y_1270_ = v_size_1285_;
                    state = 5;
                    continue;
                } else {
                    v___x_1286_ = lean_unsigned_to_nat(0);
                    v___y_1268_ = v___x_1284_;
                    v___y_1269_ = v___x_1283_;
                    v___y_1270_ = v___x_1286_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1308_ = (!lean_is_exclusive(v_r_1229_)) as u8;
                if v_isSharedCheck_1308_ == 0 {
                    v_unused_1309_ = lean_ctor_get(v_r_1229_, 4);
                    lean_dec(v_unused_1309_);
                    v_unused_1310_ = lean_ctor_get(v_r_1229_, 3);
                    lean_dec(v_unused_1310_);
                    v_unused_1311_ = lean_ctor_get(v_r_1229_, 2);
                    lean_dec(v_unused_1311_);
                    v_unused_1312_ = lean_ctor_get(v_r_1229_, 1);
                    lean_dec(v_unused_1312_);
                    v_unused_1313_ = lean_ctor_get(v_r_1229_, 0);
                    lean_dec(v_unused_1313_);
                    v___x_1303_ = v_r_1229_;
                    v_isShared_1304_ = v_isSharedCheck_1308_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_1229_);
                    v___x_1303_ = lean_box(0);
                    v_isShared_1304_ = v_isSharedCheck_1308_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1304_ == 0 {
                    lean_ctor_set(v___x_1303_, 4, v___x_1301_);
                    lean_ctor_set(v___x_1303_, 3, v_l_1240_);
                    lean_ctor_set(v___x_1303_, 2, v_v_1239_);
                    lean_ctor_set(v___x_1303_, 1, v_k_1238_);
                    lean_ctor_set(v___x_1303_, 0, v___x_1297_);
                    v___x_1306_ = v___x_1303_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1297_);
                    lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_k_1238_);
                    lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_v_1239_);
                    lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_l_1240_);
                    lean_ctor_set(v_reuseFailAlloc_1307_, 4, v___x_1301_);
                    v___x_1306_ = v_reuseFailAlloc_1307_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1306_;
            }
            13 => {
                v___x_1328_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_1322_);
                if v_isShared_1327_ == 0 {
                    lean_ctor_set(v___x_1326_, 3, v_r_1322_);
                    lean_ctor_set(v___x_1326_, 2, v_v_1227_);
                    lean_ctor_set(v___x_1326_, 1, v_k_1226_);
                    lean_ctor_set(v___x_1326_, 0, v___x_1235_);
                    v___x_1330_ = v___x_1326_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1235_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_r_1322_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_r_1322_);
                    v___x_1330_ = v_reuseFailAlloc_1334_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 4, v___x_1330_);
                    lean_ctor_set(v___x_1231_, 3, v_l_1321_);
                    lean_ctor_set(v___x_1231_, 2, v_v_1324_);
                    lean_ctor_set(v___x_1231_, 1, v_k_1323_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1328_);
                    v___x_1332_ = v___x_1231_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_k_1323_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_v_1324_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_l_1321_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 4, v___x_1330_);
                    v___x_1332_ = v_reuseFailAlloc_1333_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1332_;
            }
            16 => {
                v_k_1344_ = lean_ctor_get(v_r_1338_, 1);
                v_v_1345_ = lean_ctor_get(v_r_1338_, 2);
                v_isSharedCheck_1359_ = (!lean_is_exclusive(v_r_1338_)) as u8;
                if v_isSharedCheck_1359_ == 0 {
                    v_unused_1360_ = lean_ctor_get(v_r_1338_, 4);
                    lean_dec(v_unused_1360_);
                    v_unused_1361_ = lean_ctor_get(v_r_1338_, 3);
                    lean_dec(v_unused_1361_);
                    v_unused_1362_ = lean_ctor_get(v_r_1338_, 0);
                    lean_dec(v_unused_1362_);
                    v___x_1347_ = v_r_1338_;
                    v_isShared_1348_ = v_isSharedCheck_1359_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_1345_);
                    lean_inc(v_k_1344_);
                    lean_dec(v_r_1338_);
                    v___x_1347_ = lean_box(0);
                    v_isShared_1348_ = v_isSharedCheck_1359_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1349_ = lean_unsigned_to_nat(3);
                if v_isShared_1348_ == 0 {
                    lean_ctor_set(v___x_1347_, 4, v_l_1321_);
                    lean_ctor_set(v___x_1347_, 3, v_l_1321_);
                    lean_ctor_set(v___x_1347_, 2, v_v_1340_);
                    lean_ctor_set(v___x_1347_, 1, v_k_1339_);
                    lean_ctor_set(v___x_1347_, 0, v___x_1235_);
                    v___x_1351_ = v___x_1347_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1235_);
                    lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_k_1339_);
                    lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_v_1340_);
                    lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_l_1321_);
                    lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_l_1321_);
                    v___x_1351_ = v_reuseFailAlloc_1358_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1343_ == 0 {
                    lean_ctor_set(v___x_1342_, 4, v_l_1321_);
                    lean_ctor_set(v___x_1342_, 2, v_v_1227_);
                    lean_ctor_set(v___x_1342_, 1, v_k_1226_);
                    lean_ctor_set(v___x_1342_, 0, v___x_1235_);
                    v___x_1353_ = v___x_1342_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1235_);
                    lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_k_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_v_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_l_1321_);
                    lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_l_1321_);
                    v___x_1353_ = v_reuseFailAlloc_1357_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 4, v___x_1353_);
                    lean_ctor_set(v___x_1231_, 3, v___x_1351_);
                    lean_ctor_set(v___x_1231_, 2, v_v_1345_);
                    lean_ctor_set(v___x_1231_, 1, v_k_1344_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1349_);
                    v___x_1355_ = v___x_1231_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1349_);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1344_);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1345_);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 3, v___x_1351_);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 4, v___x_1353_);
                    v___x_1355_ = v_reuseFailAlloc_1356_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1355_;
            }
            21 => {
                return v___x_1369_;
            }
            22 => {
                return v___x_1372_;
            }
            23 => {
                return v___x_1388_;
            }
            24 => {
                v_size_1393_ = lean_ctor_get(v_l_1380_, 0);
                v_k_1394_ = lean_ctor_get(v_l_1380_, 1);
                v_v_1395_ = lean_ctor_get(v_l_1380_, 2);
                v_l_1396_ = lean_ctor_get(v_l_1380_, 3);
                v_r_1397_ = lean_ctor_get(v_l_1380_, 4);
                v_size_1398_ = lean_ctor_get(v_r_1381_, 0);
                v___x_1399_ = lean_unsigned_to_nat(2);
                v___x_1400_ = lean_nat_mul(v___x_1399_, v_size_1398_);
                v___x_1401_ = lean_nat_dec_lt(v_size_1393_, v___x_1400_);
                lean_dec(v___x_1400_);
                if v___x_1401_ == 0 {
                    lean_inc(v_r_1397_);
                    lean_inc(v_l_1396_);
                    lean_inc(v_v_1395_);
                    lean_inc(v_k_1394_);
                    v_isSharedCheck_1429_ = (!lean_is_exclusive(v_l_1380_)) as u8;
                    if v_isSharedCheck_1429_ == 0 {
                        v_unused_1430_ = lean_ctor_get(v_l_1380_, 4);
                        lean_dec(v_unused_1430_);
                        v_unused_1431_ = lean_ctor_get(v_l_1380_, 3);
                        lean_dec(v_unused_1431_);
                        v_unused_1432_ = lean_ctor_get(v_l_1380_, 2);
                        lean_dec(v_unused_1432_);
                        v_unused_1433_ = lean_ctor_get(v_l_1380_, 1);
                        lean_dec(v_unused_1433_);
                        v_unused_1434_ = lean_ctor_get(v_l_1380_, 0);
                        lean_dec(v_unused_1434_);
                        v___x_1403_ = v_l_1380_;
                        v_isShared_1404_ = v_isSharedCheck_1429_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_1380_);
                        v___x_1403_ = lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1429_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1231_);
                    v___x_1435_ = lean_nat_add(v___x_1375_, v_size_1376_);
                    v___x_1436_ = lean_nat_add(v___x_1435_, v_size_1377_);
                    lean_dec(v_size_1377_);
                    v___x_1437_ = lean_nat_add(v___x_1435_, v_size_1393_);
                    lean_dec(v___x_1435_);
                    lean_inc_ref(v_l_1228_);
                    if v_isShared_1392_ == 0 {
                        lean_ctor_set(v___x_1391_, 4, v_l_1380_);
                        lean_ctor_set(v___x_1391_, 3, v_l_1228_);
                        lean_ctor_set(v___x_1391_, 2, v_v_1227_);
                        lean_ctor_set(v___x_1391_, 1, v_k_1226_);
                        lean_ctor_set(v___x_1391_, 0, v___x_1437_);
                        v___x_1439_ = v___x_1391_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1437_);
                        lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1226_);
                        lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1227_);
                        lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_l_1228_);
                        lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_l_1380_);
                        v___x_1439_ = v_reuseFailAlloc_1452_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1405_ = lean_nat_add(v___x_1375_, v_size_1376_);
                v___x_1406_ = lean_nat_add(v___x_1405_, v_size_1377_);
                lean_dec(v_size_1377_);
                if lean_obj_tag(v_l_1396_) == 0 {
                    v_size_1427_ = lean_ctor_get(v_l_1396_, 0);
                    lean_inc(v_size_1427_);
                    v___y_1419_ = v_size_1427_;
                    state = 29;
                    continue;
                } else {
                    v___x_1428_ = lean_unsigned_to_nat(0);
                    v___y_1419_ = v___x_1428_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1411_ = lean_nat_add(v___y_1409_, v___y_1410_);
                lean_dec(v___y_1410_);
                lean_dec(v___y_1409_);
                if v_isShared_1404_ == 0 {
                    lean_ctor_set(v___x_1403_, 4, v_r_1381_);
                    lean_ctor_set(v___x_1403_, 3, v_r_1397_);
                    lean_ctor_set(v___x_1403_, 2, v_v_1379_);
                    lean_ctor_set(v___x_1403_, 1, v_k_1378_);
                    lean_ctor_set(v___x_1403_, 0, v___x_1411_);
                    v___x_1413_ = v___x_1403_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1411_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1378_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1379_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_r_1397_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_r_1381_);
                    v___x_1413_ = v_reuseFailAlloc_1417_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1392_ == 0 {
                    lean_ctor_set(v___x_1391_, 4, v___x_1413_);
                    lean_ctor_set(v___x_1391_, 3, v___y_1408_);
                    lean_ctor_set(v___x_1391_, 2, v_v_1395_);
                    lean_ctor_set(v___x_1391_, 1, v_k_1394_);
                    lean_ctor_set(v___x_1391_, 0, v___x_1406_);
                    v___x_1415_ = v___x_1391_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1406_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1394_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1395_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___y_1408_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 4, v___x_1413_);
                    v___x_1415_ = v_reuseFailAlloc_1416_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1415_;
            }
            29 => {
                v___x_1420_ = lean_nat_add(v___x_1405_, v___y_1419_);
                lean_dec(v___y_1419_);
                lean_dec(v___x_1405_);
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 4, v_l_1396_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1231_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1420_);
                    lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_k_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_v_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_l_1228_);
                    lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_l_1396_);
                    v___x_1422_ = v_reuseFailAlloc_1426_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1423_ = lean_nat_add(v___x_1375_, v_size_1398_);
                if lean_obj_tag(v_r_1397_) == 0 {
                    v_size_1424_ = lean_ctor_get(v_r_1397_, 0);
                    lean_inc(v_size_1424_);
                    v___y_1408_ = v___x_1422_;
                    v___y_1409_ = v___x_1423_;
                    v___y_1410_ = v_size_1424_;
                    state = 26;
                    continue;
                } else {
                    v___x_1425_ = lean_unsigned_to_nat(0);
                    v___y_1408_ = v___x_1422_;
                    v___y_1409_ = v___x_1423_;
                    v___y_1410_ = v___x_1425_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1446_ = (!lean_is_exclusive(v_l_1228_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v_unused_1447_ = lean_ctor_get(v_l_1228_, 4);
                    lean_dec(v_unused_1447_);
                    v_unused_1448_ = lean_ctor_get(v_l_1228_, 3);
                    lean_dec(v_unused_1448_);
                    v_unused_1449_ = lean_ctor_get(v_l_1228_, 2);
                    lean_dec(v_unused_1449_);
                    v_unused_1450_ = lean_ctor_get(v_l_1228_, 1);
                    lean_dec(v_unused_1450_);
                    v_unused_1451_ = lean_ctor_get(v_l_1228_, 0);
                    lean_dec(v_unused_1451_);
                    v___x_1441_ = v_l_1228_;
                    v_isShared_1442_ = v_isSharedCheck_1446_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_1228_);
                    v___x_1441_ = lean_box(0);
                    v_isShared_1442_ = v_isSharedCheck_1446_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1442_ == 0 {
                    lean_ctor_set(v___x_1441_, 4, v_r_1381_);
                    lean_ctor_set(v___x_1441_, 3, v___x_1439_);
                    lean_ctor_set(v___x_1441_, 2, v_v_1379_);
                    lean_ctor_set(v___x_1441_, 1, v_k_1378_);
                    lean_ctor_set(v___x_1441_, 0, v___x_1436_);
                    v___x_1444_ = v___x_1441_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1436_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1378_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1379_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 3, v___x_1439_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1381_);
                    v___x_1444_ = v_reuseFailAlloc_1445_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1444_;
            }
            34 => {
                v_k_1466_ = lean_ctor_get(v_l_1459_, 1);
                v_v_1467_ = lean_ctor_get(v_l_1459_, 2);
                v_isSharedCheck_1481_ = (!lean_is_exclusive(v_l_1459_)) as u8;
                if v_isSharedCheck_1481_ == 0 {
                    v_unused_1482_ = lean_ctor_get(v_l_1459_, 4);
                    lean_dec(v_unused_1482_);
                    v_unused_1483_ = lean_ctor_get(v_l_1459_, 3);
                    lean_dec(v_unused_1483_);
                    v_unused_1484_ = lean_ctor_get(v_l_1459_, 0);
                    lean_dec(v_unused_1484_);
                    v___x_1469_ = v_l_1459_;
                    v_isShared_1470_ = v_isSharedCheck_1481_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_1467_);
                    lean_inc(v_k_1466_);
                    lean_dec(v_l_1459_);
                    v___x_1469_ = lean_box(0);
                    v_isShared_1470_ = v_isSharedCheck_1481_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1471_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_1460_, 2);
                if v_isShared_1470_ == 0 {
                    lean_ctor_set(v___x_1469_, 4, v_r_1460_);
                    lean_ctor_set(v___x_1469_, 3, v_r_1460_);
                    lean_ctor_set(v___x_1469_, 2, v_v_1227_);
                    lean_ctor_set(v___x_1469_, 1, v_k_1226_);
                    lean_ctor_set(v___x_1469_, 0, v___x_1375_);
                    v___x_1473_ = v___x_1469_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1375_);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1460_);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1460_);
                    v___x_1473_ = v_reuseFailAlloc_1480_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_1460_);
                if v_isShared_1465_ == 0 {
                    lean_ctor_set(v___x_1464_, 3, v_r_1460_);
                    lean_ctor_set(v___x_1464_, 0, v___x_1375_);
                    v___x_1475_ = v___x_1464_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1375_);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1461_);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1462_);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_r_1460_);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_r_1460_);
                    v___x_1475_ = v_reuseFailAlloc_1479_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 4, v___x_1475_);
                    lean_ctor_set(v___x_1231_, 3, v___x_1473_);
                    lean_ctor_set(v___x_1231_, 2, v_v_1467_);
                    lean_ctor_set(v___x_1231_, 1, v_k_1466_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1471_);
                    v___x_1477_ = v___x_1231_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1471_);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1466_);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1467_);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 3, v___x_1473_);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 4, v___x_1475_);
                    v___x_1477_ = v_reuseFailAlloc_1478_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1477_;
            }
            39 => {
                v___x_1494_ = lean_unsigned_to_nat(3);
                if v_isShared_1493_ == 0 {
                    lean_ctor_set(v___x_1492_, 4, v_l_1459_);
                    lean_ctor_set(v___x_1492_, 2, v_v_1227_);
                    lean_ctor_set(v___x_1492_, 1, v_k_1226_);
                    lean_ctor_set(v___x_1492_, 0, v___x_1375_);
                    v___x_1496_ = v___x_1492_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1375_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1459_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1459_);
                    v___x_1496_ = v_reuseFailAlloc_1500_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 4, v_r_1488_);
                    lean_ctor_set(v___x_1231_, 3, v___x_1496_);
                    lean_ctor_set(v___x_1231_, 2, v_v_1490_);
                    lean_ctor_set(v___x_1231_, 1, v_k_1489_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1494_);
                    v___x_1498_ = v___x_1231_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1494_);
                    lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1489_);
                    lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1490_);
                    lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1496_);
                    lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_r_1488_);
                    v___x_1498_ = v_reuseFailAlloc_1499_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1498_;
            }
            42 => {
                return v___x_1507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(
    mut v_k_1512_: *mut LeanObject,
    mut v_t_1513_: *mut LeanObject,
) -> u8 {
    let mut v_k_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1513_) == 0 {
                    v_k_1514_ = lean_ctor_get(v_t_1513_, 1);
                    v_l_1515_ = lean_ctor_get(v_t_1513_, 3);
                    v_r_1516_ = lean_ctor_get(v_t_1513_, 4);
                    v___x_1517_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1512_, v_k_1514_);
                    match v___x_1517_ {
                        0 => {
                            v_t_1513_ = v_l_1515_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_1519_ = 1;
                            return v___x_1519_;
                        }
                        _ => {
                            v_t_1513_ = v_r_1516_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1521_ = 0;
                    return v___x_1521_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(
    mut v_k_1522_: *mut LeanObject,
    mut v_t_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1524_: u8 = 0;
    let mut v_r_1525_: *mut LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_1522_, v_t_1523_);
    lean_dec(v_t_1523_);
    lean_dec(v_k_1522_);
    v_r_1525_ = lean_box((v_res_1524_) as usize);
    return v_r_1525_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectFnBody(
    mut v_x_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: usize = 0;
    let mut v___x_1571_: usize = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: usize = 0;
    let mut v___x_1574_: usize = 0;
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1526_) {
                0 => {
                    v_e_1529_ = lean_ctor_get(v_x_1526_, 2);
                    lean_inc_ref(v_e_1529_);
                    v_b_1530_ = lean_ctor_get(v_x_1526_, 3);
                    lean_inc(v_b_1530_);
                    lean_dec_ref_known(v_x_1526_, 4);
                    match lean_obj_tag(v_e_1529_) {
                        6 => {
                            v_c_1554_ = lean_ctor_get(v_e_1529_, 0);
                            lean_inc(v_c_1554_);
                            lean_dec_ref_known(v_e_1529_, 2);
                            v_f_1544_ = v_c_1554_;
                            v___y_1545_ = v_a_1527_;
                            v___y_1546_ = v_a_1528_;
                            state = 2;
                            continue;
                        }
                        7 => {
                            v_c_1555_ = lean_ctor_get(v_e_1529_, 0);
                            lean_inc(v_c_1555_);
                            lean_dec_ref_known(v_e_1529_, 2);
                            v_f_1544_ = v_c_1555_;
                            v___y_1545_ = v_a_1527_;
                            v___y_1546_ = v_a_1528_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_e_1529_);
                            v_x_1526_ = v_b_1530_;
                            state = 0;
                            continue;
                        }
                    }
                }
                1 => {
                    v_v_1557_ = lean_ctor_get(v_x_1526_, 2);
                    lean_inc(v_v_1557_);
                    v_b_1558_ = lean_ctor_get(v_x_1526_, 3);
                    lean_inc(v_b_1558_);
                    lean_dec_ref_known(v_x_1526_, 4);
                    v___x_1559_ =
                        l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_1557_, v_a_1527_, v_a_1528_);
                    v_snd_1560_ = lean_ctor_get(v___x_1559_, 1);
                    lean_inc(v_snd_1560_);
                    lean_dec_ref(v___x_1559_);
                    v_x_1526_ = v_b_1558_;
                    v_a_1528_ = v_snd_1560_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_cs_1562_ = lean_ctor_get(v_x_1526_, 3);
                    lean_inc_ref(v_cs_1562_);
                    lean_dec_ref_known(v_x_1526_, 4);
                    v___x_1563_ = lean_unsigned_to_nat(0);
                    v___x_1564_ = lean_array_get_size(v_cs_1562_);
                    v___x_1565_ = lean_box(0);
                    v___x_1566_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
                    if v___x_1566_ == 0 {
                        lean_dec_ref(v_cs_1562_);
                        v___x_1567_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1567_, 0, v___x_1565_);
                        lean_ctor_set(v___x_1567_, 1, v_a_1528_);
                        return v___x_1567_;
                    } else {
                        v___x_1568_ = lean_nat_dec_le(v___x_1564_, v___x_1564_);
                        if v___x_1568_ == 0 {
                            if v___x_1566_ == 0 {
                                lean_dec_ref(v_cs_1562_);
                                v___x_1569_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_1569_, 0, v___x_1565_);
                                lean_ctor_set(v___x_1569_, 1, v_a_1528_);
                                return v___x_1569_;
                            } else {
                                v___x_1570_ = 0usize;
                                v___x_1571_ = lean_usize_of_nat(v___x_1564_);
                                v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_1562_, v___x_1570_, v___x_1571_, v___x_1565_, v_a_1527_, v_a_1528_);
                                lean_dec_ref(v_cs_1562_);
                                return v___x_1572_;
                            }
                        } else {
                            v___x_1573_ = 0usize;
                            v___x_1574_ = lean_usize_of_nat(v___x_1564_);
                            v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_1562_, v___x_1573_, v___x_1574_, v___x_1565_, v_a_1527_, v_a_1528_);
                            lean_dec_ref(v_cs_1562_);
                            return v___x_1575_;
                        }
                    }
                }
                _ => {
                    v___x_1576_ = l_Lean_IR_FnBody_isTerminal(v_x_1526_);
                    if v___x_1576_ == 0 {
                        v___x_1577_ = l_Lean_IR_FnBody_body(v_x_1526_);
                        lean_dec(v_x_1526_);
                        v_x_1526_ = v___x_1577_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_x_1526_);
                        v___x_1579_ = lean_box(0);
                        v___x_1580_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1580_, 0, v___x_1579_);
                        lean_ctor_set(v___x_1580_, 1, v_a_1528_);
                        return v___x_1580_;
                    }
                }
            },
            1 => {
                v___x_1537_ = (lean_unbox(v_fst_1535_) as u8);
                lean_dec(v_fst_1535_);
                if v___x_1537_ == 0 {
                    v___x_1538_ = lean_array_push(v___y_1534_, v___y_1533_);
                    v___x_1539_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1539_, 0, v_snd_1536_);
                    lean_ctor_set(v___x_1539_, 1, v___x_1538_);
                    v_x_1526_ = v_b_1530_;
                    v_a_1527_ = v___y_1532_;
                    v_a_1528_ = v___x_1539_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___y_1533_);
                    v___x_1541_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1541_, 0, v_snd_1536_);
                    lean_ctor_set(v___x_1541_, 1, v___y_1534_);
                    v_x_1526_ = v_b_1530_;
                    v_a_1527_ = v___y_1532_;
                    v_a_1528_ = v___x_1541_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_set_1547_ = lean_ctor_get(v___y_1546_, 0);
                lean_inc(v_set_1547_);
                v_order_1548_ = lean_ctor_get(v___y_1546_, 1);
                lean_inc_ref(v_order_1548_);
                lean_dec_ref(v___y_1546_);
                v___x_1549_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_f_1544_, v_set_1547_);
                if v___x_1549_ == 0 {
                    v___x_1550_ = lean_box(0);
                    lean_inc(v_f_1544_);
                    v___x_1551_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_f_1544_, v___x_1550_, v_set_1547_);
                    v___x_1552_ = lean_box((v___x_1549_) as usize);
                    v___y_1532_ = v___y_1545_;
                    v___y_1533_ = v_f_1544_;
                    v___y_1534_ = v_order_1548_;
                    v_fst_1535_ = v___x_1552_;
                    v_snd_1536_ = v___x_1551_;
                    state = 1;
                    continue;
                } else {
                    v___x_1553_ = lean_box((v___x_1549_) as usize);
                    v___y_1532_ = v___y_1545_;
                    v___y_1533_ = v_f_1544_;
                    v___y_1534_ = v_order_1548_;
                    v_fst_1535_ = v___x_1553_;
                    v_snd_1536_ = v_set_1547_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(
    mut v_as_1581_: *mut LeanObject,
    mut v_i_1582_: usize,
    mut v_stop_1583_: usize,
    mut v_b_1584_: *mut LeanObject,
    mut v___y_1585_: *mut LeanObject,
    mut v___y_1586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: usize = 0;
    let mut v___x_1594_: usize = 0;
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1587_ = lean_usize_dec_eq(v_i_1582_, v_stop_1583_);
                if v___x_1587_ == 0 {
                    v___x_1588_ = lean_array_uget_borrowed(v_as_1581_, v_i_1582_);
                    v___x_1589_ = l_Lean_IR_Alt_body(v___x_1588_);
                    v___x_1590_ = l_Lean_IR_CollectUsedDecls_collectFnBody(
                        v___x_1589_,
                        v___y_1585_,
                        v___y_1586_,
                    );
                    v_fst_1591_ = lean_ctor_get(v___x_1590_, 0);
                    lean_inc(v_fst_1591_);
                    v_snd_1592_ = lean_ctor_get(v___x_1590_, 1);
                    lean_inc(v_snd_1592_);
                    lean_dec_ref(v___x_1590_);
                    v___x_1593_ = 1usize;
                    v___x_1594_ = lean_usize_add(v_i_1582_, v___x_1593_);
                    v_i_1582_ = v___x_1594_;
                    v_b_1584_ = v_fst_1591_;
                    v___y_1586_ = v_snd_1592_;
                    state = 0;
                    continue;
                } else {
                    v___x_1596_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1596_, 0, v_b_1584_);
                    lean_ctor_set(v___x_1596_, 1, v___y_1586_);
                    return v___x_1596_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(
    mut v_as_1597_: *mut LeanObject,
    mut v_i_1598_: *mut LeanObject,
    mut v_stop_1599_: *mut LeanObject,
    mut v_b_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1603_: usize = 0;
    let mut v_stop_boxed_1604_: usize = 0;
    let mut v_res_1605_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1603_ = lean_unbox_usize(v_i_1598_);
    lean_dec(v_i_1598_);
    v_stop_boxed_1604_ = lean_unbox_usize(v_stop_1599_);
    lean_dec(v_stop_1599_);
    v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_1597_, v_i_boxed_1603_, v_stop_boxed_1604_, v_b_1600_, v___y_1601_, v___y_1602_);
    lean_dec_ref(v___y_1601_);
    lean_dec_ref(v_as_1597_);
    return v_res_1605_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(
    mut v_x_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1609_: *mut LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_1606_, v_a_1607_, v_a_1608_);
    lean_dec_ref(v_a_1607_);
    return v_res_1609_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(
    mut v_00_u03b2_1610_: *mut LeanObject,
    mut v_k_1611_: *mut LeanObject,
    mut v_t_1612_: *mut LeanObject,
) -> u8 {
    let mut v___x_1613_: u8 = 0;
    v___x_1613_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_1611_, v_t_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(
    mut v_00_u03b2_1614_: *mut LeanObject,
    mut v_k_1615_: *mut LeanObject,
    mut v_t_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1617_: u8 = 0;
    let mut v_r_1618_: *mut LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_1614_, v_k_1615_, v_t_1616_);
    lean_dec(v_t_1616_);
    lean_dec(v_k_1615_);
    v_r_1618_ = lean_box((v_res_1617_) as usize);
    return v_r_1618_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(
    mut v_00_u03b2_1619_: *mut LeanObject,
    mut v_k_1620_: *mut LeanObject,
    mut v_v_1621_: *mut LeanObject,
    mut v_t_1622_: *mut LeanObject,
    mut v_hl_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    v___x_1624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_1620_, v_v_1621_, v_t_1622_);
    return v___x_1624_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectInitDecl(
    mut v_fn_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
    mut v_a_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_1626_);
                v___x_1628_ = lean_get_init_fn_name_for(v_a_1626_, v_fn_1625_);
                if lean_obj_tag(v___x_1628_) == 1 {
                    v_val_1629_ = lean_ctor_get(v___x_1628_, 0);
                    lean_inc(v_val_1629_);
                    lean_dec_ref_known(v___x_1628_, 1);
                    v_set_1630_ = lean_ctor_get(v_a_1627_, 0);
                    v_order_1631_ = lean_ctor_get(v_a_1627_, 1);
                    v_isSharedCheck_1653_ = (!lean_is_exclusive(v_a_1627_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1633_ = v_a_1627_;
                        v_isShared_1634_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_order_1631_);
                        lean_inc(v_set_1630_);
                        lean_dec(v_a_1627_);
                        v___x_1633_ = lean_box(0);
                        v_isShared_1634_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1628_);
                    v___x_1654_ = lean_box(0);
                    v___x_1655_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1655_, 0, v___x_1654_);
                    lean_ctor_set(v___x_1655_, 1, v_a_1627_);
                    return v___x_1655_;
                }
            }
            1 => {
                v___x_1635_ = lean_box(0);
                v___x_1649_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_1629_, v_set_1630_);
                if v___x_1649_ == 0 {
                    lean_inc(v_val_1629_);
                    v___x_1650_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_1629_, v___x_1635_, v_set_1630_);
                    v___x_1651_ = lean_box((v___x_1649_) as usize);
                    v_fst_1637_ = v___x_1651_;
                    v_snd_1638_ = v___x_1650_;
                    state = 2;
                    continue;
                } else {
                    v___x_1652_ = lean_box((v___x_1649_) as usize);
                    v_fst_1637_ = v___x_1652_;
                    v_snd_1638_ = v_set_1630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1639_ = (lean_unbox(v_fst_1637_) as u8);
                lean_dec(v_fst_1637_);
                if v___x_1639_ == 0 {
                    v___x_1640_ = lean_array_push(v_order_1631_, v_val_1629_);
                    if v_isShared_1634_ == 0 {
                        lean_ctor_set(v___x_1633_, 1, v___x_1640_);
                        lean_ctor_set(v___x_1633_, 0, v_snd_1638_);
                        v___x_1642_ = v___x_1633_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_snd_1638_);
                        lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1640_);
                        v___x_1642_ = v_reuseFailAlloc_1644_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_val_1629_);
                    if v_isShared_1634_ == 0 {
                        lean_ctor_set(v___x_1633_, 0, v_snd_1638_);
                        v___x_1646_ = v___x_1633_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_snd_1638_);
                        lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_order_1631_);
                        v___x_1646_ = v_reuseFailAlloc_1648_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1643_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1643_, 0, v___x_1635_);
                lean_ctor_set(v___x_1643_, 1, v___x_1642_);
                return v___x_1643_;
            }
            4 => {
                v___x_1647_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1647_, 0, v___x_1635_);
                lean_ctor_set(v___x_1647_, 1, v___x_1646_);
                return v___x_1647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(
    mut v_fn_1656_: *mut LeanObject,
    mut v_a_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1659_: *mut LeanObject = core::ptr::null_mut();
    v_res_1659_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_1656_, v_a_1657_, v_a_1658_);
    lean_dec_ref(v_a_1657_);
    return v_res_1659_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDecl(
    mut v_x_1660_: *mut LeanObject,
    mut v_a_1661_: *mut LeanObject,
    mut v_a_1662_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1660_) == 0 {
        let mut v_f_1663_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_1664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
        v_f_1663_ = lean_ctor_get(v_x_1660_, 0);
        lean_inc(v_f_1663_);
        v_body_1664_ = lean_ctor_get(v_x_1660_, 3);
        lean_inc(v_body_1664_);
        lean_dec_ref_known(v_x_1660_, 5);
        v___x_1665_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_1663_, v_a_1661_, v_a_1662_);
        v_snd_1666_ = lean_ctor_get(v___x_1665_, 1);
        lean_inc(v_snd_1666_);
        lean_dec_ref(v___x_1665_);
        v___x_1667_ =
            l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_1664_, v_a_1661_, v_snd_1666_);
        return v___x_1667_;
    } else {
        let mut v_f_1668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
        v_f_1668_ = lean_ctor_get(v_x_1660_, 0);
        lean_inc(v_f_1668_);
        lean_dec_ref_known(v_x_1660_, 4);
        v___x_1669_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_1668_, v_a_1661_, v_a_1662_);
        return v___x_1669_;
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDecl___boxed(
    mut v_x_1670_: *mut LeanObject,
    mut v_a_1671_: *mut LeanObject,
    mut v_a_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1673_: *mut LeanObject = core::ptr::null_mut();
    v_res_1673_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_1670_, v_a_1671_, v_a_1672_);
    lean_dec_ref(v_a_1671_);
    return v_res_1673_;
}
pub unsafe fn l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
    mut v_as_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_1674_) == 0 {
                    v___x_1677_ = lean_box(0);
                    v___x_1678_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                    lean_ctor_set(v___x_1678_, 1, v___y_1676_);
                    return v___x_1678_;
                } else {
                    v_head_1679_ = lean_ctor_get(v_as_1674_, 0);
                    lean_inc_n(v_head_1679_, 2);
                    v_tail_1680_ = lean_ctor_get(v_as_1674_, 1);
                    lean_inc(v_tail_1680_);
                    lean_dec_ref_known(v_as_1674_, 2);
                    v___x_1681_ = l_Lean_IR_CollectUsedDecls_collectDecl(
                        v_head_1679_,
                        v___y_1675_,
                        v___y_1676_,
                    );
                    v_snd_1682_ = lean_ctor_get(v___x_1681_, 1);
                    lean_inc(v_snd_1682_);
                    lean_dec_ref(v___x_1681_);
                    v_set_1683_ = lean_ctor_get(v_snd_1682_, 0);
                    v_order_1684_ = lean_ctor_get(v_snd_1682_, 1);
                    v_isSharedCheck_1707_ = (!lean_is_exclusive(v_snd_1682_)) as u8;
                    if v_isSharedCheck_1707_ == 0 {
                        v___x_1686_ = v_snd_1682_;
                        v_isShared_1687_ = v_isSharedCheck_1707_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_order_1684_);
                        lean_inc(v_set_1683_);
                        lean_dec(v_snd_1682_);
                        v___x_1686_ = lean_box(0);
                        v_isShared_1687_ = v_isSharedCheck_1707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1688_ = l_Lean_IR_Decl_name(v_head_1679_);
                lean_dec(v_head_1679_);
                v___x_1702_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_1688_, v_set_1683_);
                if v___x_1702_ == 0 {
                    v___x_1703_ = lean_box(0);
                    lean_inc(v___x_1688_);
                    v___x_1704_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_1688_, v___x_1703_, v_set_1683_);
                    v___x_1705_ = lean_box((v___x_1702_) as usize);
                    v_fst_1690_ = v___x_1705_;
                    v_snd_1691_ = v___x_1704_;
                    state = 2;
                    continue;
                } else {
                    v___x_1706_ = lean_box((v___x_1702_) as usize);
                    v_fst_1690_ = v___x_1706_;
                    v_snd_1691_ = v_set_1683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1692_ = (lean_unbox(v_fst_1690_) as u8);
                lean_dec(v_fst_1690_);
                if v___x_1692_ == 0 {
                    v___x_1693_ = lean_array_push(v_order_1684_, v___x_1688_);
                    if v_isShared_1687_ == 0 {
                        lean_ctor_set(v___x_1686_, 1, v___x_1693_);
                        lean_ctor_set(v___x_1686_, 0, v_snd_1691_);
                        v___x_1695_ = v___x_1686_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_snd_1691_);
                        lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1693_);
                        v___x_1695_ = v_reuseFailAlloc_1697_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1688_);
                    if v_isShared_1687_ == 0 {
                        lean_ctor_set(v___x_1686_, 0, v_snd_1691_);
                        v___x_1699_ = v___x_1686_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_snd_1691_);
                        lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_order_1684_);
                        v___x_1699_ = v_reuseFailAlloc_1701_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_as_1674_ = v_tail_1680_;
                v___y_1676_ = v___x_1695_;
                state = 0;
                continue;
            }
            4 => {
                v_as_1674_ = v_tail_1680_;
                v___y_1676_ = v___x_1699_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(
    mut v_as_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1711_: *mut LeanObject = core::ptr::null_mut();
    v_res_1711_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
        v_as_1708_,
        v___y_1709_,
        v___y_1710_,
    );
    lean_dec_ref(v___y_1709_);
    return v_res_1711_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDeclLoop(
    mut v_decls_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
    mut v_a_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
        v_decls_1712_,
        v_a_1713_,
        v_a_1714_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(
    mut v_decls_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1719_: *mut LeanObject = core::ptr::null_mut();
    v_res_1719_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_1716_, v_a_1717_, v_a_1718_);
    lean_dec_ref(v_a_1717_);
    return v_res_1719_;
}
pub unsafe fn _init_l_Lean_IR_collectUsedDecls___closed__1() -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = l_Lean_IR_collectUsedDecls___closed__0;
    v___x_1723_ = l_Lean_NameSet_empty;
    v___x_1724_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1724_, 0, v___x_1723_);
    lean_ctor_set(v___x_1724_, 1, v___x_1722_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_IR_collectUsedDecls(
    mut v_env_1725_: *mut LeanObject,
    mut v_decls_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_order_1730_: *mut LeanObject = core::ptr::null_mut();
    v___x_1727_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_collectUsedDecls___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_collectUsedDecls___closed__1_once),
        _init_l_Lean_IR_collectUsedDecls___closed__1,
    );
    v___x_1728_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
        v_decls_1726_,
        v_env_1725_,
        v___x_1727_,
    );
    v_snd_1729_ = lean_ctor_get(v___x_1728_, 1);
    lean_inc(v_snd_1729_);
    lean_dec_ref(v___x_1728_);
    v_order_1730_ = lean_ctor_get(v_snd_1729_, 1);
    lean_inc_ref(v_order_1730_);
    lean_dec(v_snd_1729_);
    return v_order_1730_;
}
pub unsafe fn l_Lean_IR_collectUsedDecls___boxed(
    mut v_env_1731_: *mut LeanObject,
    mut v_decls_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1733_: *mut LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Lean_IR_collectUsedDecls(v_env_1731_, v_decls_1732_);
    lean_dec_ref(v_env_1731_);
    return v_res_1733_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectVar(
    mut v_x_1736_: *mut LeanObject,
    mut v_t_1737_: *mut LeanObject,
    mut v_x_1738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1739_ = lean_ctor_get(v_x_1738_, 0);
                v_snd_1740_ = lean_ctor_get(v_x_1738_, 1);
                v_isSharedCheck_1750_ = (!lean_is_exclusive(v_x_1738_)) as u8;
                if v_isSharedCheck_1750_ == 0 {
                    v___x_1742_ = v_x_1738_;
                    v_isShared_1743_ = v_isSharedCheck_1750_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1740_);
                    lean_inc(v_fst_1739_);
                    lean_dec(v_x_1738_);
                    v___x_1742_ = lean_box(0);
                    v_isShared_1743_ = v_isSharedCheck_1750_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1744_ = l_Lean_IR_CollectMaps_collectVar___closed__0;
                v___x_1745_ = l_Lean_IR_CollectMaps_collectVar___closed__1;
                v___x_1746_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_1744_,
                    v___x_1745_,
                    v_fst_1739_,
                    v_x_1736_,
                    v_t_1737_,
                );
                if v_isShared_1743_ == 0 {
                    lean_ctor_set(v___x_1742_, 0, v___x_1746_);
                    v___x_1748_ = v___x_1742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
                    lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_snd_1740_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_1751_: *mut LeanObject,
    mut v_x_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u64 = 0;
    let mut v___x_1761_: u64 = 0;
    let mut v___x_1762_: u64 = 0;
    let mut v_fold_1763_: u64 = 0;
    let mut v___x_1764_: u64 = 0;
    let mut v___x_1765_: u64 = 0;
    let mut v___x_1766_: u64 = 0;
    let mut v___x_1767_: usize = 0;
    let mut v___x_1768_: usize = 0;
    let mut v___x_1769_: usize = 0;
    let mut v___x_1770_: usize = 0;
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1752_) == 0 {
                    return v_x_1751_;
                } else {
                    v_key_1753_ = lean_ctor_get(v_x_1752_, 0);
                    v_value_1754_ = lean_ctor_get(v_x_1752_, 1);
                    v_tail_1755_ = lean_ctor_get(v_x_1752_, 2);
                    v_isSharedCheck_1778_ = (!lean_is_exclusive(v_x_1752_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1757_ = v_x_1752_;
                        v_isShared_1758_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1755_);
                        lean_inc(v_value_1754_);
                        lean_inc(v_key_1753_);
                        lean_dec(v_x_1752_);
                        v___x_1757_ = lean_box(0);
                        v_isShared_1758_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1759_ = lean_array_get_size(v_x_1751_);
                v___x_1760_ = l_Lean_IR_instHashableVarId_hash(v_key_1753_);
                v___x_1761_ = 32u64;
                v___x_1762_ = lean_uint64_shift_right(v___x_1760_, v___x_1761_);
                v_fold_1763_ = lean_uint64_xor(v___x_1760_, v___x_1762_);
                v___x_1764_ = 16u64;
                v___x_1765_ = lean_uint64_shift_right(v_fold_1763_, v___x_1764_);
                v___x_1766_ = lean_uint64_xor(v_fold_1763_, v___x_1765_);
                v___x_1767_ = lean_uint64_to_usize(v___x_1766_);
                v___x_1768_ = lean_usize_of_nat(v___x_1759_);
                v___x_1769_ = 1usize;
                v___x_1770_ = lean_usize_sub(v___x_1768_, v___x_1769_);
                v___x_1771_ = lean_usize_land(v___x_1767_, v___x_1770_);
                v___x_1772_ = lean_array_uget_borrowed(v_x_1751_, v___x_1771_);
                lean_inc(v___x_1772_);
                if v_isShared_1758_ == 0 {
                    lean_ctor_set(v___x_1757_, 2, v___x_1772_);
                    v___x_1774_ = v___x_1757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_key_1753_);
                    lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_value_1754_);
                    lean_ctor_set(v_reuseFailAlloc_1777_, 2, v___x_1772_);
                    v___x_1774_ = v_reuseFailAlloc_1777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1775_ = lean_array_uset(v_x_1751_, v___x_1771_, v___x_1774_);
                v_x_1751_ = v___x_1775_;
                v_x_1752_ = v_tail_1755_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(
    mut v_i_1779_: *mut LeanObject,
    mut v_source_1780_: *mut LeanObject,
    mut v_target_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v_es_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1782_ = lean_array_get_size(v_source_1780_);
                v___x_1783_ = lean_nat_dec_lt(v_i_1779_, v___x_1782_);
                if v___x_1783_ == 0 {
                    lean_dec_ref(v_source_1780_);
                    lean_dec(v_i_1779_);
                    return v_target_1781_;
                } else {
                    v_es_1784_ = lean_array_fget(v_source_1780_, v_i_1779_);
                    v___x_1785_ = lean_box(0);
                    v_source_1786_ = lean_array_fset(v_source_1780_, v_i_1779_, v___x_1785_);
                    v_target_1787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1781_, v_es_1784_);
                    v___x_1788_ = lean_unsigned_to_nat(1);
                    v___x_1789_ = lean_nat_add(v_i_1779_, v___x_1788_);
                    lean_dec(v_i_1779_);
                    v_i_1779_ = v___x_1789_;
                    v_source_1780_ = v_source_1786_;
                    v_target_1781_ = v_target_1787_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(
    mut v_data_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    v___x_1792_ = lean_array_get_size(v_data_1791_);
    v___x_1793_ = lean_unsigned_to_nat(2);
    v_nbuckets_1794_ = lean_nat_mul(v___x_1792_, v___x_1793_);
    v___x_1795_ = lean_unsigned_to_nat(0);
    v___x_1796_ = lean_box(0);
    v___x_1797_ = lean_mk_array(v_nbuckets_1794_, v___x_1796_);
    v___x_1798_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_1795_, v_data_1791_, v___x_1797_);
    return v___x_1798_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(
    mut v_a_1799_: *mut LeanObject,
    mut v_x_1800_: *mut LeanObject,
) -> u8 {
    let mut v___x_1801_: u8 = 0;
    let mut v_key_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1800_) == 0 {
                    v___x_1801_ = 0;
                    return v___x_1801_;
                } else {
                    v_key_1802_ = lean_ctor_get(v_x_1800_, 0);
                    v_tail_1803_ = lean_ctor_get(v_x_1800_, 2);
                    v___x_1804_ = l_Lean_IR_instBEqVarId_beq(v_key_1802_, v_a_1799_);
                    if v___x_1804_ == 0 {
                        v_x_1800_ = v_tail_1803_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(
    mut v_a_1806_: *mut LeanObject,
    mut v_x_1807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1808_: u8 = 0;
    let mut v_r_1809_: *mut LeanObject = core::ptr::null_mut();
    v_res_1808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_1806_, v_x_1807_);
    lean_dec(v_x_1807_);
    lean_dec(v_a_1806_);
    v_r_1809_ = lean_box((v_res_1808_) as usize);
    return v_r_1809_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(
    mut v_a_1810_: *mut LeanObject,
    mut v_b_1811_: *mut LeanObject,
    mut v_x_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1812_) == 0 {
                    lean_dec(v_b_1811_);
                    lean_dec(v_a_1810_);
                    return v_x_1812_;
                } else {
                    v_key_1813_ = lean_ctor_get(v_x_1812_, 0);
                    v_value_1814_ = lean_ctor_get(v_x_1812_, 1);
                    v_tail_1815_ = lean_ctor_get(v_x_1812_, 2);
                    v_isSharedCheck_1827_ = (!lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1817_ = v_x_1812_;
                        v_isShared_1818_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1815_);
                        lean_inc(v_value_1814_);
                        lean_inc(v_key_1813_);
                        lean_dec(v_x_1812_);
                        v___x_1817_ = lean_box(0);
                        v_isShared_1818_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1819_ = l_Lean_IR_instBEqVarId_beq(v_key_1813_, v_a_1810_);
                if v___x_1819_ == 0 {
                    v___x_1820_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_1810_, v_b_1811_, v_tail_1815_);
                    if v_isShared_1818_ == 0 {
                        lean_ctor_set(v___x_1817_, 2, v___x_1820_);
                        v___x_1822_ = v___x_1817_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_key_1813_);
                        lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_value_1814_);
                        lean_ctor_set(v_reuseFailAlloc_1823_, 2, v___x_1820_);
                        v___x_1822_ = v_reuseFailAlloc_1823_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1814_);
                    lean_dec(v_key_1813_);
                    if v_isShared_1818_ == 0 {
                        lean_ctor_set(v___x_1817_, 1, v_b_1811_);
                        lean_ctor_set(v___x_1817_, 0, v_a_1810_);
                        v___x_1825_ = v___x_1817_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1810_);
                        lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_b_1811_);
                        lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_tail_1815_);
                        v___x_1825_ = v_reuseFailAlloc_1826_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1822_;
            }
            3 => {
                return v___x_1825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(
    mut v_m_1828_: *mut LeanObject,
    mut v_a_1829_: *mut LeanObject,
    mut v_b_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: u64 = 0;
    let mut v___x_1838_: u64 = 0;
    let mut v___x_1839_: u64 = 0;
    let mut v_fold_1840_: u64 = 0;
    let mut v___x_1841_: u64 = 0;
    let mut v___x_1842_: u64 = 0;
    let mut v___x_1843_: u64 = 0;
    let mut v___x_1844_: usize = 0;
    let mut v___x_1845_: usize = 0;
    let mut v___x_1846_: usize = 0;
    let mut v___x_1847_: usize = 0;
    let mut v___x_1848_: usize = 0;
    let mut v_bkt_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v_val_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1831_ = lean_ctor_get(v_m_1828_, 0);
                v_buckets_1832_ = lean_ctor_get(v_m_1828_, 1);
                v_isSharedCheck_1875_ = (!lean_is_exclusive(v_m_1828_)) as u8;
                if v_isSharedCheck_1875_ == 0 {
                    v___x_1834_ = v_m_1828_;
                    v_isShared_1835_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1832_);
                    lean_inc(v_size_1831_);
                    lean_dec(v_m_1828_);
                    v___x_1834_ = lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1836_ = lean_array_get_size(v_buckets_1832_);
                v___x_1837_ = l_Lean_IR_instHashableVarId_hash(v_a_1829_);
                v___x_1838_ = 32u64;
                v___x_1839_ = lean_uint64_shift_right(v___x_1837_, v___x_1838_);
                v_fold_1840_ = lean_uint64_xor(v___x_1837_, v___x_1839_);
                v___x_1841_ = 16u64;
                v___x_1842_ = lean_uint64_shift_right(v_fold_1840_, v___x_1841_);
                v___x_1843_ = lean_uint64_xor(v_fold_1840_, v___x_1842_);
                v___x_1844_ = lean_uint64_to_usize(v___x_1843_);
                v___x_1845_ = lean_usize_of_nat(v___x_1836_);
                v___x_1846_ = 1usize;
                v___x_1847_ = lean_usize_sub(v___x_1845_, v___x_1846_);
                v___x_1848_ = lean_usize_land(v___x_1844_, v___x_1847_);
                v_bkt_1849_ = lean_array_uget_borrowed(v_buckets_1832_, v___x_1848_);
                v___x_1850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_1829_, v_bkt_1849_);
                if v___x_1850_ == 0 {
                    v___x_1851_ = lean_unsigned_to_nat(1);
                    v_size_x27_1852_ = lean_nat_add(v_size_1831_, v___x_1851_);
                    lean_dec(v_size_1831_);
                    lean_inc(v_bkt_1849_);
                    v___x_1853_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1853_, 0, v_a_1829_);
                    lean_ctor_set(v___x_1853_, 1, v_b_1830_);
                    lean_ctor_set(v___x_1853_, 2, v_bkt_1849_);
                    v_buckets_x27_1854_ =
                        lean_array_uset(v_buckets_1832_, v___x_1848_, v___x_1853_);
                    v___x_1855_ = lean_unsigned_to_nat(4);
                    v___x_1856_ = lean_nat_mul(v_size_x27_1852_, v___x_1855_);
                    v___x_1857_ = lean_unsigned_to_nat(3);
                    v___x_1858_ = lean_nat_div(v___x_1856_, v___x_1857_);
                    lean_dec(v___x_1856_);
                    v___x_1859_ = lean_array_get_size(v_buckets_x27_1854_);
                    v___x_1860_ = lean_nat_dec_le(v___x_1858_, v___x_1859_);
                    lean_dec(v___x_1858_);
                    if v___x_1860_ == 0 {
                        v_val_1861_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_1854_);
                        if v_isShared_1835_ == 0 {
                            lean_ctor_set(v___x_1834_, 1, v_val_1861_);
                            lean_ctor_set(v___x_1834_, 0, v_size_x27_1852_);
                            v___x_1863_ = v___x_1834_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_size_x27_1852_);
                            lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_val_1861_);
                            v___x_1863_ = v_reuseFailAlloc_1864_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1835_ == 0 {
                            lean_ctor_set(v___x_1834_, 1, v_buckets_x27_1854_);
                            lean_ctor_set(v___x_1834_, 0, v_size_x27_1852_);
                            v___x_1866_ = v___x_1834_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_size_x27_1852_);
                            lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_buckets_x27_1854_);
                            v___x_1866_ = v_reuseFailAlloc_1867_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1849_);
                    v___x_1868_ = lean_box(0);
                    v_buckets_x27_1869_ =
                        lean_array_uset(v_buckets_1832_, v___x_1848_, v___x_1868_);
                    v___x_1870_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_1829_, v_b_1830_, v_bkt_1849_);
                    v___x_1871_ = lean_array_uset(v_buckets_x27_1869_, v___x_1848_, v___x_1870_);
                    if v_isShared_1835_ == 0 {
                        lean_ctor_set(v___x_1834_, 1, v___x_1871_);
                        v___x_1873_ = v___x_1834_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_size_1831_);
                        lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1871_);
                        v___x_1873_ = v_reuseFailAlloc_1874_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1863_;
            }
            3 => {
                return v___x_1866_;
            }
            4 => {
                return v___x_1873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(
    mut v_as_1876_: *mut LeanObject,
    mut v_i_1877_: usize,
    mut v_stop_1878_: usize,
    mut v_b_1879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1880_: u8 = 0;
    let mut v_fst_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1885_: u8 = 0;
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: usize = 0;
    let mut v___x_1893_: usize = 0;
    let mut v_reuseFailAlloc_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = lean_usize_dec_eq(v_i_1877_, v_stop_1878_);
                if v___x_1880_ == 0 {
                    v_fst_1881_ = lean_ctor_get(v_b_1879_, 0);
                    v_snd_1882_ = lean_ctor_get(v_b_1879_, 1);
                    v_isSharedCheck_1896_ = (!lean_is_exclusive(v_b_1879_)) as u8;
                    if v_isSharedCheck_1896_ == 0 {
                        v___x_1884_ = v_b_1879_;
                        v_isShared_1885_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1882_);
                        lean_inc(v_fst_1881_);
                        lean_dec(v_b_1879_);
                        v___x_1884_ = lean_box(0);
                        v_isShared_1885_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1879_;
                }
            }
            1 => {
                v___x_1886_ = lean_array_uget_borrowed(v_as_1876_, v_i_1877_);
                v_x_1887_ = lean_ctor_get(v___x_1886_, 0);
                v_ty_1888_ = lean_ctor_get(v___x_1886_, 1);
                lean_inc(v_ty_1888_);
                lean_inc(v_x_1887_);
                v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_1881_, v_x_1887_, v_ty_1888_);
                if v_isShared_1885_ == 0 {
                    lean_ctor_set(v___x_1884_, 0, v___x_1889_);
                    v___x_1891_ = v___x_1884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1889_);
                    lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_snd_1882_);
                    v___x_1891_ = v_reuseFailAlloc_1895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1892_ = 1usize;
                v___x_1893_ = lean_usize_add(v_i_1877_, v___x_1892_);
                v_i_1877_ = v___x_1893_;
                v_b_1879_ = v___x_1891_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(
    mut v_as_1897_: *mut LeanObject,
    mut v_i_1898_: *mut LeanObject,
    mut v_stop_1899_: *mut LeanObject,
    mut v_b_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1901_: usize = 0;
    let mut v_stop_boxed_1902_: usize = 0;
    let mut v_res_1903_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1901_ = lean_unbox_usize(v_i_1898_);
    lean_dec(v_i_1898_);
    v_stop_boxed_1902_ = lean_unbox_usize(v_stop_1899_);
    lean_dec(v_stop_1899_);
    v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_1897_, v_i_boxed_1901_, v_stop_boxed_1902_, v_b_1900_);
    lean_dec_ref(v_as_1897_);
    return v_res_1903_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectParams(
    mut v_ps_1904_: *mut LeanObject,
    mut v_s_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u8 = 0;
    v___x_1906_ = lean_unsigned_to_nat(0);
    v___x_1907_ = lean_array_get_size(v_ps_1904_);
    v___x_1908_ = lean_nat_dec_lt(v___x_1906_, v___x_1907_);
    if v___x_1908_ == 0 {
        return v_s_1905_;
    } else {
        let mut v___x_1909_: u8 = 0;
        v___x_1909_ = lean_nat_dec_le(v___x_1907_, v___x_1907_);
        if v___x_1909_ == 0 {
            if v___x_1908_ == 0 {
                return v_s_1905_;
            } else {
                let mut v___x_1910_: usize = 0;
                let mut v___x_1911_: usize = 0;
                let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
                v___x_1910_ = 0usize;
                v___x_1911_ = lean_usize_of_nat(v___x_1907_);
                v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_1904_, v___x_1910_, v___x_1911_, v_s_1905_);
                return v___x_1912_;
            }
        } else {
            let mut v___x_1913_: usize = 0;
            let mut v___x_1914_: usize = 0;
            let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
            v___x_1913_ = 0usize;
            v___x_1914_ = lean_usize_of_nat(v___x_1907_);
            v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_1904_, v___x_1913_, v___x_1914_, v_s_1905_);
            return v___x_1915_;
        }
    }
}
pub unsafe fn l_Lean_IR_CollectMaps_collectParams___boxed(
    mut v_ps_1916_: *mut LeanObject,
    mut v_s_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1918_: *mut LeanObject = core::ptr::null_mut();
    v_res_1918_ = l_Lean_IR_CollectMaps_collectParams(v_ps_1916_, v_s_1917_);
    lean_dec_ref(v_ps_1916_);
    return v_res_1918_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(
    mut v_00_u03b2_1919_: *mut LeanObject,
    mut v_m_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
    mut v_b_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    v___x_1923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_1920_, v_a_1921_, v_b_1922_);
    return v___x_1923_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(
    mut v_00_u03b2_1924_: *mut LeanObject,
    mut v_a_1925_: *mut LeanObject,
    mut v_x_1926_: *mut LeanObject,
) -> u8 {
    let mut v___x_1927_: u8 = 0;
    v___x_1927_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_1925_, v_x_1926_);
    return v___x_1927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(
    mut v_00_u03b2_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
    mut v_x_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1931_: u8 = 0;
    let mut v_r_1932_: *mut LeanObject = core::ptr::null_mut();
    v_res_1931_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_1928_, v_a_1929_, v_x_1930_);
    lean_dec(v_x_1930_);
    lean_dec(v_a_1929_);
    v_r_1932_ = lean_box((v_res_1931_) as usize);
    return v_r_1932_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(
    mut v_00_u03b2_1933_: *mut LeanObject,
    mut v_data_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    v___x_1935_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_1934_);
    return v___x_1935_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(
    mut v_00_u03b2_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
    mut v_b_1938_: *mut LeanObject,
    mut v_x_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    v___x_1940_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_1937_, v_b_1938_, v_x_1939_);
    return v___x_1940_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1941_: *mut LeanObject,
    mut v_i_1942_: *mut LeanObject,
    mut v_source_1943_: *mut LeanObject,
    mut v_target_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    v___x_1945_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_1942_, v_source_1943_, v_target_1944_);
    return v___x_1945_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1946_: *mut LeanObject,
    mut v_x_1947_: *mut LeanObject,
    mut v_x_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1947_, v_x_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectJP(
    mut v_j_1952_: *mut LeanObject,
    mut v_xs_1953_: *mut LeanObject,
    mut v_x_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1955_ = lean_ctor_get(v_x_1954_, 0);
                v_snd_1956_ = lean_ctor_get(v_x_1954_, 1);
                v_isSharedCheck_1966_ = (!lean_is_exclusive(v_x_1954_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v___x_1958_ = v_x_1954_;
                    v_isShared_1959_ = v_isSharedCheck_1966_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1956_);
                    lean_inc(v_fst_1955_);
                    lean_dec(v_x_1954_);
                    v___x_1958_ = lean_box(0);
                    v_isShared_1959_ = v_isSharedCheck_1966_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1960_ = l_Lean_IR_CollectMaps_collectJP___closed__0;
                v___x_1961_ = l_Lean_IR_CollectMaps_collectJP___closed__1;
                v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_1960_,
                    v___x_1961_,
                    v_snd_1956_,
                    v_j_1952_,
                    v_xs_1953_,
                );
                if v_isShared_1959_ == 0 {
                    lean_ctor_set(v___x_1958_, 1, v___x_1962_);
                    v___x_1964_ = v___x_1958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_fst_1955_);
                    lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___x_1962_);
                    v___x_1964_ = v_reuseFailAlloc_1965_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(
    mut v_a_1967_: *mut LeanObject,
    mut v_x_1968_: *mut LeanObject,
) -> u8 {
    let mut v___x_1969_: u8 = 0;
    let mut v_key_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1968_) == 0 {
                    v___x_1969_ = 0;
                    return v___x_1969_;
                } else {
                    v_key_1970_ = lean_ctor_get(v_x_1968_, 0);
                    v_tail_1971_ = lean_ctor_get(v_x_1968_, 2);
                    v___x_1972_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_1970_, v_a_1967_);
                    if v___x_1972_ == 0 {
                        v_x_1968_ = v_tail_1971_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1972_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(
    mut v_a_1974_: *mut LeanObject,
    mut v_x_1975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1976_: u8 = 0;
    let mut v_r_1977_: *mut LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1974_, v_x_1975_);
    lean_dec(v_x_1975_);
    lean_dec(v_a_1974_);
    v_r_1977_ = lean_box((v_res_1976_) as usize);
    return v_r_1977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_1978_: *mut LeanObject,
    mut v_x_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u64 = 0;
    let mut v___x_1988_: u64 = 0;
    let mut v___x_1989_: u64 = 0;
    let mut v_fold_1990_: u64 = 0;
    let mut v___x_1991_: u64 = 0;
    let mut v___x_1992_: u64 = 0;
    let mut v___x_1993_: u64 = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: usize = 0;
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1979_) == 0 {
                    return v_x_1978_;
                } else {
                    v_key_1980_ = lean_ctor_get(v_x_1979_, 0);
                    v_value_1981_ = lean_ctor_get(v_x_1979_, 1);
                    v_tail_1982_ = lean_ctor_get(v_x_1979_, 2);
                    v_isSharedCheck_2005_ = (!lean_is_exclusive(v_x_1979_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_1984_ = v_x_1979_;
                        v_isShared_1985_ = v_isSharedCheck_2005_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1982_);
                        lean_inc(v_value_1981_);
                        lean_inc(v_key_1980_);
                        lean_dec(v_x_1979_);
                        v___x_1984_ = lean_box(0);
                        v_isShared_1985_ = v_isSharedCheck_2005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1986_ = lean_array_get_size(v_x_1978_);
                v___x_1987_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_1980_);
                v___x_1988_ = 32u64;
                v___x_1989_ = lean_uint64_shift_right(v___x_1987_, v___x_1988_);
                v_fold_1990_ = lean_uint64_xor(v___x_1987_, v___x_1989_);
                v___x_1991_ = 16u64;
                v___x_1992_ = lean_uint64_shift_right(v_fold_1990_, v___x_1991_);
                v___x_1993_ = lean_uint64_xor(v_fold_1990_, v___x_1992_);
                v___x_1994_ = lean_uint64_to_usize(v___x_1993_);
                v___x_1995_ = lean_usize_of_nat(v___x_1986_);
                v___x_1996_ = 1usize;
                v___x_1997_ = lean_usize_sub(v___x_1995_, v___x_1996_);
                v___x_1998_ = lean_usize_land(v___x_1994_, v___x_1997_);
                v___x_1999_ = lean_array_uget_borrowed(v_x_1978_, v___x_1998_);
                lean_inc(v___x_1999_);
                if v_isShared_1985_ == 0 {
                    lean_ctor_set(v___x_1984_, 2, v___x_1999_);
                    v___x_2001_ = v___x_1984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_key_1980_);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_value_1981_);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 2, v___x_1999_);
                    v___x_2001_ = v_reuseFailAlloc_2004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2002_ = lean_array_uset(v_x_1978_, v___x_1998_, v___x_2001_);
                v_x_1978_ = v___x_2002_;
                v_x_1979_ = v_tail_1982_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(
    mut v_i_2006_: *mut LeanObject,
    mut v_source_2007_: *mut LeanObject,
    mut v_target_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v_es_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2009_ = lean_array_get_size(v_source_2007_);
                v___x_2010_ = lean_nat_dec_lt(v_i_2006_, v___x_2009_);
                if v___x_2010_ == 0 {
                    lean_dec_ref(v_source_2007_);
                    lean_dec(v_i_2006_);
                    return v_target_2008_;
                } else {
                    v_es_2011_ = lean_array_fget(v_source_2007_, v_i_2006_);
                    v___x_2012_ = lean_box(0);
                    v_source_2013_ = lean_array_fset(v_source_2007_, v_i_2006_, v___x_2012_);
                    v_target_2014_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2008_, v_es_2011_);
                    v___x_2015_ = lean_unsigned_to_nat(1);
                    v___x_2016_ = lean_nat_add(v_i_2006_, v___x_2015_);
                    lean_dec(v_i_2006_);
                    v_i_2006_ = v___x_2016_;
                    v_source_2007_ = v_source_2013_;
                    v_target_2008_ = v_target_2014_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(
    mut v_data_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    v___x_2019_ = lean_array_get_size(v_data_2018_);
    v___x_2020_ = lean_unsigned_to_nat(2);
    v_nbuckets_2021_ = lean_nat_mul(v___x_2019_, v___x_2020_);
    v___x_2022_ = lean_unsigned_to_nat(0);
    v___x_2023_ = lean_box(0);
    v___x_2024_ = lean_mk_array(v_nbuckets_2021_, v___x_2023_);
    v___x_2025_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_2022_, v_data_2018_, v___x_2024_);
    return v___x_2025_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(
    mut v_a_2026_: *mut LeanObject,
    mut v_b_2027_: *mut LeanObject,
    mut v_x_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2028_) == 0 {
                    lean_dec(v_b_2027_);
                    lean_dec(v_a_2026_);
                    return v_x_2028_;
                } else {
                    v_key_2029_ = lean_ctor_get(v_x_2028_, 0);
                    v_value_2030_ = lean_ctor_get(v_x_2028_, 1);
                    v_tail_2031_ = lean_ctor_get(v_x_2028_, 2);
                    v_isSharedCheck_2043_ = (!lean_is_exclusive(v_x_2028_)) as u8;
                    if v_isSharedCheck_2043_ == 0 {
                        v___x_2033_ = v_x_2028_;
                        v_isShared_2034_ = v_isSharedCheck_2043_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2031_);
                        lean_inc(v_value_2030_);
                        lean_inc(v_key_2029_);
                        lean_dec(v_x_2028_);
                        v___x_2033_ = lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2035_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_2029_, v_a_2026_);
                if v___x_2035_ == 0 {
                    v___x_2036_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_2026_, v_b_2027_, v_tail_2031_);
                    if v_isShared_2034_ == 0 {
                        lean_ctor_set(v___x_2033_, 2, v___x_2036_);
                        v___x_2038_ = v___x_2033_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_key_2029_);
                        lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_value_2030_);
                        lean_ctor_set(v_reuseFailAlloc_2039_, 2, v___x_2036_);
                        v___x_2038_ = v_reuseFailAlloc_2039_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2030_);
                    lean_dec(v_key_2029_);
                    if v_isShared_2034_ == 0 {
                        lean_ctor_set(v___x_2033_, 1, v_b_2027_);
                        lean_ctor_set(v___x_2033_, 0, v_a_2026_);
                        v___x_2041_ = v___x_2033_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2026_);
                        lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_b_2027_);
                        lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_tail_2031_);
                        v___x_2041_ = v_reuseFailAlloc_2042_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2038_;
            }
            3 => {
                return v___x_2041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(
    mut v_m_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
    mut v_b_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u64 = 0;
    let mut v___x_2054_: u64 = 0;
    let mut v___x_2055_: u64 = 0;
    let mut v_fold_2056_: u64 = 0;
    let mut v___x_2057_: u64 = 0;
    let mut v___x_2058_: u64 = 0;
    let mut v___x_2059_: u64 = 0;
    let mut v___x_2060_: usize = 0;
    let mut v___x_2061_: usize = 0;
    let mut v___x_2062_: usize = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: usize = 0;
    let mut v_bkt_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v_val_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2047_ = lean_ctor_get(v_m_2044_, 0);
                v_buckets_2048_ = lean_ctor_get(v_m_2044_, 1);
                v_isSharedCheck_2091_ = (!lean_is_exclusive(v_m_2044_)) as u8;
                if v_isSharedCheck_2091_ == 0 {
                    v___x_2050_ = v_m_2044_;
                    v_isShared_2051_ = v_isSharedCheck_2091_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2048_);
                    lean_inc(v_size_2047_);
                    lean_dec(v_m_2044_);
                    v___x_2050_ = lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2091_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2052_ = lean_array_get_size(v_buckets_2048_);
                v___x_2053_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_2045_);
                v___x_2054_ = 32u64;
                v___x_2055_ = lean_uint64_shift_right(v___x_2053_, v___x_2054_);
                v_fold_2056_ = lean_uint64_xor(v___x_2053_, v___x_2055_);
                v___x_2057_ = 16u64;
                v___x_2058_ = lean_uint64_shift_right(v_fold_2056_, v___x_2057_);
                v___x_2059_ = lean_uint64_xor(v_fold_2056_, v___x_2058_);
                v___x_2060_ = lean_uint64_to_usize(v___x_2059_);
                v___x_2061_ = lean_usize_of_nat(v___x_2052_);
                v___x_2062_ = 1usize;
                v___x_2063_ = lean_usize_sub(v___x_2061_, v___x_2062_);
                v___x_2064_ = lean_usize_land(v___x_2060_, v___x_2063_);
                v_bkt_2065_ = lean_array_uget_borrowed(v_buckets_2048_, v___x_2064_);
                v___x_2066_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_2045_, v_bkt_2065_);
                if v___x_2066_ == 0 {
                    v___x_2067_ = lean_unsigned_to_nat(1);
                    v_size_x27_2068_ = lean_nat_add(v_size_2047_, v___x_2067_);
                    lean_dec(v_size_2047_);
                    lean_inc(v_bkt_2065_);
                    v___x_2069_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2069_, 0, v_a_2045_);
                    lean_ctor_set(v___x_2069_, 1, v_b_2046_);
                    lean_ctor_set(v___x_2069_, 2, v_bkt_2065_);
                    v_buckets_x27_2070_ =
                        lean_array_uset(v_buckets_2048_, v___x_2064_, v___x_2069_);
                    v___x_2071_ = lean_unsigned_to_nat(4);
                    v___x_2072_ = lean_nat_mul(v_size_x27_2068_, v___x_2071_);
                    v___x_2073_ = lean_unsigned_to_nat(3);
                    v___x_2074_ = lean_nat_div(v___x_2072_, v___x_2073_);
                    lean_dec(v___x_2072_);
                    v___x_2075_ = lean_array_get_size(v_buckets_x27_2070_);
                    v___x_2076_ = lean_nat_dec_le(v___x_2074_, v___x_2075_);
                    lean_dec(v___x_2074_);
                    if v___x_2076_ == 0 {
                        v_val_2077_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_2070_);
                        if v_isShared_2051_ == 0 {
                            lean_ctor_set(v___x_2050_, 1, v_val_2077_);
                            lean_ctor_set(v___x_2050_, 0, v_size_x27_2068_);
                            v___x_2079_ = v___x_2050_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_size_x27_2068_);
                            lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_val_2077_);
                            v___x_2079_ = v_reuseFailAlloc_2080_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2051_ == 0 {
                            lean_ctor_set(v___x_2050_, 1, v_buckets_x27_2070_);
                            lean_ctor_set(v___x_2050_, 0, v_size_x27_2068_);
                            v___x_2082_ = v___x_2050_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_size_x27_2068_);
                            lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_buckets_x27_2070_);
                            v___x_2082_ = v_reuseFailAlloc_2083_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2065_);
                    v___x_2084_ = lean_box(0);
                    v_buckets_x27_2085_ =
                        lean_array_uset(v_buckets_2048_, v___x_2064_, v___x_2084_);
                    v___x_2086_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_2045_, v_b_2046_, v_bkt_2065_);
                    v___x_2087_ = lean_array_uset(v_buckets_x27_2085_, v___x_2064_, v___x_2086_);
                    if v_isShared_2051_ == 0 {
                        lean_ctor_set(v___x_2050_, 1, v___x_2087_);
                        v___x_2089_ = v___x_2050_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_size_2047_);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2087_);
                        v___x_2089_ = v_reuseFailAlloc_2090_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2079_;
            }
            3 => {
                return v___x_2082_;
            }
            4 => {
                return v___x_2089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CollectMaps_collectFnBody(
    mut v_x_2092_: *mut LeanObject,
    mut v_a_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut v_j_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_cs_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: usize = 0;
    let mut v___x_2131_: usize = 0;
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: usize = 0;
    let mut v___x_2134_: usize = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2092_) {
                0 => {
                    v_x_2094_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2094_);
                    v_ty_2095_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_ty_2095_);
                    v_b_2096_ = lean_ctor_get(v_x_2092_, 3);
                    lean_inc(v_b_2096_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2097_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_2096_, v_a_2093_);
                    v_fst_2098_ = lean_ctor_get(v___x_2097_, 0);
                    v_snd_2099_ = lean_ctor_get(v___x_2097_, 1);
                    v_isSharedCheck_2107_ = (!lean_is_exclusive(v___x_2097_)) as u8;
                    if v_isSharedCheck_2107_ == 0 {
                        v___x_2101_ = v___x_2097_;
                        v_isShared_2102_ = v_isSharedCheck_2107_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2099_);
                        lean_inc(v_fst_2098_);
                        lean_dec(v___x_2097_);
                        v___x_2101_ = lean_box(0);
                        v_isShared_2102_ = v_isSharedCheck_2107_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_j_2108_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_j_2108_);
                    v_xs_2109_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc_ref(v_xs_2109_);
                    v_v_2110_ = lean_ctor_get(v_x_2092_, 2);
                    lean_inc(v_v_2110_);
                    v_b_2111_ = lean_ctor_get(v_x_2092_, 3);
                    lean_inc(v_b_2111_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2112_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_2111_, v_a_2093_);
                    v___x_2113_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_2110_, v___x_2112_);
                    v___x_2114_ = l_Lean_IR_CollectMaps_collectParams(v_xs_2109_, v___x_2113_);
                    v_fst_2115_ = lean_ctor_get(v___x_2114_, 0);
                    v_snd_2116_ = lean_ctor_get(v___x_2114_, 1);
                    v_isSharedCheck_2124_ = (!lean_is_exclusive(v___x_2114_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2118_ = v___x_2114_;
                        v_isShared_2119_ = v_isSharedCheck_2124_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_2116_);
                        lean_inc(v_fst_2115_);
                        lean_dec(v___x_2114_);
                        v___x_2118_ = lean_box(0);
                        v_isShared_2119_ = v_isSharedCheck_2124_;
                        state = 3;
                        continue;
                    }
                }
                9 => {
                    v_cs_2125_ = lean_ctor_get(v_x_2092_, 3);
                    lean_inc_ref(v_cs_2125_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2126_ = lean_unsigned_to_nat(0);
                    v___x_2127_ = lean_array_get_size(v_cs_2125_);
                    v___x_2128_ = lean_nat_dec_lt(v___x_2126_, v___x_2127_);
                    if v___x_2128_ == 0 {
                        lean_dec_ref(v_cs_2125_);
                        return v_a_2093_;
                    } else {
                        v___x_2129_ = lean_nat_dec_le(v___x_2127_, v___x_2127_);
                        if v___x_2129_ == 0 {
                            if v___x_2128_ == 0 {
                                lean_dec_ref(v_cs_2125_);
                                return v_a_2093_;
                            } else {
                                v___x_2130_ = 0usize;
                                v___x_2131_ = lean_usize_of_nat(v___x_2127_);
                                v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_2125_, v___x_2130_, v___x_2131_, v_a_2093_);
                                lean_dec_ref(v_cs_2125_);
                                return v___x_2132_;
                            }
                        } else {
                            v___x_2133_ = 0usize;
                            v___x_2134_ = lean_usize_of_nat(v___x_2127_);
                            v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_2125_, v___x_2133_, v___x_2134_, v_a_2093_);
                            lean_dec_ref(v_cs_2125_);
                            return v___x_2135_;
                        }
                    }
                }
                _ => {
                    v___x_2136_ = l_Lean_IR_FnBody_isTerminal(v_x_2092_);
                    if v___x_2136_ == 0 {
                        v___x_2137_ = l_Lean_IR_FnBody_body(v_x_2092_);
                        lean_dec(v_x_2092_);
                        v_x_2092_ = v___x_2137_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_x_2092_);
                        return v_a_2093_;
                    }
                }
            },
            1 => {
                v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_2098_, v_x_2094_, v_ty_2095_);
                if v_isShared_2102_ == 0 {
                    lean_ctor_set(v___x_2101_, 0, v___x_2103_);
                    v___x_2105_ = v___x_2101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
                    lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_snd_2099_);
                    v___x_2105_ = v_reuseFailAlloc_2106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2105_;
            }
            3 => {
                v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_2116_, v_j_2108_, v_xs_2109_);
                if v_isShared_2119_ == 0 {
                    lean_ctor_set(v___x_2118_, 1, v___x_2120_);
                    v___x_2122_ = v___x_2118_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_fst_2115_);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(
    mut v_as_2139_: *mut LeanObject,
    mut v_i_2140_: usize,
    mut v_stop_2141_: usize,
    mut v_b_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: usize = 0;
    let mut v___x_2148_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2143_ = lean_usize_dec_eq(v_i_2140_, v_stop_2141_);
                if v___x_2143_ == 0 {
                    v___x_2144_ = lean_array_uget_borrowed(v_as_2139_, v_i_2140_);
                    v___x_2145_ = l_Lean_IR_Alt_body(v___x_2144_);
                    v___x_2146_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_2145_, v_b_2142_);
                    v___x_2147_ = 1usize;
                    v___x_2148_ = lean_usize_add(v_i_2140_, v___x_2147_);
                    v_i_2140_ = v___x_2148_;
                    v_b_2142_ = v___x_2146_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2142_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(
    mut v_as_2150_: *mut LeanObject,
    mut v_i_2151_: *mut LeanObject,
    mut v_stop_2152_: *mut LeanObject,
    mut v_b_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2154_: usize = 0;
    let mut v_stop_boxed_2155_: usize = 0;
    let mut v_res_2156_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2154_ = lean_unbox_usize(v_i_2151_);
    lean_dec(v_i_2151_);
    v_stop_boxed_2155_ = lean_unbox_usize(v_stop_2152_);
    lean_dec(v_stop_2152_);
    v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_2150_, v_i_boxed_2154_, v_stop_boxed_2155_, v_b_2153_);
    lean_dec_ref(v_as_2150_);
    return v_res_2156_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(
    mut v_00_u03b2_2157_: *mut LeanObject,
    mut v_m_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
    mut v_b_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_2158_, v_a_2159_, v_b_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(
    mut v_00_u03b2_2162_: *mut LeanObject,
    mut v_a_2163_: *mut LeanObject,
    mut v_x_2164_: *mut LeanObject,
) -> u8 {
    let mut v___x_2165_: u8 = 0;
    v___x_2165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_2163_, v_x_2164_);
    return v___x_2165_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(
    mut v_00_u03b2_2166_: *mut LeanObject,
    mut v_a_2167_: *mut LeanObject,
    mut v_x_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2169_: u8 = 0;
    let mut v_r_2170_: *mut LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_2166_, v_a_2167_, v_x_2168_);
    lean_dec(v_x_2168_);
    lean_dec(v_a_2167_);
    v_r_2170_ = lean_box((v_res_2169_) as usize);
    return v_r_2170_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(
    mut v_00_u03b2_2171_: *mut LeanObject,
    mut v_data_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    v___x_2173_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_2172_);
    return v___x_2173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(
    mut v_00_u03b2_2174_: *mut LeanObject,
    mut v_a_2175_: *mut LeanObject,
    mut v_b_2176_: *mut LeanObject,
    mut v_x_2177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_2175_, v_b_2176_, v_x_2177_);
    return v___x_2178_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2179_: *mut LeanObject,
    mut v_i_2180_: *mut LeanObject,
    mut v_source_2181_: *mut LeanObject,
    mut v_target_2182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    v___x_2183_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_2180_, v_source_2181_, v_target_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2184_: *mut LeanObject,
    mut v_x_2185_: *mut LeanObject,
    mut v_x_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2185_, v_x_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectDecl(
    mut v_x_2188_: *mut LeanObject,
    mut v_a_2189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2188_) == 0 {
        let mut v_xs_2190_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_2191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
        v_xs_2190_ = lean_ctor_get(v_x_2188_, 1);
        lean_inc_ref(v_xs_2190_);
        v_body_2191_ = lean_ctor_get(v_x_2188_, 3);
        lean_inc(v_body_2191_);
        lean_dec_ref_known(v_x_2188_, 5);
        v___x_2192_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_2191_, v_a_2189_);
        v___x_2193_ = l_Lean_IR_CollectMaps_collectParams(v_xs_2190_, v___x_2192_);
        lean_dec_ref(v_xs_2190_);
        return v___x_2193_;
    } else {
        lean_dec_ref(v_x_2188_);
        return v_a_2189_;
    }
}
pub unsafe fn _init_l_Lean_IR_mkVarJPMaps___closed__0() -> *mut LeanObject {
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    v___x_2194_ = lean_box(0);
    v___x_2195_ = lean_unsigned_to_nat(16);
    v___x_2196_ = lean_mk_array(v___x_2195_, v___x_2194_);
    return v___x_2196_;
}
pub unsafe fn _init_l_Lean_IR_mkVarJPMaps___closed__1() -> *mut LeanObject {
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    v___x_2197_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__0_once),
        _init_l_Lean_IR_mkVarJPMaps___closed__0,
    );
    v___x_2198_ = lean_unsigned_to_nat(0);
    v___x_2199_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2199_, 0, v___x_2198_);
    lean_ctor_set(v___x_2199_, 1, v___x_2197_);
    return v___x_2199_;
}
pub unsafe fn _init_l_Lean_IR_mkVarJPMaps___closed__2() -> *mut LeanObject {
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    v___x_2200_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__1_once),
        _init_l_Lean_IR_mkVarJPMaps___closed__1,
    );
    v___x_2201_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2201_, 0, v___x_2200_);
    lean_ctor_set(v___x_2201_, 1, v___x_2200_);
    return v___x_2201_;
}
pub unsafe fn l_Lean_IR_mkVarJPMaps(mut v_d_2202_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__2),
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__2_once),
        _init_l_Lean_IR_mkVarJPMaps___closed__2,
    );
    v___x_2204_ = l_Lean_IR_CollectMaps_collectDecl(v_d_2202_, v___x_2203_);
    return v___x_2204_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_EmitUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_EmitUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_EmitUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_EmitUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_EmitUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_EmitUtil(builtin);
}

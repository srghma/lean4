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
pub static l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0_value:
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
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_collectUsedDecls___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_IR_collectUsedDecls___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_collectUsedDecls___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_collectUsedDecls___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_collectUsedDecls___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_CollectMaps_collectVar___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instBEqVarId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectVar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_CollectMaps_collectVar___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instHashableVarId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectVar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectVar___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_CollectMaps_collectJP___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instBEqJoinPointId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectJP___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectJP___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_CollectMaps_collectJP___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instHashableJoinPointId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_CollectMaps_collectJP___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_CollectMaps_collectJP___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_mkVarJPMaps___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_mkVarJPMaps___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_mkVarJPMaps___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_mkVarJPMaps___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_mkVarJPMaps___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_mkVarJPMaps___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_IR_isTailCallTo(
    mut v_g_1103_: *mut crate::leanh::LeanObject,
    mut v_b_1104_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_b_1104_) == 0 {
        let mut v_e_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_e_1105_ = crate::leanh::lean_ctor_get(v_b_1104_, 2);
        if crate::leanh::lean_obj_tag(v_e_1105_) == 6 {
            let mut v_b_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_1106_ = crate::leanh::lean_ctor_get(v_b_1104_, 3);
            if crate::leanh::lean_obj_tag(v_b_1106_) == 10 {
                let mut v_x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_x_1107_ = crate::leanh::lean_ctor_get(v_b_1106_, 0);
                if crate::leanh::lean_obj_tag(v_x_1107_) == 0 {
                    let mut v_x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_c_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_id_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1111_: u8 = 0;
                    v_x_1108_ = crate::leanh::lean_ctor_get(v_b_1104_, 0);
                    v_c_1109_ = crate::leanh::lean_ctor_get(v_e_1105_, 0);
                    v_id_1110_ = crate::leanh::lean_ctor_get(v_x_1107_, 0);
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
    mut v_g_1117_: *mut crate::leanh::LeanObject,
    mut v_b_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1119_: u8 = 0;
    let mut v_r_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1119_ = l_Lean_IR_isTailCallTo(v_g_1117_, v_b_1118_);
    crate::leanh::lean_dec(v_b_1118_);
    crate::leanh::lean_dec(v_g_1117_);
    v_r_1120_ = crate::leanh::lean_box((v_res_1119_) as usize);
    return v_r_1120_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(
    mut v_modulePrefix_1121_: *mut crate::leanh::LeanObject,
    mut v_as_1122_: *mut crate::leanh::LeanObject,
    mut v_i_1123_: usize,
    mut v_stop_1124_: usize,
) -> u8 {
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irPhases_1128_: u8 = 0;
    let mut v___x_1129_: u8 = 0;
    let mut v___y_1131_: u8 = 0;
    let mut v___x_1132_: usize = 0;
    let mut v___x_1133_: usize = 0;
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: u8 = 0;
    let mut v_module_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1125_ = lean_usize_dec_eq(v_i_1123_, v_stop_1124_);
                if v___x_1125_ == 0 {
                    v___x_1126_ = lean_array_uget_borrowed(v_as_1122_, v_i_1123_);
                    v_toImport_1127_ = crate::leanh::lean_ctor_get(v___x_1126_, 0);
                    v_irPhases_1128_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1126_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_1129_ = 1;
                    v___x_1135_ = 1;
                    v___x_1136_ = l_Lean_instBEqIRPhases_beq(v_irPhases_1128_, v___x_1135_);
                    if v___x_1136_ == 0 {
                        v_module_1137_ = crate::leanh::lean_ctor_get(v_toImport_1127_, 0);
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
    mut v_modulePrefix_1140_: *mut crate::leanh::LeanObject,
    mut v_as_1141_: *mut crate::leanh::LeanObject,
    mut v_i_1142_: *mut crate::leanh::LeanObject,
    mut v_stop_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1144_: usize = 0;
    let mut v_stop_boxed_1145_: usize = 0;
    let mut v_res_1146_: u8 = 0;
    let mut v_r_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1144_ = crate::leanh::lean_unbox_usize(v_i_1142_);
    crate::leanh::lean_dec(v_i_1142_);
    v_stop_boxed_1145_ = crate::leanh::lean_unbox_usize(v_stop_1143_);
    crate::leanh::lean_dec(v_stop_1143_);
    v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_1140_, v_as_1141_, v_i_boxed_1144_, v_stop_boxed_1145_);
    crate::leanh::lean_dec_ref(v_as_1141_);
    crate::leanh::lean_dec(v_modulePrefix_1140_);
    v_r_1147_ = crate::leanh::lean_box((v_res_1146_) as usize);
    return v_r_1147_;
}
pub unsafe fn l_Lean_IR_usesModuleFrom(
    mut v_env_1148_: *mut crate::leanh::LeanObject,
    mut v_modulePrefix_1149_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: u8 = 0;
    v___x_1150_ = l_Lean_Environment_header(v_env_1148_);
    v_modules_1151_ = crate::leanh::lean_ctor_get(v___x_1150_, 3);
    crate::leanh::lean_inc_ref(v_modules_1151_);
    crate::leanh::lean_dec_ref(v___x_1150_);
    v___x_1152_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1153_ = lean_array_get_size(v_modules_1151_);
    v___x_1154_ = lean_nat_dec_lt(v___x_1152_, v___x_1153_);
    if v___x_1154_ == 0 {
        crate::leanh::lean_dec_ref(v_modules_1151_);
        return v___x_1154_;
    } else {
        if v___x_1154_ == 0 {
            crate::leanh::lean_dec_ref(v_modules_1151_);
            return v___x_1154_;
        } else {
            let mut v___x_1155_: usize = 0;
            let mut v___x_1156_: usize = 0;
            let mut v___x_1157_: u8 = 0;
            v___x_1155_ = 0usize;
            v___x_1156_ = lean_usize_of_nat(v___x_1153_);
            v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_1149_, v_modules_1151_, v___x_1155_, v___x_1156_);
            crate::leanh::lean_dec_ref(v_modules_1151_);
            return v___x_1157_;
        }
    }
}
pub unsafe fn l_Lean_IR_usesModuleFrom___boxed(
    mut v_env_1158_: *mut crate::leanh::LeanObject,
    mut v_modulePrefix_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1160_: u8 = 0;
    let mut v_r_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_Lean_IR_usesModuleFrom(v_env_1158_, v_modulePrefix_1159_);
    crate::leanh::lean_dec(v_modulePrefix_1159_);
    crate::leanh::lean_dec_ref(v_env_1158_);
    v_r_1161_ = crate::leanh::lean_box((v_res_1160_) as usize);
    return v_r_1161_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collect___redArg(
    mut v_f_1163_: *mut crate::leanh::LeanObject,
    mut v_a_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_set_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_order_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1169_: u8 = 0;
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_set_1165_ = crate::leanh::lean_ctor_get(v_a_1164_, 0);
                v_order_1166_ = crate::leanh::lean_ctor_get(v_a_1164_, 1);
                v_isSharedCheck_1189_ = (!crate::leanh::lean_is_exclusive(v_a_1164_)) as u8;
                if v_isSharedCheck_1189_ == 0 {
                    v___x_1168_ = v_a_1164_;
                    v_isShared_1169_ = v_isSharedCheck_1189_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_order_1166_);
                    crate::leanh::lean_inc(v_set_1165_);
                    crate::leanh::lean_dec(v_a_1164_);
                    v___x_1168_ = crate::leanh::lean_box(0);
                    v_isShared_1169_ = v_isSharedCheck_1189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1170_ = crate::leanh::lean_box(0);
                v___x_1184_ = l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0;
                crate::leanh::lean_inc(v_set_1165_);
                crate::leanh::lean_inc(v_f_1163_);
                v___x_1185_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(
                    v___x_1184_,
                    v_f_1163_,
                    v_set_1165_,
                );
                if v___x_1185_ == 0 {
                    crate::leanh::lean_inc(v_f_1163_);
                    v___x_1186_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v___x_1184_,
                        v_f_1163_,
                        v___x_1170_,
                        v_set_1165_,
                    );
                    v___x_1187_ = crate::leanh::lean_box((v___x_1185_) as usize);
                    v_fst_1172_ = v___x_1187_;
                    v_snd_1173_ = v___x_1186_;
                    state = 2;
                    continue;
                } else {
                    v___x_1188_ = crate::leanh::lean_box((v___x_1185_) as usize);
                    v_fst_1172_ = v___x_1188_;
                    v_snd_1173_ = v_set_1165_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1174_ = (crate::leanh::lean_unbox(v_fst_1172_) as u8);
                crate::leanh::lean_dec(v_fst_1172_);
                if v___x_1174_ == 0 {
                    v___x_1175_ = lean_array_push(v_order_1166_, v_f_1163_);
                    if v_isShared_1169_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1168_, 1, v___x_1175_);
                        crate::leanh::lean_ctor_set(v___x_1168_, 0, v_snd_1173_);
                        v___x_1177_ = v___x_1168_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_snd_1173_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1175_);
                        v___x_1177_ = v_reuseFailAlloc_1179_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1163_);
                    if v_isShared_1169_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1168_, 0, v_snd_1173_);
                        v___x_1181_ = v___x_1168_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_snd_1173_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_order_1166_);
                        v___x_1181_ = v_reuseFailAlloc_1183_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1178_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1178_, 0, v___x_1170_);
                crate::leanh::lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                return v___x_1178_;
            }
            4 => {
                v___x_1182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1182_, 0, v___x_1170_);
                crate::leanh::lean_ctor_set(v___x_1182_, 1, v___x_1181_);
                return v___x_1182_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collect(
    mut v_f_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_set_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_order_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1197_: u8 = 0;
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: u8 = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_set_1193_ = crate::leanh::lean_ctor_get(v_a_1192_, 0);
                v_order_1194_ = crate::leanh::lean_ctor_get(v_a_1192_, 1);
                v_isSharedCheck_1217_ = (!crate::leanh::lean_is_exclusive(v_a_1192_)) as u8;
                if v_isSharedCheck_1217_ == 0 {
                    v___x_1196_ = v_a_1192_;
                    v_isShared_1197_ = v_isSharedCheck_1217_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_order_1194_);
                    crate::leanh::lean_inc(v_set_1193_);
                    crate::leanh::lean_dec(v_a_1192_);
                    v___x_1196_ = crate::leanh::lean_box(0);
                    v_isShared_1197_ = v_isSharedCheck_1217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1198_ = crate::leanh::lean_box(0);
                v___x_1212_ = l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0;
                crate::leanh::lean_inc(v_set_1193_);
                crate::leanh::lean_inc(v_f_1190_);
                v___x_1213_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(
                    v___x_1212_,
                    v_f_1190_,
                    v_set_1193_,
                );
                if v___x_1213_ == 0 {
                    crate::leanh::lean_inc(v_f_1190_);
                    v___x_1214_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v___x_1212_,
                        v_f_1190_,
                        v___x_1198_,
                        v_set_1193_,
                    );
                    v___x_1215_ = crate::leanh::lean_box((v___x_1213_) as usize);
                    v_fst_1200_ = v___x_1215_;
                    v_snd_1201_ = v___x_1214_;
                    state = 2;
                    continue;
                } else {
                    v___x_1216_ = crate::leanh::lean_box((v___x_1213_) as usize);
                    v_fst_1200_ = v___x_1216_;
                    v_snd_1201_ = v_set_1193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1202_ = (crate::leanh::lean_unbox(v_fst_1200_) as u8);
                crate::leanh::lean_dec(v_fst_1200_);
                if v___x_1202_ == 0 {
                    v___x_1203_ = lean_array_push(v_order_1194_, v_f_1190_);
                    if v_isShared_1197_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1196_, 1, v___x_1203_);
                        crate::leanh::lean_ctor_set(v___x_1196_, 0, v_snd_1201_);
                        v___x_1205_ = v___x_1196_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1207_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_snd_1201_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1203_);
                        v___x_1205_ = v_reuseFailAlloc_1207_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1190_);
                    if v_isShared_1197_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1196_, 0, v_snd_1201_);
                        v___x_1209_ = v___x_1196_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1211_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_snd_1201_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_order_1194_);
                        v___x_1209_ = v_reuseFailAlloc_1211_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1206_, 0, v___x_1198_);
                crate::leanh::lean_ctor_set(v___x_1206_, 1, v___x_1205_);
                return v___x_1206_;
            }
            4 => {
                v___x_1210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1210_, 0, v___x_1198_);
                crate::leanh::lean_ctor_set(v___x_1210_, 1, v___x_1209_);
                return v___x_1210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collect___boxed(
    mut v_f_1218_: *mut crate::leanh::LeanObject,
    mut v_a_1219_: *mut crate::leanh::LeanObject,
    mut v_a_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Lean_IR_CollectUsedDecls_collect(v_f_1218_, v_a_1219_, v_a_1220_);
    crate::leanh::lean_dec_ref(v_a_1219_);
    return v_res_1221_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(
    mut v_k_1222_: *mut crate::leanh::LeanObject,
    mut v_v_1223_: *mut crate::leanh::LeanObject,
    mut v_t_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: u8 = 0;
    let mut v_impl_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1252_: u8 = 0;
    let mut v_size_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1264_: u8 = 0;
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut v_unused_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1304_: u8 = 0;
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut v_unused_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut v_unused_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v_unused_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v_k_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1359_: u8 = 0;
    let mut v_unused_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_unused_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1392_: u8 = 0;
    let mut v_size_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut v_unused_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1442_: u8 = 0;
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_unused_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_unused_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v_k_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1481_: u8 = 0;
    let mut v_unused_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_unused_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_unused_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1224_) == 0 {
                    v_size_1225_ = crate::leanh::lean_ctor_get(v_t_1224_, 0);
                    v_k_1226_ = crate::leanh::lean_ctor_get(v_t_1224_, 1);
                    v_v_1227_ = crate::leanh::lean_ctor_get(v_t_1224_, 2);
                    v_l_1228_ = crate::leanh::lean_ctor_get(v_t_1224_, 3);
                    v_r_1229_ = crate::leanh::lean_ctor_get(v_t_1224_, 4);
                    v_isSharedCheck_1509_ = (!crate::leanh::lean_is_exclusive(v_t_1224_)) as u8;
                    if v_isSharedCheck_1509_ == 0 {
                        v___x_1231_ = v_t_1224_;
                        v_isShared_1232_ = v_isSharedCheck_1509_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1229_);
                        crate::leanh::lean_inc(v_l_1228_);
                        crate::leanh::lean_inc(v_v_1227_);
                        crate::leanh::lean_inc(v_k_1226_);
                        crate::leanh::lean_inc(v_size_1225_);
                        crate::leanh::lean_dec(v_t_1224_);
                        v___x_1231_ = crate::leanh::lean_box(0);
                        v_isShared_1232_ = v_isSharedCheck_1509_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1510_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1511_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
                    crate::leanh::lean_ctor_set(v___x_1511_, 1, v_k_1222_);
                    crate::leanh::lean_ctor_set(v___x_1511_, 2, v_v_1223_);
                    crate::leanh::lean_ctor_set(v___x_1511_, 3, v_t_1224_);
                    crate::leanh::lean_ctor_set(v___x_1511_, 4, v_t_1224_);
                    return v___x_1511_;
                }
            }
            1 => {
                v___x_1233_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1222_, v_k_1226_);
                match v___x_1233_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_1225_);
                        v_impl_1234_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_1222_, v_v_1223_, v_l_1228_);
                        v___x_1235_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_1229_) == 0 {
                            v_size_1236_ = crate::leanh::lean_ctor_get(v_r_1229_, 0);
                            v_size_1237_ = crate::leanh::lean_ctor_get(v_impl_1234_, 0);
                            crate::leanh::lean_inc(v_size_1237_);
                            v_k_1238_ = crate::leanh::lean_ctor_get(v_impl_1234_, 1);
                            crate::leanh::lean_inc(v_k_1238_);
                            v_v_1239_ = crate::leanh::lean_ctor_get(v_impl_1234_, 2);
                            crate::leanh::lean_inc(v_v_1239_);
                            v_l_1240_ = crate::leanh::lean_ctor_get(v_impl_1234_, 3);
                            crate::leanh::lean_inc(v_l_1240_);
                            v_r_1241_ = crate::leanh::lean_ctor_get(v_impl_1234_, 4);
                            crate::leanh::lean_inc(v_r_1241_);
                            v___x_1242_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1243_ = lean_nat_mul(v___x_1242_, v_size_1236_);
                            v___x_1244_ = lean_nat_dec_lt(v___x_1243_, v_size_1237_);
                            crate::leanh::lean_dec(v___x_1243_);
                            if v___x_1244_ == 0 {
                                crate::leanh::lean_dec(v_r_1241_);
                                crate::leanh::lean_dec(v_l_1240_);
                                crate::leanh::lean_dec(v_v_1239_);
                                crate::leanh::lean_dec(v_k_1238_);
                                v___x_1245_ = lean_nat_add(v___x_1235_, v_size_1237_);
                                crate::leanh::lean_dec(v_size_1237_);
                                v___x_1246_ = lean_nat_add(v___x_1245_, v_size_1236_);
                                crate::leanh::lean_dec(v___x_1245_);
                                if v_isShared_1232_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1231_, 3, v_impl_1234_);
                                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1246_);
                                    v___x_1248_ = v___x_1231_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1249_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1249_,
                                        0,
                                        v___x_1246_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1249_,
                                        1,
                                        v_k_1226_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1249_,
                                        2,
                                        v_v_1227_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1249_,
                                        3,
                                        v_impl_1234_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1249_,
                                        4,
                                        v_r_1229_,
                                    );
                                    v___x_1248_ = v_reuseFailAlloc_1249_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1315_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1234_)) as u8;
                                if v_isSharedCheck_1315_ == 0 {
                                    v_unused_1316_ = crate::leanh::lean_ctor_get(v_impl_1234_, 4);
                                    crate::leanh::lean_dec(v_unused_1316_);
                                    v_unused_1317_ = crate::leanh::lean_ctor_get(v_impl_1234_, 3);
                                    crate::leanh::lean_dec(v_unused_1317_);
                                    v_unused_1318_ = crate::leanh::lean_ctor_get(v_impl_1234_, 2);
                                    crate::leanh::lean_dec(v_unused_1318_);
                                    v_unused_1319_ = crate::leanh::lean_ctor_get(v_impl_1234_, 1);
                                    crate::leanh::lean_dec(v_unused_1319_);
                                    v_unused_1320_ = crate::leanh::lean_ctor_get(v_impl_1234_, 0);
                                    crate::leanh::lean_dec(v_unused_1320_);
                                    v___x_1251_ = v_impl_1234_;
                                    v_isShared_1252_ = v_isSharedCheck_1315_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1234_);
                                    v___x_1251_ = crate::leanh::lean_box(0);
                                    v_isShared_1252_ = v_isSharedCheck_1315_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1321_ = crate::leanh::lean_ctor_get(v_impl_1234_, 3);
                            crate::leanh::lean_inc(v_l_1321_);
                            if crate::leanh::lean_obj_tag(v_l_1321_) == 0 {
                                v_r_1322_ = crate::leanh::lean_ctor_get(v_impl_1234_, 4);
                                v_k_1323_ = crate::leanh::lean_ctor_get(v_impl_1234_, 1);
                                v_v_1324_ = crate::leanh::lean_ctor_get(v_impl_1234_, 2);
                                v_isSharedCheck_1335_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1234_)) as u8;
                                if v_isSharedCheck_1335_ == 0 {
                                    v_unused_1336_ = crate::leanh::lean_ctor_get(v_impl_1234_, 3);
                                    crate::leanh::lean_dec(v_unused_1336_);
                                    v_unused_1337_ = crate::leanh::lean_ctor_get(v_impl_1234_, 0);
                                    crate::leanh::lean_dec(v_unused_1337_);
                                    v___x_1326_ = v_impl_1234_;
                                    v_isShared_1327_ = v_isSharedCheck_1335_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1322_);
                                    crate::leanh::lean_inc(v_v_1324_);
                                    crate::leanh::lean_inc(v_k_1323_);
                                    crate::leanh::lean_dec(v_impl_1234_);
                                    v___x_1326_ = crate::leanh::lean_box(0);
                                    v_isShared_1327_ = v_isSharedCheck_1335_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1338_ = crate::leanh::lean_ctor_get(v_impl_1234_, 4);
                                crate::leanh::lean_inc(v_r_1338_);
                                if crate::leanh::lean_obj_tag(v_r_1338_) == 0 {
                                    v_k_1339_ = crate::leanh::lean_ctor_get(v_impl_1234_, 1);
                                    v_v_1340_ = crate::leanh::lean_ctor_get(v_impl_1234_, 2);
                                    v_isSharedCheck_1363_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1234_)) as u8;
                                    if v_isSharedCheck_1363_ == 0 {
                                        v_unused_1364_ =
                                            crate::leanh::lean_ctor_get(v_impl_1234_, 4);
                                        crate::leanh::lean_dec(v_unused_1364_);
                                        v_unused_1365_ =
                                            crate::leanh::lean_ctor_get(v_impl_1234_, 3);
                                        crate::leanh::lean_dec(v_unused_1365_);
                                        v_unused_1366_ =
                                            crate::leanh::lean_ctor_get(v_impl_1234_, 0);
                                        crate::leanh::lean_dec(v_unused_1366_);
                                        v___x_1342_ = v_impl_1234_;
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1340_);
                                        crate::leanh::lean_inc(v_k_1339_);
                                        crate::leanh::lean_dec(v_impl_1234_);
                                        v___x_1342_ = crate::leanh::lean_box(0);
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1367_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1232_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1231_, 4, v_r_1338_);
                                        crate::leanh::lean_ctor_set(v___x_1231_, 3, v_impl_1234_);
                                        crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1367_);
                                        v___x_1369_ = v___x_1231_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1370_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1370_,
                                            0,
                                            v___x_1367_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1370_,
                                            1,
                                            v_k_1226_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1370_,
                                            2,
                                            v_v_1227_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1370_,
                                            3,
                                            v_impl_1234_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1370_,
                                            4,
                                            v_r_1338_,
                                        );
                                        v___x_1369_ = v_reuseFailAlloc_1370_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_1227_);
                        crate::leanh::lean_dec(v_k_1226_);
                        if v_isShared_1232_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1231_, 2, v_v_1223_);
                            crate::leanh::lean_ctor_set(v___x_1231_, 1, v_k_1222_);
                            v___x_1372_ = v___x_1231_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1373_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_size_1225_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1222_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1223_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_l_1228_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1229_);
                            v___x_1372_ = v_reuseFailAlloc_1373_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_1225_);
                        v_impl_1374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_1222_, v_v_1223_, v_r_1229_);
                        v___x_1375_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1228_) == 0 {
                            v_size_1376_ = crate::leanh::lean_ctor_get(v_l_1228_, 0);
                            v_size_1377_ = crate::leanh::lean_ctor_get(v_impl_1374_, 0);
                            crate::leanh::lean_inc(v_size_1377_);
                            v_k_1378_ = crate::leanh::lean_ctor_get(v_impl_1374_, 1);
                            crate::leanh::lean_inc(v_k_1378_);
                            v_v_1379_ = crate::leanh::lean_ctor_get(v_impl_1374_, 2);
                            crate::leanh::lean_inc(v_v_1379_);
                            v_l_1380_ = crate::leanh::lean_ctor_get(v_impl_1374_, 3);
                            crate::leanh::lean_inc(v_l_1380_);
                            v_r_1381_ = crate::leanh::lean_ctor_get(v_impl_1374_, 4);
                            crate::leanh::lean_inc(v_r_1381_);
                            v___x_1382_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1383_ = lean_nat_mul(v___x_1382_, v_size_1376_);
                            v___x_1384_ = lean_nat_dec_lt(v___x_1383_, v_size_1377_);
                            crate::leanh::lean_dec(v___x_1383_);
                            if v___x_1384_ == 0 {
                                crate::leanh::lean_dec(v_r_1381_);
                                crate::leanh::lean_dec(v_l_1380_);
                                crate::leanh::lean_dec(v_v_1379_);
                                crate::leanh::lean_dec(v_k_1378_);
                                v___x_1385_ = lean_nat_add(v___x_1375_, v_size_1376_);
                                v___x_1386_ = lean_nat_add(v___x_1385_, v_size_1377_);
                                crate::leanh::lean_dec(v_size_1377_);
                                crate::leanh::lean_dec(v___x_1385_);
                                if v_isShared_1232_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1231_, 4, v_impl_1374_);
                                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1386_);
                                    v___x_1388_ = v___x_1231_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1389_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1389_,
                                        0,
                                        v___x_1386_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1389_,
                                        1,
                                        v_k_1226_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1389_,
                                        2,
                                        v_v_1227_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1389_,
                                        3,
                                        v_l_1228_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1389_,
                                        4,
                                        v_impl_1374_,
                                    );
                                    v___x_1388_ = v_reuseFailAlloc_1389_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1453_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1374_)) as u8;
                                if v_isSharedCheck_1453_ == 0 {
                                    v_unused_1454_ = crate::leanh::lean_ctor_get(v_impl_1374_, 4);
                                    crate::leanh::lean_dec(v_unused_1454_);
                                    v_unused_1455_ = crate::leanh::lean_ctor_get(v_impl_1374_, 3);
                                    crate::leanh::lean_dec(v_unused_1455_);
                                    v_unused_1456_ = crate::leanh::lean_ctor_get(v_impl_1374_, 2);
                                    crate::leanh::lean_dec(v_unused_1456_);
                                    v_unused_1457_ = crate::leanh::lean_ctor_get(v_impl_1374_, 1);
                                    crate::leanh::lean_dec(v_unused_1457_);
                                    v_unused_1458_ = crate::leanh::lean_ctor_get(v_impl_1374_, 0);
                                    crate::leanh::lean_dec(v_unused_1458_);
                                    v___x_1391_ = v_impl_1374_;
                                    v_isShared_1392_ = v_isSharedCheck_1453_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1374_);
                                    v___x_1391_ = crate::leanh::lean_box(0);
                                    v_isShared_1392_ = v_isSharedCheck_1453_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1459_ = crate::leanh::lean_ctor_get(v_impl_1374_, 3);
                            crate::leanh::lean_inc(v_l_1459_);
                            if crate::leanh::lean_obj_tag(v_l_1459_) == 0 {
                                v_r_1460_ = crate::leanh::lean_ctor_get(v_impl_1374_, 4);
                                v_k_1461_ = crate::leanh::lean_ctor_get(v_impl_1374_, 1);
                                v_v_1462_ = crate::leanh::lean_ctor_get(v_impl_1374_, 2);
                                v_isSharedCheck_1485_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1374_)) as u8;
                                if v_isSharedCheck_1485_ == 0 {
                                    v_unused_1486_ = crate::leanh::lean_ctor_get(v_impl_1374_, 3);
                                    crate::leanh::lean_dec(v_unused_1486_);
                                    v_unused_1487_ = crate::leanh::lean_ctor_get(v_impl_1374_, 0);
                                    crate::leanh::lean_dec(v_unused_1487_);
                                    v___x_1464_ = v_impl_1374_;
                                    v_isShared_1465_ = v_isSharedCheck_1485_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1460_);
                                    crate::leanh::lean_inc(v_v_1462_);
                                    crate::leanh::lean_inc(v_k_1461_);
                                    crate::leanh::lean_dec(v_impl_1374_);
                                    v___x_1464_ = crate::leanh::lean_box(0);
                                    v_isShared_1465_ = v_isSharedCheck_1485_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1488_ = crate::leanh::lean_ctor_get(v_impl_1374_, 4);
                                crate::leanh::lean_inc(v_r_1488_);
                                if crate::leanh::lean_obj_tag(v_r_1488_) == 0 {
                                    v_k_1489_ = crate::leanh::lean_ctor_get(v_impl_1374_, 1);
                                    v_v_1490_ = crate::leanh::lean_ctor_get(v_impl_1374_, 2);
                                    v_isSharedCheck_1501_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1374_)) as u8;
                                    if v_isSharedCheck_1501_ == 0 {
                                        v_unused_1502_ =
                                            crate::leanh::lean_ctor_get(v_impl_1374_, 4);
                                        crate::leanh::lean_dec(v_unused_1502_);
                                        v_unused_1503_ =
                                            crate::leanh::lean_ctor_get(v_impl_1374_, 3);
                                        crate::leanh::lean_dec(v_unused_1503_);
                                        v_unused_1504_ =
                                            crate::leanh::lean_ctor_get(v_impl_1374_, 0);
                                        crate::leanh::lean_dec(v_unused_1504_);
                                        v___x_1492_ = v_impl_1374_;
                                        v_isShared_1493_ = v_isSharedCheck_1501_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1490_);
                                        crate::leanh::lean_inc(v_k_1489_);
                                        crate::leanh::lean_dec(v_impl_1374_);
                                        v___x_1492_ = crate::leanh::lean_box(0);
                                        v_isShared_1493_ = v_isSharedCheck_1501_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1505_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1232_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1231_, 4, v_impl_1374_);
                                        crate::leanh::lean_ctor_set(v___x_1231_, 3, v_r_1488_);
                                        crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1505_);
                                        v___x_1507_ = v___x_1231_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1508_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1508_,
                                            0,
                                            v___x_1505_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1508_,
                                            1,
                                            v_k_1226_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1508_,
                                            2,
                                            v_v_1227_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1508_,
                                            3,
                                            v_r_1488_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1508_,
                                            4,
                                            v_impl_1374_,
                                        );
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
                v_size_1253_ = crate::leanh::lean_ctor_get(v_l_1240_, 0);
                v_size_1254_ = crate::leanh::lean_ctor_get(v_r_1241_, 0);
                v_k_1255_ = crate::leanh::lean_ctor_get(v_r_1241_, 1);
                v_v_1256_ = crate::leanh::lean_ctor_get(v_r_1241_, 2);
                v_l_1257_ = crate::leanh::lean_ctor_get(v_r_1241_, 3);
                v_r_1258_ = crate::leanh::lean_ctor_get(v_r_1241_, 4);
                v___x_1259_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1260_ = lean_nat_mul(v___x_1259_, v_size_1253_);
                v___x_1261_ = lean_nat_dec_lt(v_size_1254_, v___x_1260_);
                crate::leanh::lean_dec(v___x_1260_);
                if v___x_1261_ == 0 {
                    crate::leanh::lean_inc(v_r_1258_);
                    crate::leanh::lean_inc(v_l_1257_);
                    crate::leanh::lean_inc(v_v_1256_);
                    crate::leanh::lean_inc(v_k_1255_);
                    v_isSharedCheck_1290_ = (!crate::leanh::lean_is_exclusive(v_r_1241_)) as u8;
                    if v_isSharedCheck_1290_ == 0 {
                        v_unused_1291_ = crate::leanh::lean_ctor_get(v_r_1241_, 4);
                        crate::leanh::lean_dec(v_unused_1291_);
                        v_unused_1292_ = crate::leanh::lean_ctor_get(v_r_1241_, 3);
                        crate::leanh::lean_dec(v_unused_1292_);
                        v_unused_1293_ = crate::leanh::lean_ctor_get(v_r_1241_, 2);
                        crate::leanh::lean_dec(v_unused_1293_);
                        v_unused_1294_ = crate::leanh::lean_ctor_get(v_r_1241_, 1);
                        crate::leanh::lean_dec(v_unused_1294_);
                        v_unused_1295_ = crate::leanh::lean_ctor_get(v_r_1241_, 0);
                        crate::leanh::lean_dec(v_unused_1295_);
                        v___x_1263_ = v_r_1241_;
                        v_isShared_1264_ = v_isSharedCheck_1290_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1241_);
                        v___x_1263_ = crate::leanh::lean_box(0);
                        v_isShared_1264_ = v_isSharedCheck_1290_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1231_);
                    v___x_1296_ = lean_nat_add(v___x_1235_, v_size_1237_);
                    crate::leanh::lean_dec(v_size_1237_);
                    v___x_1297_ = lean_nat_add(v___x_1296_, v_size_1236_);
                    crate::leanh::lean_dec(v___x_1296_);
                    v___x_1298_ = lean_nat_add(v___x_1235_, v_size_1236_);
                    v___x_1299_ = lean_nat_add(v___x_1298_, v_size_1254_);
                    crate::leanh::lean_dec(v___x_1298_);
                    crate::leanh::lean_inc_ref(v_r_1229_);
                    if v_isShared_1252_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1251_, 4, v_r_1229_);
                        crate::leanh::lean_ctor_set(v___x_1251_, 3, v_r_1241_);
                        crate::leanh::lean_ctor_set(v___x_1251_, 2, v_v_1227_);
                        crate::leanh::lean_ctor_set(v___x_1251_, 1, v_k_1226_);
                        crate::leanh::lean_ctor_set(v___x_1251_, 0, v___x_1299_);
                        v___x_1301_ = v___x_1251_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1299_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_k_1226_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_v_1227_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_r_1241_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_r_1229_);
                        v___x_1301_ = v_reuseFailAlloc_1314_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1265_ = lean_nat_add(v___x_1235_, v_size_1237_);
                crate::leanh::lean_dec(v_size_1237_);
                v___x_1266_ = lean_nat_add(v___x_1265_, v_size_1236_);
                crate::leanh::lean_dec(v___x_1265_);
                v___x_1278_ = lean_nat_add(v___x_1235_, v_size_1253_);
                if crate::leanh::lean_obj_tag(v_l_1257_) == 0 {
                    v_size_1288_ = crate::leanh::lean_ctor_get(v_l_1257_, 0);
                    crate::leanh::lean_inc(v_size_1288_);
                    v___y_1280_ = v_size_1288_;
                    state = 8;
                    continue;
                } else {
                    v___x_1289_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1280_ = v___x_1289_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1271_ = lean_nat_add(v___y_1268_, v___y_1270_);
                crate::leanh::lean_dec(v___y_1270_);
                crate::leanh::lean_dec(v___y_1268_);
                if v_isShared_1264_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1263_, 4, v_r_1229_);
                    crate::leanh::lean_ctor_set(v___x_1263_, 3, v_r_1258_);
                    crate::leanh::lean_ctor_set(v___x_1263_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v___x_1263_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v___x_1263_, 0, v___x_1271_);
                    v___x_1273_ = v___x_1263_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_r_1258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_r_1229_);
                    v___x_1273_ = v_reuseFailAlloc_1277_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1252_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1251_, 4, v___x_1273_);
                    crate::leanh::lean_ctor_set(v___x_1251_, 3, v___y_1269_);
                    crate::leanh::lean_ctor_set(v___x_1251_, 2, v_v_1256_);
                    crate::leanh::lean_ctor_set(v___x_1251_, 1, v_k_1255_);
                    crate::leanh::lean_ctor_set(v___x_1251_, 0, v___x_1266_);
                    v___x_1275_ = v___x_1251_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_k_1255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_v_1256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___y_1269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___x_1273_);
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
                crate::leanh::lean_dec(v___y_1280_);
                crate::leanh::lean_dec(v___x_1278_);
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 4, v_l_1257_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 3, v_l_1240_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 2, v_v_1239_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 1, v_k_1238_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1281_);
                    v___x_1283_ = v___x_1231_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_l_1240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_l_1257_);
                    v___x_1283_ = v_reuseFailAlloc_1287_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1284_ = lean_nat_add(v___x_1235_, v_size_1236_);
                if crate::leanh::lean_obj_tag(v_r_1258_) == 0 {
                    v_size_1285_ = crate::leanh::lean_ctor_get(v_r_1258_, 0);
                    crate::leanh::lean_inc(v_size_1285_);
                    v___y_1268_ = v___x_1284_;
                    v___y_1269_ = v___x_1283_;
                    v___y_1270_ = v_size_1285_;
                    state = 5;
                    continue;
                } else {
                    v___x_1286_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1268_ = v___x_1284_;
                    v___y_1269_ = v___x_1283_;
                    v___y_1270_ = v___x_1286_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1308_ = (!crate::leanh::lean_is_exclusive(v_r_1229_)) as u8;
                if v_isSharedCheck_1308_ == 0 {
                    v_unused_1309_ = crate::leanh::lean_ctor_get(v_r_1229_, 4);
                    crate::leanh::lean_dec(v_unused_1309_);
                    v_unused_1310_ = crate::leanh::lean_ctor_get(v_r_1229_, 3);
                    crate::leanh::lean_dec(v_unused_1310_);
                    v_unused_1311_ = crate::leanh::lean_ctor_get(v_r_1229_, 2);
                    crate::leanh::lean_dec(v_unused_1311_);
                    v_unused_1312_ = crate::leanh::lean_ctor_get(v_r_1229_, 1);
                    crate::leanh::lean_dec(v_unused_1312_);
                    v_unused_1313_ = crate::leanh::lean_ctor_get(v_r_1229_, 0);
                    crate::leanh::lean_dec(v_unused_1313_);
                    v___x_1303_ = v_r_1229_;
                    v_isShared_1304_ = v_isSharedCheck_1308_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1229_);
                    v___x_1303_ = crate::leanh::lean_box(0);
                    v_isShared_1304_ = v_isSharedCheck_1308_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1304_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1303_, 4, v___x_1301_);
                    crate::leanh::lean_ctor_set(v___x_1303_, 3, v_l_1240_);
                    crate::leanh::lean_ctor_set(v___x_1303_, 2, v_v_1239_);
                    crate::leanh::lean_ctor_set(v___x_1303_, 1, v_k_1238_);
                    crate::leanh::lean_ctor_set(v___x_1303_, 0, v___x_1297_);
                    v___x_1306_ = v___x_1303_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1307_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_k_1238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_v_1239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_l_1240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 4, v___x_1301_);
                    v___x_1306_ = v_reuseFailAlloc_1307_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1306_;
            }
            13 => {
                v___x_1328_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_1322_);
                if v_isShared_1327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1326_, 3, v_r_1322_);
                    crate::leanh::lean_ctor_set(v___x_1326_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v___x_1326_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1235_);
                    v___x_1330_ = v___x_1326_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_r_1322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_r_1322_);
                    v___x_1330_ = v_reuseFailAlloc_1334_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 4, v___x_1330_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 3, v_l_1321_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 2, v_v_1324_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 1, v_k_1323_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1328_);
                    v___x_1332_ = v___x_1231_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_k_1323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_v_1324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_l_1321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 4, v___x_1330_);
                    v___x_1332_ = v_reuseFailAlloc_1333_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1332_;
            }
            16 => {
                v_k_1344_ = crate::leanh::lean_ctor_get(v_r_1338_, 1);
                v_v_1345_ = crate::leanh::lean_ctor_get(v_r_1338_, 2);
                v_isSharedCheck_1359_ = (!crate::leanh::lean_is_exclusive(v_r_1338_)) as u8;
                if v_isSharedCheck_1359_ == 0 {
                    v_unused_1360_ = crate::leanh::lean_ctor_get(v_r_1338_, 4);
                    crate::leanh::lean_dec(v_unused_1360_);
                    v_unused_1361_ = crate::leanh::lean_ctor_get(v_r_1338_, 3);
                    crate::leanh::lean_dec(v_unused_1361_);
                    v_unused_1362_ = crate::leanh::lean_ctor_get(v_r_1338_, 0);
                    crate::leanh::lean_dec(v_unused_1362_);
                    v___x_1347_ = v_r_1338_;
                    v_isShared_1348_ = v_isSharedCheck_1359_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1345_);
                    crate::leanh::lean_inc(v_k_1344_);
                    crate::leanh::lean_dec(v_r_1338_);
                    v___x_1347_ = crate::leanh::lean_box(0);
                    v_isShared_1348_ = v_isSharedCheck_1359_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1349_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1347_, 4, v_l_1321_);
                    crate::leanh::lean_ctor_set(v___x_1347_, 3, v_l_1321_);
                    crate::leanh::lean_ctor_set(v___x_1347_, 2, v_v_1340_);
                    crate::leanh::lean_ctor_set(v___x_1347_, 1, v_k_1339_);
                    crate::leanh::lean_ctor_set(v___x_1347_, 0, v___x_1235_);
                    v___x_1351_ = v___x_1347_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1358_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_k_1339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_v_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_l_1321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_l_1321_);
                    v___x_1351_ = v_reuseFailAlloc_1358_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1343_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1342_, 4, v_l_1321_);
                    crate::leanh::lean_ctor_set(v___x_1342_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v___x_1342_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v___x_1342_, 0, v___x_1235_);
                    v___x_1353_ = v___x_1342_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1357_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_l_1321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_l_1321_);
                    v___x_1353_ = v_reuseFailAlloc_1357_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 4, v___x_1353_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 3, v___x_1351_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 2, v_v_1345_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 1, v_k_1344_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1349_);
                    v___x_1355_ = v___x_1231_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 3, v___x_1351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 4, v___x_1353_);
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
                v_size_1393_ = crate::leanh::lean_ctor_get(v_l_1380_, 0);
                v_k_1394_ = crate::leanh::lean_ctor_get(v_l_1380_, 1);
                v_v_1395_ = crate::leanh::lean_ctor_get(v_l_1380_, 2);
                v_l_1396_ = crate::leanh::lean_ctor_get(v_l_1380_, 3);
                v_r_1397_ = crate::leanh::lean_ctor_get(v_l_1380_, 4);
                v_size_1398_ = crate::leanh::lean_ctor_get(v_r_1381_, 0);
                v___x_1399_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1400_ = lean_nat_mul(v___x_1399_, v_size_1398_);
                v___x_1401_ = lean_nat_dec_lt(v_size_1393_, v___x_1400_);
                crate::leanh::lean_dec(v___x_1400_);
                if v___x_1401_ == 0 {
                    crate::leanh::lean_inc(v_r_1397_);
                    crate::leanh::lean_inc(v_l_1396_);
                    crate::leanh::lean_inc(v_v_1395_);
                    crate::leanh::lean_inc(v_k_1394_);
                    v_isSharedCheck_1429_ = (!crate::leanh::lean_is_exclusive(v_l_1380_)) as u8;
                    if v_isSharedCheck_1429_ == 0 {
                        v_unused_1430_ = crate::leanh::lean_ctor_get(v_l_1380_, 4);
                        crate::leanh::lean_dec(v_unused_1430_);
                        v_unused_1431_ = crate::leanh::lean_ctor_get(v_l_1380_, 3);
                        crate::leanh::lean_dec(v_unused_1431_);
                        v_unused_1432_ = crate::leanh::lean_ctor_get(v_l_1380_, 2);
                        crate::leanh::lean_dec(v_unused_1432_);
                        v_unused_1433_ = crate::leanh::lean_ctor_get(v_l_1380_, 1);
                        crate::leanh::lean_dec(v_unused_1433_);
                        v_unused_1434_ = crate::leanh::lean_ctor_get(v_l_1380_, 0);
                        crate::leanh::lean_dec(v_unused_1434_);
                        v___x_1403_ = v_l_1380_;
                        v_isShared_1404_ = v_isSharedCheck_1429_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1380_);
                        v___x_1403_ = crate::leanh::lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1429_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1231_);
                    v___x_1435_ = lean_nat_add(v___x_1375_, v_size_1376_);
                    v___x_1436_ = lean_nat_add(v___x_1435_, v_size_1377_);
                    crate::leanh::lean_dec(v_size_1377_);
                    v___x_1437_ = lean_nat_add(v___x_1435_, v_size_1393_);
                    crate::leanh::lean_dec(v___x_1435_);
                    crate::leanh::lean_inc_ref(v_l_1228_);
                    if v_isShared_1392_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1391_, 4, v_l_1380_);
                        crate::leanh::lean_ctor_set(v___x_1391_, 3, v_l_1228_);
                        crate::leanh::lean_ctor_set(v___x_1391_, 2, v_v_1227_);
                        crate::leanh::lean_ctor_set(v___x_1391_, 1, v_k_1226_);
                        crate::leanh::lean_ctor_set(v___x_1391_, 0, v___x_1437_);
                        v___x_1439_ = v___x_1391_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1437_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1226_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1227_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_l_1228_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_l_1380_);
                        v___x_1439_ = v_reuseFailAlloc_1452_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1405_ = lean_nat_add(v___x_1375_, v_size_1376_);
                v___x_1406_ = lean_nat_add(v___x_1405_, v_size_1377_);
                crate::leanh::lean_dec(v_size_1377_);
                if crate::leanh::lean_obj_tag(v_l_1396_) == 0 {
                    v_size_1427_ = crate::leanh::lean_ctor_get(v_l_1396_, 0);
                    crate::leanh::lean_inc(v_size_1427_);
                    v___y_1419_ = v_size_1427_;
                    state = 29;
                    continue;
                } else {
                    v___x_1428_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1419_ = v___x_1428_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1411_ = lean_nat_add(v___y_1409_, v___y_1410_);
                crate::leanh::lean_dec(v___y_1410_);
                crate::leanh::lean_dec(v___y_1409_);
                if v_isShared_1404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1403_, 4, v_r_1381_);
                    crate::leanh::lean_ctor_set(v___x_1403_, 3, v_r_1397_);
                    crate::leanh::lean_ctor_set(v___x_1403_, 2, v_v_1379_);
                    crate::leanh::lean_ctor_set(v___x_1403_, 1, v_k_1378_);
                    crate::leanh::lean_ctor_set(v___x_1403_, 0, v___x_1411_);
                    v___x_1413_ = v___x_1403_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_r_1397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_r_1381_);
                    v___x_1413_ = v_reuseFailAlloc_1417_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1391_, 4, v___x_1413_);
                    crate::leanh::lean_ctor_set(v___x_1391_, 3, v___y_1408_);
                    crate::leanh::lean_ctor_set(v___x_1391_, 2, v_v_1395_);
                    crate::leanh::lean_ctor_set(v___x_1391_, 1, v_k_1394_);
                    crate::leanh::lean_ctor_set(v___x_1391_, 0, v___x_1406_);
                    v___x_1415_ = v___x_1391_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___y_1408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 4, v___x_1413_);
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
                crate::leanh::lean_dec(v___y_1419_);
                crate::leanh::lean_dec(v___x_1405_);
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 4, v_l_1396_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1231_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1426_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_l_1228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_l_1396_);
                    v___x_1422_ = v_reuseFailAlloc_1426_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1423_ = lean_nat_add(v___x_1375_, v_size_1398_);
                if crate::leanh::lean_obj_tag(v_r_1397_) == 0 {
                    v_size_1424_ = crate::leanh::lean_ctor_get(v_r_1397_, 0);
                    crate::leanh::lean_inc(v_size_1424_);
                    v___y_1408_ = v___x_1422_;
                    v___y_1409_ = v___x_1423_;
                    v___y_1410_ = v_size_1424_;
                    state = 26;
                    continue;
                } else {
                    v___x_1425_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1408_ = v___x_1422_;
                    v___y_1409_ = v___x_1423_;
                    v___y_1410_ = v___x_1425_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1446_ = (!crate::leanh::lean_is_exclusive(v_l_1228_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v_unused_1447_ = crate::leanh::lean_ctor_get(v_l_1228_, 4);
                    crate::leanh::lean_dec(v_unused_1447_);
                    v_unused_1448_ = crate::leanh::lean_ctor_get(v_l_1228_, 3);
                    crate::leanh::lean_dec(v_unused_1448_);
                    v_unused_1449_ = crate::leanh::lean_ctor_get(v_l_1228_, 2);
                    crate::leanh::lean_dec(v_unused_1449_);
                    v_unused_1450_ = crate::leanh::lean_ctor_get(v_l_1228_, 1);
                    crate::leanh::lean_dec(v_unused_1450_);
                    v_unused_1451_ = crate::leanh::lean_ctor_get(v_l_1228_, 0);
                    crate::leanh::lean_dec(v_unused_1451_);
                    v___x_1441_ = v_l_1228_;
                    v_isShared_1442_ = v_isSharedCheck_1446_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1228_);
                    v___x_1441_ = crate::leanh::lean_box(0);
                    v_isShared_1442_ = v_isSharedCheck_1446_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1442_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1441_, 4, v_r_1381_);
                    crate::leanh::lean_ctor_set(v___x_1441_, 3, v___x_1439_);
                    crate::leanh::lean_ctor_set(v___x_1441_, 2, v_v_1379_);
                    crate::leanh::lean_ctor_set(v___x_1441_, 1, v_k_1378_);
                    crate::leanh::lean_ctor_set(v___x_1441_, 0, v___x_1436_);
                    v___x_1444_ = v___x_1441_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 3, v___x_1439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1381_);
                    v___x_1444_ = v_reuseFailAlloc_1445_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1444_;
            }
            34 => {
                v_k_1466_ = crate::leanh::lean_ctor_get(v_l_1459_, 1);
                v_v_1467_ = crate::leanh::lean_ctor_get(v_l_1459_, 2);
                v_isSharedCheck_1481_ = (!crate::leanh::lean_is_exclusive(v_l_1459_)) as u8;
                if v_isSharedCheck_1481_ == 0 {
                    v_unused_1482_ = crate::leanh::lean_ctor_get(v_l_1459_, 4);
                    crate::leanh::lean_dec(v_unused_1482_);
                    v_unused_1483_ = crate::leanh::lean_ctor_get(v_l_1459_, 3);
                    crate::leanh::lean_dec(v_unused_1483_);
                    v_unused_1484_ = crate::leanh::lean_ctor_get(v_l_1459_, 0);
                    crate::leanh::lean_dec(v_unused_1484_);
                    v___x_1469_ = v_l_1459_;
                    v_isShared_1470_ = v_isSharedCheck_1481_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1467_);
                    crate::leanh::lean_inc(v_k_1466_);
                    crate::leanh::lean_dec(v_l_1459_);
                    v___x_1469_ = crate::leanh::lean_box(0);
                    v_isShared_1470_ = v_isSharedCheck_1481_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1471_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_1460_, 2);
                if v_isShared_1470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1469_, 4, v_r_1460_);
                    crate::leanh::lean_ctor_set(v___x_1469_, 3, v_r_1460_);
                    crate::leanh::lean_ctor_set(v___x_1469_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v___x_1469_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1375_);
                    v___x_1473_ = v___x_1469_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1480_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1460_);
                    v___x_1473_ = v_reuseFailAlloc_1480_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_1460_);
                if v_isShared_1465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1464_, 3, v_r_1460_);
                    crate::leanh::lean_ctor_set(v___x_1464_, 0, v___x_1375_);
                    v___x_1475_ = v___x_1464_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_r_1460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_r_1460_);
                    v___x_1475_ = v_reuseFailAlloc_1479_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 4, v___x_1475_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 3, v___x_1473_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 2, v_v_1467_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 1, v_k_1466_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1471_);
                    v___x_1477_ = v___x_1231_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 3, v___x_1473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 4, v___x_1475_);
                    v___x_1477_ = v_reuseFailAlloc_1478_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1477_;
            }
            39 => {
                v___x_1494_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1492_, 4, v_l_1459_);
                    crate::leanh::lean_ctor_set(v___x_1492_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v___x_1492_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v___x_1492_, 0, v___x_1375_);
                    v___x_1496_ = v___x_1492_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1459_);
                    v___x_1496_ = v_reuseFailAlloc_1500_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 4, v_r_1488_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 3, v___x_1496_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 2, v_v_1490_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 1, v_k_1489_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1494_);
                    v___x_1498_ = v___x_1231_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1499_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_r_1488_);
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
    mut v_k_1512_: *mut crate::leanh::LeanObject,
    mut v_t_1513_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1513_) == 0 {
                    v_k_1514_ = crate::leanh::lean_ctor_get(v_t_1513_, 1);
                    v_l_1515_ = crate::leanh::lean_ctor_get(v_t_1513_, 3);
                    v_r_1516_ = crate::leanh::lean_ctor_get(v_t_1513_, 4);
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
    mut v_k_1522_: *mut crate::leanh::LeanObject,
    mut v_t_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: u8 = 0;
    let mut v_r_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_1522_, v_t_1523_);
    crate::leanh::lean_dec(v_t_1523_);
    crate::leanh::lean_dec(v_k_1522_);
    v_r_1525_ = crate::leanh::lean_box((v_res_1524_) as usize);
    return v_r_1525_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectFnBody(
    mut v_x_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_order_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: usize = 0;
    let mut v___x_1571_: usize = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: usize = 0;
    let mut v___x_1574_: usize = 0;
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1526_) {
                0 => {
                    v_e_1529_ = crate::leanh::lean_ctor_get(v_x_1526_, 2);
                    crate::leanh::lean_inc_ref(v_e_1529_);
                    v_b_1530_ = crate::leanh::lean_ctor_get(v_x_1526_, 3);
                    crate::leanh::lean_inc(v_b_1530_);
                    crate::leanh::lean_dec_ref_known(v_x_1526_, 4);
                    match crate::leanh::lean_obj_tag(v_e_1529_) {
                        6 => {
                            v_c_1554_ = crate::leanh::lean_ctor_get(v_e_1529_, 0);
                            crate::leanh::lean_inc(v_c_1554_);
                            crate::leanh::lean_dec_ref_known(v_e_1529_, 2);
                            v_f_1544_ = v_c_1554_;
                            v___y_1545_ = v_a_1527_;
                            v___y_1546_ = v_a_1528_;
                            state = 2;
                            continue;
                        }
                        7 => {
                            v_c_1555_ = crate::leanh::lean_ctor_get(v_e_1529_, 0);
                            crate::leanh::lean_inc(v_c_1555_);
                            crate::leanh::lean_dec_ref_known(v_e_1529_, 2);
                            v_f_1544_ = v_c_1555_;
                            v___y_1545_ = v_a_1527_;
                            v___y_1546_ = v_a_1528_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_1529_);
                            v_x_1526_ = v_b_1530_;
                            state = 0;
                            continue;
                        }
                    }
                }
                1 => {
                    v_v_1557_ = crate::leanh::lean_ctor_get(v_x_1526_, 2);
                    crate::leanh::lean_inc(v_v_1557_);
                    v_b_1558_ = crate::leanh::lean_ctor_get(v_x_1526_, 3);
                    crate::leanh::lean_inc(v_b_1558_);
                    crate::leanh::lean_dec_ref_known(v_x_1526_, 4);
                    v___x_1559_ =
                        l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_1557_, v_a_1527_, v_a_1528_);
                    v_snd_1560_ = crate::leanh::lean_ctor_get(v___x_1559_, 1);
                    crate::leanh::lean_inc(v_snd_1560_);
                    crate::leanh::lean_dec_ref(v___x_1559_);
                    v_x_1526_ = v_b_1558_;
                    v_a_1528_ = v_snd_1560_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_cs_1562_ = crate::leanh::lean_ctor_get(v_x_1526_, 3);
                    crate::leanh::lean_inc_ref(v_cs_1562_);
                    crate::leanh::lean_dec_ref_known(v_x_1526_, 4);
                    v___x_1563_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1564_ = lean_array_get_size(v_cs_1562_);
                    v___x_1565_ = crate::leanh::lean_box(0);
                    v___x_1566_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
                    if v___x_1566_ == 0 {
                        crate::leanh::lean_dec_ref(v_cs_1562_);
                        v___x_1567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1567_, 0, v___x_1565_);
                        crate::leanh::lean_ctor_set(v___x_1567_, 1, v_a_1528_);
                        return v___x_1567_;
                    } else {
                        v___x_1568_ = lean_nat_dec_le(v___x_1564_, v___x_1564_);
                        if v___x_1568_ == 0 {
                            if v___x_1566_ == 0 {
                                crate::leanh::lean_dec_ref(v_cs_1562_);
                                v___x_1569_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1569_, 0, v___x_1565_);
                                crate::leanh::lean_ctor_set(v___x_1569_, 1, v_a_1528_);
                                return v___x_1569_;
                            } else {
                                v___x_1570_ = 0usize;
                                v___x_1571_ = lean_usize_of_nat(v___x_1564_);
                                v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_1562_, v___x_1570_, v___x_1571_, v___x_1565_, v_a_1527_, v_a_1528_);
                                crate::leanh::lean_dec_ref(v_cs_1562_);
                                return v___x_1572_;
                            }
                        } else {
                            v___x_1573_ = 0usize;
                            v___x_1574_ = lean_usize_of_nat(v___x_1564_);
                            v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_1562_, v___x_1573_, v___x_1574_, v___x_1565_, v_a_1527_, v_a_1528_);
                            crate::leanh::lean_dec_ref(v_cs_1562_);
                            return v___x_1575_;
                        }
                    }
                }
                _ => {
                    v___x_1576_ = l_Lean_IR_FnBody_isTerminal(v_x_1526_);
                    if v___x_1576_ == 0 {
                        v___x_1577_ = l_Lean_IR_FnBody_body(v_x_1526_);
                        crate::leanh::lean_dec(v_x_1526_);
                        v_x_1526_ = v___x_1577_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1526_);
                        v___x_1579_ = crate::leanh::lean_box(0);
                        v___x_1580_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1580_, 0, v___x_1579_);
                        crate::leanh::lean_ctor_set(v___x_1580_, 1, v_a_1528_);
                        return v___x_1580_;
                    }
                }
            },
            1 => {
                v___x_1537_ = (crate::leanh::lean_unbox(v_fst_1535_) as u8);
                crate::leanh::lean_dec(v_fst_1535_);
                if v___x_1537_ == 0 {
                    v___x_1538_ = lean_array_push(v___y_1534_, v___y_1533_);
                    v___x_1539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1539_, 0, v_snd_1536_);
                    crate::leanh::lean_ctor_set(v___x_1539_, 1, v___x_1538_);
                    v_x_1526_ = v_b_1530_;
                    v_a_1527_ = v___y_1532_;
                    v_a_1528_ = v___x_1539_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1533_);
                    v___x_1541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1541_, 0, v_snd_1536_);
                    crate::leanh::lean_ctor_set(v___x_1541_, 1, v___y_1534_);
                    v_x_1526_ = v_b_1530_;
                    v_a_1527_ = v___y_1532_;
                    v_a_1528_ = v___x_1541_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_set_1547_ = crate::leanh::lean_ctor_get(v___y_1546_, 0);
                crate::leanh::lean_inc(v_set_1547_);
                v_order_1548_ = crate::leanh::lean_ctor_get(v___y_1546_, 1);
                crate::leanh::lean_inc_ref(v_order_1548_);
                crate::leanh::lean_dec_ref(v___y_1546_);
                v___x_1549_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_f_1544_, v_set_1547_);
                if v___x_1549_ == 0 {
                    v___x_1550_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_f_1544_);
                    v___x_1551_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_f_1544_, v___x_1550_, v_set_1547_);
                    v___x_1552_ = crate::leanh::lean_box((v___x_1549_) as usize);
                    v___y_1532_ = v___y_1545_;
                    v___y_1533_ = v_f_1544_;
                    v___y_1534_ = v_order_1548_;
                    v_fst_1535_ = v___x_1552_;
                    v_snd_1536_ = v___x_1551_;
                    state = 1;
                    continue;
                } else {
                    v___x_1553_ = crate::leanh::lean_box((v___x_1549_) as usize);
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
    mut v_as_1581_: *mut crate::leanh::LeanObject,
    mut v_i_1582_: usize,
    mut v_stop_1583_: usize,
    mut v_b_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
    mut v___y_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: usize = 0;
    let mut v___x_1594_: usize = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v_fst_1591_ = crate::leanh::lean_ctor_get(v___x_1590_, 0);
                    crate::leanh::lean_inc(v_fst_1591_);
                    v_snd_1592_ = crate::leanh::lean_ctor_get(v___x_1590_, 1);
                    crate::leanh::lean_inc(v_snd_1592_);
                    crate::leanh::lean_dec_ref(v___x_1590_);
                    v___x_1593_ = 1usize;
                    v___x_1594_ = lean_usize_add(v_i_1582_, v___x_1593_);
                    v_i_1582_ = v___x_1594_;
                    v_b_1584_ = v_fst_1591_;
                    v___y_1586_ = v_snd_1592_;
                    state = 0;
                    continue;
                } else {
                    v___x_1596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1596_, 0, v_b_1584_);
                    crate::leanh::lean_ctor_set(v___x_1596_, 1, v___y_1586_);
                    return v___x_1596_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(
    mut v_as_1597_: *mut crate::leanh::LeanObject,
    mut v_i_1598_: *mut crate::leanh::LeanObject,
    mut v_stop_1599_: *mut crate::leanh::LeanObject,
    mut v_b_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1603_: usize = 0;
    let mut v_stop_boxed_1604_: usize = 0;
    let mut v_res_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1603_ = crate::leanh::lean_unbox_usize(v_i_1598_);
    crate::leanh::lean_dec(v_i_1598_);
    v_stop_boxed_1604_ = crate::leanh::lean_unbox_usize(v_stop_1599_);
    crate::leanh::lean_dec(v_stop_1599_);
    v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_1597_, v_i_boxed_1603_, v_stop_boxed_1604_, v_b_1600_, v___y_1601_, v___y_1602_);
    crate::leanh::lean_dec_ref(v___y_1601_);
    crate::leanh::lean_dec_ref(v_as_1597_);
    return v_res_1605_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(
    mut v_x_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_1606_, v_a_1607_, v_a_1608_);
    crate::leanh::lean_dec_ref(v_a_1607_);
    return v_res_1609_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(
    mut v_00_u03b2_1610_: *mut crate::leanh::LeanObject,
    mut v_k_1611_: *mut crate::leanh::LeanObject,
    mut v_t_1612_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1613_: u8 = 0;
    v___x_1613_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_1611_, v_t_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(
    mut v_00_u03b2_1614_: *mut crate::leanh::LeanObject,
    mut v_k_1615_: *mut crate::leanh::LeanObject,
    mut v_t_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1617_: u8 = 0;
    let mut v_r_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_1614_, v_k_1615_, v_t_1616_);
    crate::leanh::lean_dec(v_t_1616_);
    crate::leanh::lean_dec(v_k_1615_);
    v_r_1618_ = crate::leanh::lean_box((v_res_1617_) as usize);
    return v_r_1618_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(
    mut v_00_u03b2_1619_: *mut crate::leanh::LeanObject,
    mut v_k_1620_: *mut crate::leanh::LeanObject,
    mut v_v_1621_: *mut crate::leanh::LeanObject,
    mut v_t_1622_: *mut crate::leanh::LeanObject,
    mut v_hl_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_1620_, v_v_1621_, v_t_1622_);
    return v___x_1624_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectInitDecl(
    mut v_fn_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_order_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_1626_);
                v___x_1628_ = lean_get_init_fn_name_for(v_a_1626_, v_fn_1625_);
                if crate::leanh::lean_obj_tag(v___x_1628_) == 1 {
                    v_val_1629_ = crate::leanh::lean_ctor_get(v___x_1628_, 0);
                    crate::leanh::lean_inc(v_val_1629_);
                    crate::leanh::lean_dec_ref_known(v___x_1628_, 1);
                    v_set_1630_ = crate::leanh::lean_ctor_get(v_a_1627_, 0);
                    v_order_1631_ = crate::leanh::lean_ctor_get(v_a_1627_, 1);
                    v_isSharedCheck_1653_ = (!crate::leanh::lean_is_exclusive(v_a_1627_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1633_ = v_a_1627_;
                        v_isShared_1634_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_order_1631_);
                        crate::leanh::lean_inc(v_set_1630_);
                        crate::leanh::lean_dec(v_a_1627_);
                        v___x_1633_ = crate::leanh::lean_box(0);
                        v_isShared_1634_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1628_);
                    v___x_1654_ = crate::leanh::lean_box(0);
                    v___x_1655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1654_);
                    crate::leanh::lean_ctor_set(v___x_1655_, 1, v_a_1627_);
                    return v___x_1655_;
                }
            }
            1 => {
                v___x_1635_ = crate::leanh::lean_box(0);
                v___x_1649_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_1629_, v_set_1630_);
                if v___x_1649_ == 0 {
                    crate::leanh::lean_inc(v_val_1629_);
                    v___x_1650_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_1629_, v___x_1635_, v_set_1630_);
                    v___x_1651_ = crate::leanh::lean_box((v___x_1649_) as usize);
                    v_fst_1637_ = v___x_1651_;
                    v_snd_1638_ = v___x_1650_;
                    state = 2;
                    continue;
                } else {
                    v___x_1652_ = crate::leanh::lean_box((v___x_1649_) as usize);
                    v_fst_1637_ = v___x_1652_;
                    v_snd_1638_ = v_set_1630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1639_ = (crate::leanh::lean_unbox(v_fst_1637_) as u8);
                crate::leanh::lean_dec(v_fst_1637_);
                if v___x_1639_ == 0 {
                    v___x_1640_ = lean_array_push(v_order_1631_, v_val_1629_);
                    if v_isShared_1634_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1633_, 1, v___x_1640_);
                        crate::leanh::lean_ctor_set(v___x_1633_, 0, v_snd_1638_);
                        v___x_1642_ = v___x_1633_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_snd_1638_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1640_);
                        v___x_1642_ = v_reuseFailAlloc_1644_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_1629_);
                    if v_isShared_1634_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1633_, 0, v_snd_1638_);
                        v___x_1646_ = v___x_1633_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_snd_1638_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_order_1631_);
                        v___x_1646_ = v_reuseFailAlloc_1648_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1643_, 0, v___x_1635_);
                crate::leanh::lean_ctor_set(v___x_1643_, 1, v___x_1642_);
                return v___x_1643_;
            }
            4 => {
                v___x_1647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1647_, 0, v___x_1635_);
                crate::leanh::lean_ctor_set(v___x_1647_, 1, v___x_1646_);
                return v___x_1647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(
    mut v_fn_1656_: *mut crate::leanh::LeanObject,
    mut v_a_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1659_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_1656_, v_a_1657_, v_a_1658_);
    crate::leanh::lean_dec_ref(v_a_1657_);
    return v_res_1659_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDecl(
    mut v_x_1660_: *mut crate::leanh::LeanObject,
    mut v_a_1661_: *mut crate::leanh::LeanObject,
    mut v_a_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1660_) == 0 {
        let mut v_f_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_f_1663_ = crate::leanh::lean_ctor_get(v_x_1660_, 0);
        crate::leanh::lean_inc(v_f_1663_);
        v_body_1664_ = crate::leanh::lean_ctor_get(v_x_1660_, 3);
        crate::leanh::lean_inc(v_body_1664_);
        crate::leanh::lean_dec_ref_known(v_x_1660_, 5);
        v___x_1665_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_1663_, v_a_1661_, v_a_1662_);
        v_snd_1666_ = crate::leanh::lean_ctor_get(v___x_1665_, 1);
        crate::leanh::lean_inc(v_snd_1666_);
        crate::leanh::lean_dec_ref(v___x_1665_);
        v___x_1667_ =
            l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_1664_, v_a_1661_, v_snd_1666_);
        return v___x_1667_;
    } else {
        let mut v_f_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_f_1668_ = crate::leanh::lean_ctor_get(v_x_1660_, 0);
        crate::leanh::lean_inc(v_f_1668_);
        crate::leanh::lean_dec_ref_known(v_x_1660_, 4);
        v___x_1669_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_1668_, v_a_1661_, v_a_1662_);
        return v___x_1669_;
    }
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDecl___boxed(
    mut v_x_1670_: *mut crate::leanh::LeanObject,
    mut v_a_1671_: *mut crate::leanh::LeanObject,
    mut v_a_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1673_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_1670_, v_a_1671_, v_a_1672_);
    crate::leanh::lean_dec_ref(v_a_1671_);
    return v_res_1673_;
}
pub unsafe fn l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
    mut v_as_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_order_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_1674_) == 0 {
                    v___x_1677_ = crate::leanh::lean_box(0);
                    v___x_1678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                    crate::leanh::lean_ctor_set(v___x_1678_, 1, v___y_1676_);
                    return v___x_1678_;
                } else {
                    v_head_1679_ = crate::leanh::lean_ctor_get(v_as_1674_, 0);
                    crate::leanh::lean_inc_n(v_head_1679_, 2);
                    v_tail_1680_ = crate::leanh::lean_ctor_get(v_as_1674_, 1);
                    crate::leanh::lean_inc(v_tail_1680_);
                    crate::leanh::lean_dec_ref_known(v_as_1674_, 2);
                    v___x_1681_ = l_Lean_IR_CollectUsedDecls_collectDecl(
                        v_head_1679_,
                        v___y_1675_,
                        v___y_1676_,
                    );
                    v_snd_1682_ = crate::leanh::lean_ctor_get(v___x_1681_, 1);
                    crate::leanh::lean_inc(v_snd_1682_);
                    crate::leanh::lean_dec_ref(v___x_1681_);
                    v_set_1683_ = crate::leanh::lean_ctor_get(v_snd_1682_, 0);
                    v_order_1684_ = crate::leanh::lean_ctor_get(v_snd_1682_, 1);
                    v_isSharedCheck_1707_ = (!crate::leanh::lean_is_exclusive(v_snd_1682_)) as u8;
                    if v_isSharedCheck_1707_ == 0 {
                        v___x_1686_ = v_snd_1682_;
                        v_isShared_1687_ = v_isSharedCheck_1707_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_order_1684_);
                        crate::leanh::lean_inc(v_set_1683_);
                        crate::leanh::lean_dec(v_snd_1682_);
                        v___x_1686_ = crate::leanh::lean_box(0);
                        v_isShared_1687_ = v_isSharedCheck_1707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1688_ = l_Lean_IR_Decl_name(v_head_1679_);
                crate::leanh::lean_dec(v_head_1679_);
                v___x_1702_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_1688_, v_set_1683_);
                if v___x_1702_ == 0 {
                    v___x_1703_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_1688_);
                    v___x_1704_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_1688_, v___x_1703_, v_set_1683_);
                    v___x_1705_ = crate::leanh::lean_box((v___x_1702_) as usize);
                    v_fst_1690_ = v___x_1705_;
                    v_snd_1691_ = v___x_1704_;
                    state = 2;
                    continue;
                } else {
                    v___x_1706_ = crate::leanh::lean_box((v___x_1702_) as usize);
                    v_fst_1690_ = v___x_1706_;
                    v_snd_1691_ = v_set_1683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1692_ = (crate::leanh::lean_unbox(v_fst_1690_) as u8);
                crate::leanh::lean_dec(v_fst_1690_);
                if v___x_1692_ == 0 {
                    v___x_1693_ = lean_array_push(v_order_1684_, v___x_1688_);
                    if v_isShared_1687_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1686_, 1, v___x_1693_);
                        crate::leanh::lean_ctor_set(v___x_1686_, 0, v_snd_1691_);
                        v___x_1695_ = v___x_1686_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_snd_1691_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1693_);
                        v___x_1695_ = v_reuseFailAlloc_1697_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1688_);
                    if v_isShared_1687_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1686_, 0, v_snd_1691_);
                        v___x_1699_ = v___x_1686_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1701_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_snd_1691_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_order_1684_);
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
    mut v_as_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1711_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
        v_as_1708_,
        v___y_1709_,
        v___y_1710_,
    );
    crate::leanh::lean_dec_ref(v___y_1709_);
    return v_res_1711_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDeclLoop(
    mut v_decls_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_a_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
        v_decls_1712_,
        v_a_1713_,
        v_a_1714_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(
    mut v_decls_1716_: *mut crate::leanh::LeanObject,
    mut v_a_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1719_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_1716_, v_a_1717_, v_a_1718_);
    crate::leanh::lean_dec_ref(v_a_1717_);
    return v_res_1719_;
}
pub unsafe fn _init_l_Lean_IR_collectUsedDecls___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1722_ = l_Lean_IR_collectUsedDecls___closed__0;
    v___x_1723_ = l_Lean_NameSet_empty;
    v___x_1724_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1724_, 0, v___x_1723_);
    crate::leanh::lean_ctor_set(v___x_1724_, 1, v___x_1722_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_IR_collectUsedDecls(
    mut v_env_1725_: *mut crate::leanh::LeanObject,
    mut v_decls_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_order_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_collectUsedDecls___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_collectUsedDecls___closed__1_once),
        _init_l_Lean_IR_collectUsedDecls___closed__1,
    );
    v___x_1728_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(
        v_decls_1726_,
        v_env_1725_,
        v___x_1727_,
    );
    v_snd_1729_ = crate::leanh::lean_ctor_get(v___x_1728_, 1);
    crate::leanh::lean_inc(v_snd_1729_);
    crate::leanh::lean_dec_ref(v___x_1728_);
    v_order_1730_ = crate::leanh::lean_ctor_get(v_snd_1729_, 1);
    crate::leanh::lean_inc_ref(v_order_1730_);
    crate::leanh::lean_dec(v_snd_1729_);
    return v_order_1730_;
}
pub unsafe fn l_Lean_IR_collectUsedDecls___boxed(
    mut v_env_1731_: *mut crate::leanh::LeanObject,
    mut v_decls_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Lean_IR_collectUsedDecls(v_env_1731_, v_decls_1732_);
    crate::leanh::lean_dec_ref(v_env_1731_);
    return v_res_1733_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectVar(
    mut v_x_1736_: *mut crate::leanh::LeanObject,
    mut v_t_1737_: *mut crate::leanh::LeanObject,
    mut v_x_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1739_ = crate::leanh::lean_ctor_get(v_x_1738_, 0);
                v_snd_1740_ = crate::leanh::lean_ctor_get(v_x_1738_, 1);
                v_isSharedCheck_1750_ = (!crate::leanh::lean_is_exclusive(v_x_1738_)) as u8;
                if v_isSharedCheck_1750_ == 0 {
                    v___x_1742_ = v_x_1738_;
                    v_isShared_1743_ = v_isSharedCheck_1750_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1740_);
                    crate::leanh::lean_inc(v_fst_1739_);
                    crate::leanh::lean_dec(v_x_1738_);
                    v___x_1742_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1746_);
                    v___x_1748_ = v___x_1742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_snd_1740_);
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
    mut v_x_1751_: *mut crate::leanh::LeanObject,
    mut v_x_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1752_) == 0 {
                    return v_x_1751_;
                } else {
                    v_key_1753_ = crate::leanh::lean_ctor_get(v_x_1752_, 0);
                    v_value_1754_ = crate::leanh::lean_ctor_get(v_x_1752_, 1);
                    v_tail_1755_ = crate::leanh::lean_ctor_get(v_x_1752_, 2);
                    v_isSharedCheck_1778_ = (!crate::leanh::lean_is_exclusive(v_x_1752_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1757_ = v_x_1752_;
                        v_isShared_1758_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1755_);
                        crate::leanh::lean_inc(v_value_1754_);
                        crate::leanh::lean_inc(v_key_1753_);
                        crate::leanh::lean_dec(v_x_1752_);
                        v___x_1757_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_1772_);
                if v_isShared_1758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1757_, 2, v___x_1772_);
                    v___x_1774_ = v___x_1757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_key_1753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_value_1754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 2, v___x_1772_);
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
    mut v_i_1779_: *mut crate::leanh::LeanObject,
    mut v_source_1780_: *mut crate::leanh::LeanObject,
    mut v_target_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v_es_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1782_ = lean_array_get_size(v_source_1780_);
                v___x_1783_ = lean_nat_dec_lt(v_i_1779_, v___x_1782_);
                if v___x_1783_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1780_);
                    crate::leanh::lean_dec(v_i_1779_);
                    return v_target_1781_;
                } else {
                    v_es_1784_ = lean_array_fget(v_source_1780_, v_i_1779_);
                    v___x_1785_ = crate::leanh::lean_box(0);
                    v_source_1786_ = lean_array_fset(v_source_1780_, v_i_1779_, v___x_1785_);
                    v_target_1787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1781_, v_es_1784_);
                    v___x_1788_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1789_ = lean_nat_add(v_i_1779_, v___x_1788_);
                    crate::leanh::lean_dec(v_i_1779_);
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
    mut v_data_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = lean_array_get_size(v_data_1791_);
    v___x_1793_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1794_ = lean_nat_mul(v___x_1792_, v___x_1793_);
    v___x_1795_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1796_ = crate::leanh::lean_box(0);
    v___x_1797_ = lean_mk_array(v_nbuckets_1794_, v___x_1796_);
    v___x_1798_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_1795_, v_data_1791_, v___x_1797_);
    return v___x_1798_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(
    mut v_a_1799_: *mut crate::leanh::LeanObject,
    mut v_x_1800_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1801_: u8 = 0;
    let mut v_key_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1800_) == 0 {
                    v___x_1801_ = 0;
                    return v___x_1801_;
                } else {
                    v_key_1802_ = crate::leanh::lean_ctor_get(v_x_1800_, 0);
                    v_tail_1803_ = crate::leanh::lean_ctor_get(v_x_1800_, 2);
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
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_x_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1808_: u8 = 0;
    let mut v_r_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_1806_, v_x_1807_);
    crate::leanh::lean_dec(v_x_1807_);
    crate::leanh::lean_dec(v_a_1806_);
    v_r_1809_ = crate::leanh::lean_box((v_res_1808_) as usize);
    return v_r_1809_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(
    mut v_a_1810_: *mut crate::leanh::LeanObject,
    mut v_b_1811_: *mut crate::leanh::LeanObject,
    mut v_x_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1812_) == 0 {
                    crate::leanh::lean_dec(v_b_1811_);
                    crate::leanh::lean_dec(v_a_1810_);
                    return v_x_1812_;
                } else {
                    v_key_1813_ = crate::leanh::lean_ctor_get(v_x_1812_, 0);
                    v_value_1814_ = crate::leanh::lean_ctor_get(v_x_1812_, 1);
                    v_tail_1815_ = crate::leanh::lean_ctor_get(v_x_1812_, 2);
                    v_isSharedCheck_1827_ = (!crate::leanh::lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1817_ = v_x_1812_;
                        v_isShared_1818_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1815_);
                        crate::leanh::lean_inc(v_value_1814_);
                        crate::leanh::lean_inc(v_key_1813_);
                        crate::leanh::lean_dec(v_x_1812_);
                        v___x_1817_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_1817_, 2, v___x_1820_);
                        v___x_1822_ = v___x_1817_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1823_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_key_1813_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_value_1814_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 2, v___x_1820_);
                        v___x_1822_ = v_reuseFailAlloc_1823_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1814_);
                    crate::leanh::lean_dec(v_key_1813_);
                    if v_isShared_1818_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1817_, 1, v_b_1811_);
                        crate::leanh::lean_ctor_set(v___x_1817_, 0, v_a_1810_);
                        v___x_1825_ = v___x_1817_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1810_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_b_1811_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_tail_1815_);
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
    mut v_m_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
    mut v_b_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v_val_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1831_ = crate::leanh::lean_ctor_get(v_m_1828_, 0);
                v_buckets_1832_ = crate::leanh::lean_ctor_get(v_m_1828_, 1);
                v_isSharedCheck_1875_ = (!crate::leanh::lean_is_exclusive(v_m_1828_)) as u8;
                if v_isSharedCheck_1875_ == 0 {
                    v___x_1834_ = v_m_1828_;
                    v_isShared_1835_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1832_);
                    crate::leanh::lean_inc(v_size_1831_);
                    crate::leanh::lean_dec(v_m_1828_);
                    v___x_1834_ = crate::leanh::lean_box(0);
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
                    v___x_1851_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1852_ = lean_nat_add(v_size_1831_, v___x_1851_);
                    crate::leanh::lean_dec(v_size_1831_);
                    crate::leanh::lean_inc(v_bkt_1849_);
                    v___x_1853_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1853_, 0, v_a_1829_);
                    crate::leanh::lean_ctor_set(v___x_1853_, 1, v_b_1830_);
                    crate::leanh::lean_ctor_set(v___x_1853_, 2, v_bkt_1849_);
                    v_buckets_x27_1854_ =
                        lean_array_uset(v_buckets_1832_, v___x_1848_, v___x_1853_);
                    v___x_1855_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1856_ = lean_nat_mul(v_size_x27_1852_, v___x_1855_);
                    v___x_1857_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1858_ = lean_nat_div(v___x_1856_, v___x_1857_);
                    crate::leanh::lean_dec(v___x_1856_);
                    v___x_1859_ = lean_array_get_size(v_buckets_x27_1854_);
                    v___x_1860_ = lean_nat_dec_le(v___x_1858_, v___x_1859_);
                    crate::leanh::lean_dec(v___x_1858_);
                    if v___x_1860_ == 0 {
                        v_val_1861_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_1854_);
                        if v_isShared_1835_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1834_, 1, v_val_1861_);
                            crate::leanh::lean_ctor_set(v___x_1834_, 0, v_size_x27_1852_);
                            v___x_1863_ = v___x_1834_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1864_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1864_,
                                0,
                                v_size_x27_1852_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_val_1861_);
                            v___x_1863_ = v_reuseFailAlloc_1864_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1835_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1834_, 1, v_buckets_x27_1854_);
                            crate::leanh::lean_ctor_set(v___x_1834_, 0, v_size_x27_1852_);
                            v___x_1866_ = v___x_1834_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1867_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1867_,
                                0,
                                v_size_x27_1852_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1867_,
                                1,
                                v_buckets_x27_1854_,
                            );
                            v___x_1866_ = v_reuseFailAlloc_1867_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1849_);
                    v___x_1868_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1869_ =
                        lean_array_uset(v_buckets_1832_, v___x_1848_, v___x_1868_);
                    v___x_1870_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_1829_, v_b_1830_, v_bkt_1849_);
                    v___x_1871_ = lean_array_uset(v_buckets_x27_1869_, v___x_1848_, v___x_1870_);
                    if v_isShared_1835_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1834_, 1, v___x_1871_);
                        v___x_1873_ = v___x_1834_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1874_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_size_1831_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1871_);
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
    mut v_as_1876_: *mut crate::leanh::LeanObject,
    mut v_i_1877_: usize,
    mut v_stop_1878_: usize,
    mut v_b_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: u8 = 0;
    let mut v_fst_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1885_: u8 = 0;
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: usize = 0;
    let mut v___x_1893_: usize = 0;
    let mut v_reuseFailAlloc_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = lean_usize_dec_eq(v_i_1877_, v_stop_1878_);
                if v___x_1880_ == 0 {
                    v_fst_1881_ = crate::leanh::lean_ctor_get(v_b_1879_, 0);
                    v_snd_1882_ = crate::leanh::lean_ctor_get(v_b_1879_, 1);
                    v_isSharedCheck_1896_ = (!crate::leanh::lean_is_exclusive(v_b_1879_)) as u8;
                    if v_isSharedCheck_1896_ == 0 {
                        v___x_1884_ = v_b_1879_;
                        v_isShared_1885_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1882_);
                        crate::leanh::lean_inc(v_fst_1881_);
                        crate::leanh::lean_dec(v_b_1879_);
                        v___x_1884_ = crate::leanh::lean_box(0);
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
                v_x_1887_ = crate::leanh::lean_ctor_get(v___x_1886_, 0);
                v_ty_1888_ = crate::leanh::lean_ctor_get(v___x_1886_, 1);
                crate::leanh::lean_inc(v_ty_1888_);
                crate::leanh::lean_inc(v_x_1887_);
                v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_1881_, v_x_1887_, v_ty_1888_);
                if v_isShared_1885_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1884_, 0, v___x_1889_);
                    v___x_1891_ = v___x_1884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_snd_1882_);
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
    mut v_as_1897_: *mut crate::leanh::LeanObject,
    mut v_i_1898_: *mut crate::leanh::LeanObject,
    mut v_stop_1899_: *mut crate::leanh::LeanObject,
    mut v_b_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1901_: usize = 0;
    let mut v_stop_boxed_1902_: usize = 0;
    let mut v_res_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1901_ = crate::leanh::lean_unbox_usize(v_i_1898_);
    crate::leanh::lean_dec(v_i_1898_);
    v_stop_boxed_1902_ = crate::leanh::lean_unbox_usize(v_stop_1899_);
    crate::leanh::lean_dec(v_stop_1899_);
    v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_1897_, v_i_boxed_1901_, v_stop_boxed_1902_, v_b_1900_);
    crate::leanh::lean_dec_ref(v_as_1897_);
    return v_res_1903_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectParams(
    mut v_ps_1904_: *mut crate::leanh::LeanObject,
    mut v_s_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u8 = 0;
    v___x_1906_ = crate::leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1910_ = 0usize;
                v___x_1911_ = lean_usize_of_nat(v___x_1907_);
                v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_1904_, v___x_1910_, v___x_1911_, v_s_1905_);
                return v___x_1912_;
            }
        } else {
            let mut v___x_1913_: usize = 0;
            let mut v___x_1914_: usize = 0;
            let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1913_ = 0usize;
            v___x_1914_ = lean_usize_of_nat(v___x_1907_);
            v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_1904_, v___x_1913_, v___x_1914_, v_s_1905_);
            return v___x_1915_;
        }
    }
}
pub unsafe fn l_Lean_IR_CollectMaps_collectParams___boxed(
    mut v_ps_1916_: *mut crate::leanh::LeanObject,
    mut v_s_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1918_ = l_Lean_IR_CollectMaps_collectParams(v_ps_1916_, v_s_1917_);
    crate::leanh::lean_dec_ref(v_ps_1916_);
    return v_res_1918_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(
    mut v_00_u03b2_1919_: *mut crate::leanh::LeanObject,
    mut v_m_1920_: *mut crate::leanh::LeanObject,
    mut v_a_1921_: *mut crate::leanh::LeanObject,
    mut v_b_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_1920_, v_a_1921_, v_b_1922_);
    return v___x_1923_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(
    mut v_00_u03b2_1924_: *mut crate::leanh::LeanObject,
    mut v_a_1925_: *mut crate::leanh::LeanObject,
    mut v_x_1926_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1927_: u8 = 0;
    v___x_1927_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_1925_, v_x_1926_);
    return v___x_1927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(
    mut v_00_u03b2_1928_: *mut crate::leanh::LeanObject,
    mut v_a_1929_: *mut crate::leanh::LeanObject,
    mut v_x_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1931_: u8 = 0;
    let mut v_r_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1931_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_1928_, v_a_1929_, v_x_1930_);
    crate::leanh::lean_dec(v_x_1930_);
    crate::leanh::lean_dec(v_a_1929_);
    v_r_1932_ = crate::leanh::lean_box((v_res_1931_) as usize);
    return v_r_1932_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(
    mut v_00_u03b2_1933_: *mut crate::leanh::LeanObject,
    mut v_data_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_1934_);
    return v___x_1935_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(
    mut v_00_u03b2_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
    mut v_b_1938_: *mut crate::leanh::LeanObject,
    mut v_x_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_1937_, v_b_1938_, v_x_1939_);
    return v___x_1940_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1941_: *mut crate::leanh::LeanObject,
    mut v_i_1942_: *mut crate::leanh::LeanObject,
    mut v_source_1943_: *mut crate::leanh::LeanObject,
    mut v_target_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_1942_, v_source_1943_, v_target_1944_);
    return v___x_1945_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1946_: *mut crate::leanh::LeanObject,
    mut v_x_1947_: *mut crate::leanh::LeanObject,
    mut v_x_1948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1947_, v_x_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectJP(
    mut v_j_1952_: *mut crate::leanh::LeanObject,
    mut v_xs_1953_: *mut crate::leanh::LeanObject,
    mut v_x_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1955_ = crate::leanh::lean_ctor_get(v_x_1954_, 0);
                v_snd_1956_ = crate::leanh::lean_ctor_get(v_x_1954_, 1);
                v_isSharedCheck_1966_ = (!crate::leanh::lean_is_exclusive(v_x_1954_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v___x_1958_ = v_x_1954_;
                    v_isShared_1959_ = v_isSharedCheck_1966_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1956_);
                    crate::leanh::lean_inc(v_fst_1955_);
                    crate::leanh::lean_dec(v_x_1954_);
                    v___x_1958_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1958_, 1, v___x_1962_);
                    v___x_1964_ = v___x_1958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_fst_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___x_1962_);
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
    mut v_a_1967_: *mut crate::leanh::LeanObject,
    mut v_x_1968_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1969_: u8 = 0;
    let mut v_key_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1968_) == 0 {
                    v___x_1969_ = 0;
                    return v___x_1969_;
                } else {
                    v_key_1970_ = crate::leanh::lean_ctor_get(v_x_1968_, 0);
                    v_tail_1971_ = crate::leanh::lean_ctor_get(v_x_1968_, 2);
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
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v_x_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: u8 = 0;
    let mut v_r_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1974_, v_x_1975_);
    crate::leanh::lean_dec(v_x_1975_);
    crate::leanh::lean_dec(v_a_1974_);
    v_r_1977_ = crate::leanh::lean_box((v_res_1976_) as usize);
    return v_r_1977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_1978_: *mut crate::leanh::LeanObject,
    mut v_x_1979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1979_) == 0 {
                    return v_x_1978_;
                } else {
                    v_key_1980_ = crate::leanh::lean_ctor_get(v_x_1979_, 0);
                    v_value_1981_ = crate::leanh::lean_ctor_get(v_x_1979_, 1);
                    v_tail_1982_ = crate::leanh::lean_ctor_get(v_x_1979_, 2);
                    v_isSharedCheck_2005_ = (!crate::leanh::lean_is_exclusive(v_x_1979_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_1984_ = v_x_1979_;
                        v_isShared_1985_ = v_isSharedCheck_2005_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1982_);
                        crate::leanh::lean_inc(v_value_1981_);
                        crate::leanh::lean_inc(v_key_1980_);
                        crate::leanh::lean_dec(v_x_1979_);
                        v___x_1984_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_1999_);
                if v_isShared_1985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1984_, 2, v___x_1999_);
                    v___x_2001_ = v___x_1984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_key_1980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_value_1981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 2, v___x_1999_);
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
    mut v_i_2006_: *mut crate::leanh::LeanObject,
    mut v_source_2007_: *mut crate::leanh::LeanObject,
    mut v_target_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v_es_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2009_ = lean_array_get_size(v_source_2007_);
                v___x_2010_ = lean_nat_dec_lt(v_i_2006_, v___x_2009_);
                if v___x_2010_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2007_);
                    crate::leanh::lean_dec(v_i_2006_);
                    return v_target_2008_;
                } else {
                    v_es_2011_ = lean_array_fget(v_source_2007_, v_i_2006_);
                    v___x_2012_ = crate::leanh::lean_box(0);
                    v_source_2013_ = lean_array_fset(v_source_2007_, v_i_2006_, v___x_2012_);
                    v_target_2014_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2008_, v_es_2011_);
                    v___x_2015_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2016_ = lean_nat_add(v_i_2006_, v___x_2015_);
                    crate::leanh::lean_dec(v_i_2006_);
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
    mut v_data_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2019_ = lean_array_get_size(v_data_2018_);
    v___x_2020_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2021_ = lean_nat_mul(v___x_2019_, v___x_2020_);
    v___x_2022_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2023_ = crate::leanh::lean_box(0);
    v___x_2024_ = lean_mk_array(v_nbuckets_2021_, v___x_2023_);
    v___x_2025_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_2022_, v_data_2018_, v___x_2024_);
    return v___x_2025_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(
    mut v_a_2026_: *mut crate::leanh::LeanObject,
    mut v_b_2027_: *mut crate::leanh::LeanObject,
    mut v_x_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2028_) == 0 {
                    crate::leanh::lean_dec(v_b_2027_);
                    crate::leanh::lean_dec(v_a_2026_);
                    return v_x_2028_;
                } else {
                    v_key_2029_ = crate::leanh::lean_ctor_get(v_x_2028_, 0);
                    v_value_2030_ = crate::leanh::lean_ctor_get(v_x_2028_, 1);
                    v_tail_2031_ = crate::leanh::lean_ctor_get(v_x_2028_, 2);
                    v_isSharedCheck_2043_ = (!crate::leanh::lean_is_exclusive(v_x_2028_)) as u8;
                    if v_isSharedCheck_2043_ == 0 {
                        v___x_2033_ = v_x_2028_;
                        v_isShared_2034_ = v_isSharedCheck_2043_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2031_);
                        crate::leanh::lean_inc(v_value_2030_);
                        crate::leanh::lean_inc(v_key_2029_);
                        crate::leanh::lean_dec(v_x_2028_);
                        v___x_2033_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_2033_, 2, v___x_2036_);
                        v___x_2038_ = v___x_2033_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2039_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_key_2029_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_value_2030_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 2, v___x_2036_);
                        v___x_2038_ = v_reuseFailAlloc_2039_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2030_);
                    crate::leanh::lean_dec(v_key_2029_);
                    if v_isShared_2034_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2033_, 1, v_b_2027_);
                        crate::leanh::lean_ctor_set(v___x_2033_, 0, v_a_2026_);
                        v___x_2041_ = v___x_2033_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2042_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2026_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_b_2027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_tail_2031_);
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
    mut v_m_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_b_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v_val_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2047_ = crate::leanh::lean_ctor_get(v_m_2044_, 0);
                v_buckets_2048_ = crate::leanh::lean_ctor_get(v_m_2044_, 1);
                v_isSharedCheck_2091_ = (!crate::leanh::lean_is_exclusive(v_m_2044_)) as u8;
                if v_isSharedCheck_2091_ == 0 {
                    v___x_2050_ = v_m_2044_;
                    v_isShared_2051_ = v_isSharedCheck_2091_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2048_);
                    crate::leanh::lean_inc(v_size_2047_);
                    crate::leanh::lean_dec(v_m_2044_);
                    v___x_2050_ = crate::leanh::lean_box(0);
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
                    v___x_2067_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2068_ = lean_nat_add(v_size_2047_, v___x_2067_);
                    crate::leanh::lean_dec(v_size_2047_);
                    crate::leanh::lean_inc(v_bkt_2065_);
                    v___x_2069_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2069_, 0, v_a_2045_);
                    crate::leanh::lean_ctor_set(v___x_2069_, 1, v_b_2046_);
                    crate::leanh::lean_ctor_set(v___x_2069_, 2, v_bkt_2065_);
                    v_buckets_x27_2070_ =
                        lean_array_uset(v_buckets_2048_, v___x_2064_, v___x_2069_);
                    v___x_2071_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2072_ = lean_nat_mul(v_size_x27_2068_, v___x_2071_);
                    v___x_2073_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2074_ = lean_nat_div(v___x_2072_, v___x_2073_);
                    crate::leanh::lean_dec(v___x_2072_);
                    v___x_2075_ = lean_array_get_size(v_buckets_x27_2070_);
                    v___x_2076_ = lean_nat_dec_le(v___x_2074_, v___x_2075_);
                    crate::leanh::lean_dec(v___x_2074_);
                    if v___x_2076_ == 0 {
                        v_val_2077_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_2070_);
                        if v_isShared_2051_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2050_, 1, v_val_2077_);
                            crate::leanh::lean_ctor_set(v___x_2050_, 0, v_size_x27_2068_);
                            v___x_2079_ = v___x_2050_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2080_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2080_,
                                0,
                                v_size_x27_2068_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_val_2077_);
                            v___x_2079_ = v_reuseFailAlloc_2080_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2051_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2050_, 1, v_buckets_x27_2070_);
                            crate::leanh::lean_ctor_set(v___x_2050_, 0, v_size_x27_2068_);
                            v___x_2082_ = v___x_2050_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2083_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2083_,
                                0,
                                v_size_x27_2068_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2083_,
                                1,
                                v_buckets_x27_2070_,
                            );
                            v___x_2082_ = v_reuseFailAlloc_2083_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2065_);
                    v___x_2084_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2085_ =
                        lean_array_uset(v_buckets_2048_, v___x_2064_, v___x_2084_);
                    v___x_2086_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_2045_, v_b_2046_, v_bkt_2065_);
                    v___x_2087_ = lean_array_uset(v_buckets_x27_2085_, v___x_2064_, v___x_2086_);
                    if v_isShared_2051_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2050_, 1, v___x_2087_);
                        v___x_2089_ = v___x_2050_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_size_2047_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2087_);
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
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut v_j_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_cs_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: usize = 0;
    let mut v___x_2131_: usize = 0;
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: usize = 0;
    let mut v___x_2134_: usize = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2092_) {
                0 => {
                    v_x_2094_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2094_);
                    v_ty_2095_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_ty_2095_);
                    v_b_2096_ = crate::leanh::lean_ctor_get(v_x_2092_, 3);
                    crate::leanh::lean_inc(v_b_2096_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2097_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_2096_, v_a_2093_);
                    v_fst_2098_ = crate::leanh::lean_ctor_get(v___x_2097_, 0);
                    v_snd_2099_ = crate::leanh::lean_ctor_get(v___x_2097_, 1);
                    v_isSharedCheck_2107_ = (!crate::leanh::lean_is_exclusive(v___x_2097_)) as u8;
                    if v_isSharedCheck_2107_ == 0 {
                        v___x_2101_ = v___x_2097_;
                        v_isShared_2102_ = v_isSharedCheck_2107_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2099_);
                        crate::leanh::lean_inc(v_fst_2098_);
                        crate::leanh::lean_dec(v___x_2097_);
                        v___x_2101_ = crate::leanh::lean_box(0);
                        v_isShared_2102_ = v_isSharedCheck_2107_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_j_2108_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_j_2108_);
                    v_xs_2109_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc_ref(v_xs_2109_);
                    v_v_2110_ = crate::leanh::lean_ctor_get(v_x_2092_, 2);
                    crate::leanh::lean_inc(v_v_2110_);
                    v_b_2111_ = crate::leanh::lean_ctor_get(v_x_2092_, 3);
                    crate::leanh::lean_inc(v_b_2111_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2112_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_2111_, v_a_2093_);
                    v___x_2113_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_2110_, v___x_2112_);
                    v___x_2114_ = l_Lean_IR_CollectMaps_collectParams(v_xs_2109_, v___x_2113_);
                    v_fst_2115_ = crate::leanh::lean_ctor_get(v___x_2114_, 0);
                    v_snd_2116_ = crate::leanh::lean_ctor_get(v___x_2114_, 1);
                    v_isSharedCheck_2124_ = (!crate::leanh::lean_is_exclusive(v___x_2114_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2118_ = v___x_2114_;
                        v_isShared_2119_ = v_isSharedCheck_2124_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2116_);
                        crate::leanh::lean_inc(v_fst_2115_);
                        crate::leanh::lean_dec(v___x_2114_);
                        v___x_2118_ = crate::leanh::lean_box(0);
                        v_isShared_2119_ = v_isSharedCheck_2124_;
                        state = 3;
                        continue;
                    }
                }
                9 => {
                    v_cs_2125_ = crate::leanh::lean_ctor_get(v_x_2092_, 3);
                    crate::leanh::lean_inc_ref(v_cs_2125_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2126_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2127_ = lean_array_get_size(v_cs_2125_);
                    v___x_2128_ = lean_nat_dec_lt(v___x_2126_, v___x_2127_);
                    if v___x_2128_ == 0 {
                        crate::leanh::lean_dec_ref(v_cs_2125_);
                        return v_a_2093_;
                    } else {
                        v___x_2129_ = lean_nat_dec_le(v___x_2127_, v___x_2127_);
                        if v___x_2129_ == 0 {
                            if v___x_2128_ == 0 {
                                crate::leanh::lean_dec_ref(v_cs_2125_);
                                return v_a_2093_;
                            } else {
                                v___x_2130_ = 0usize;
                                v___x_2131_ = lean_usize_of_nat(v___x_2127_);
                                v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_2125_, v___x_2130_, v___x_2131_, v_a_2093_);
                                crate::leanh::lean_dec_ref(v_cs_2125_);
                                return v___x_2132_;
                            }
                        } else {
                            v___x_2133_ = 0usize;
                            v___x_2134_ = lean_usize_of_nat(v___x_2127_);
                            v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_2125_, v___x_2133_, v___x_2134_, v_a_2093_);
                            crate::leanh::lean_dec_ref(v_cs_2125_);
                            return v___x_2135_;
                        }
                    }
                }
                _ => {
                    v___x_2136_ = l_Lean_IR_FnBody_isTerminal(v_x_2092_);
                    if v___x_2136_ == 0 {
                        v___x_2137_ = l_Lean_IR_FnBody_body(v_x_2092_);
                        crate::leanh::lean_dec(v_x_2092_);
                        v_x_2092_ = v___x_2137_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2092_);
                        return v_a_2093_;
                    }
                }
            },
            1 => {
                v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_2098_, v_x_2094_, v_ty_2095_);
                if v_isShared_2102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2103_);
                    v___x_2105_ = v___x_2101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_snd_2099_);
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
                    crate::leanh::lean_ctor_set(v___x_2118_, 1, v___x_2120_);
                    v___x_2122_ = v___x_2118_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_fst_2115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2120_);
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
    mut v_as_2139_: *mut crate::leanh::LeanObject,
    mut v_i_2140_: usize,
    mut v_stop_2141_: usize,
    mut v_b_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_as_2150_: *mut crate::leanh::LeanObject,
    mut v_i_2151_: *mut crate::leanh::LeanObject,
    mut v_stop_2152_: *mut crate::leanh::LeanObject,
    mut v_b_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2154_: usize = 0;
    let mut v_stop_boxed_2155_: usize = 0;
    let mut v_res_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2154_ = crate::leanh::lean_unbox_usize(v_i_2151_);
    crate::leanh::lean_dec(v_i_2151_);
    v_stop_boxed_2155_ = crate::leanh::lean_unbox_usize(v_stop_2152_);
    crate::leanh::lean_dec(v_stop_2152_);
    v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_2150_, v_i_boxed_2154_, v_stop_boxed_2155_, v_b_2153_);
    crate::leanh::lean_dec_ref(v_as_2150_);
    return v_res_2156_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(
    mut v_00_u03b2_2157_: *mut crate::leanh::LeanObject,
    mut v_m_2158_: *mut crate::leanh::LeanObject,
    mut v_a_2159_: *mut crate::leanh::LeanObject,
    mut v_b_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_2158_, v_a_2159_, v_b_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(
    mut v_00_u03b2_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_x_2164_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2165_: u8 = 0;
    v___x_2165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_2163_, v_x_2164_);
    return v___x_2165_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(
    mut v_00_u03b2_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
    mut v_x_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2169_: u8 = 0;
    let mut v_r_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_2166_, v_a_2167_, v_x_2168_);
    crate::leanh::lean_dec(v_x_2168_);
    crate::leanh::lean_dec(v_a_2167_);
    v_r_2170_ = crate::leanh::lean_box((v_res_2169_) as usize);
    return v_r_2170_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(
    mut v_00_u03b2_2171_: *mut crate::leanh::LeanObject,
    mut v_data_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2173_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_2172_);
    return v___x_2173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(
    mut v_00_u03b2_2174_: *mut crate::leanh::LeanObject,
    mut v_a_2175_: *mut crate::leanh::LeanObject,
    mut v_b_2176_: *mut crate::leanh::LeanObject,
    mut v_x_2177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_2175_, v_b_2176_, v_x_2177_);
    return v___x_2178_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2179_: *mut crate::leanh::LeanObject,
    mut v_i_2180_: *mut crate::leanh::LeanObject,
    mut v_source_2181_: *mut crate::leanh::LeanObject,
    mut v_target_2182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_2180_, v_source_2181_, v_target_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2184_: *mut crate::leanh::LeanObject,
    mut v_x_2185_: *mut crate::leanh::LeanObject,
    mut v_x_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2185_, v_x_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Lean_IR_CollectMaps_collectDecl(
    mut v_x_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2188_) == 0 {
        let mut v_xs_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_xs_2190_ = crate::leanh::lean_ctor_get(v_x_2188_, 1);
        crate::leanh::lean_inc_ref(v_xs_2190_);
        v_body_2191_ = crate::leanh::lean_ctor_get(v_x_2188_, 3);
        crate::leanh::lean_inc(v_body_2191_);
        crate::leanh::lean_dec_ref_known(v_x_2188_, 5);
        v___x_2192_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_2191_, v_a_2189_);
        v___x_2193_ = l_Lean_IR_CollectMaps_collectParams(v_xs_2190_, v___x_2192_);
        crate::leanh::lean_dec_ref(v_xs_2190_);
        return v___x_2193_;
    } else {
        crate::leanh::lean_dec_ref(v_x_2188_);
        return v_a_2189_;
    }
}
pub unsafe fn _init_l_Lean_IR_mkVarJPMaps___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = crate::leanh::lean_box(0);
    v___x_2195_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2196_ = lean_mk_array(v___x_2195_, v___x_2194_);
    return v___x_2196_;
}
pub unsafe fn _init_l_Lean_IR_mkVarJPMaps___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__0_once),
        _init_l_Lean_IR_mkVarJPMaps___closed__0,
    );
    v___x_2198_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2199_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2198_);
    crate::leanh::lean_ctor_set(v___x_2199_, 1, v___x_2197_);
    return v___x_2199_;
}
pub unsafe fn _init_l_Lean_IR_mkVarJPMaps___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__1_once),
        _init_l_Lean_IR_mkVarJPMaps___closed__1,
    );
    v___x_2201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2200_);
    crate::leanh::lean_ctor_set(v___x_2201_, 1, v___x_2200_);
    return v___x_2201_;
}
pub unsafe fn l_Lean_IR_mkVarJPMaps(
    mut v_d_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__2),
        core::ptr::addr_of_mut!(l_Lean_IR_mkVarJPMaps___closed__2_once),
        _init_l_Lean_IR_mkVarJPMaps___closed__2,
    );
    v___x_2204_ = l_Lean_IR_CollectMaps_collectDecl(v_d_2202_, v___x_2203_);
    return v___x_2204_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_EmitUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_EmitUtil(
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
pub unsafe fn initialize_Lean_Compiler_IR_EmitUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_EmitUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_EmitUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_EmitUtil(builtin);
}

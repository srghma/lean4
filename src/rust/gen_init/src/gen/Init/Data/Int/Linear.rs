// Lean compiler output
// Module: Init.Data.Int.Linear
// Imports: Init.Data.Int.Gcd Init.Data.AC Init.LawfulBEqTactics Init.Data.Bool Init.Data.Int.Gcd Init.Data.RArray Init.Data.Int.Cooper Init.Data.Int.LemmasAux
use crate::r#gen::Init::Data::AC::{initialize_Init_Data_AC, runtime_initialize_Init_Data_AC};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Int::Cooper::{
    initialize_Init_Data_Int_Cooper, runtime_initialize_Init_Data_Int_Cooper,
};
use crate::r#gen::Init::Data::Int::Gcd::{
    initialize_Init_Data_Int_Gcd, l_Int_gcd, runtime_initialize_Init_Data_Int_Gcd,
};
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt;
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, l_Lean_RArray_getImpl___redArg,
    runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::ffi::{lean_int_ediv, lean_int_emod};
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
static mut l_Int_Linear_instInhabitedExpr_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_instInhabitedExpr_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Int_Linear_instInhabitedExpr_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_instInhabitedExpr_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Int_Linear_instInhabitedExpr_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Int_Linear_instInhabitedExpr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int_Linear_instBEqExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_Linear_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_Linear_instBEqExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Int_Linear_instBEqExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_instBEqPoly___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_Linear_instBEqPoly_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_Linear_instBEqPoly___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instBEqPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Int_Linear_instBEqPoly: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_instBEqPoly___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Int_Linear_hugeFuel: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int_Linear_Expr_toPoly_x27___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Expr_toPoly_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Int_Linear_Expr_toPoly_x27___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Expr_toPoly_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Int_Linear_Var_denote(
    mut v_ctx_1166_: *mut crate::leanh::LeanObject,
    mut v_v_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1168_ = l_Lean_RArray_getImpl___redArg(v_ctx_1166_, v_v_1167_);
    return v___x_1168_;
}
pub unsafe fn l_Int_Linear_Var_denote___boxed(
    mut v_ctx_1169_: *mut crate::leanh::LeanObject,
    mut v_v_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Int_Linear_Var_denote(v_ctx_1169_, v_v_1170_);
    crate::leanh::lean_dec(v_v_1170_);
    crate::leanh::lean_dec_ref(v_ctx_1169_);
    return v_res_1171_;
}
pub unsafe fn l_Int_Linear_Expr_ctorIdx(
    mut v_x_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1172_) {
        0 => {
            let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1173_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1173_;
        }
        1 => {
            let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1174_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1174_;
        }
        2 => {
            let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1175_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1175_;
        }
        3 => {
            let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1176_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1176_;
        }
        4 => {
            let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1177_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1177_;
        }
        5 => {
            let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1178_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1178_;
        }
        _ => {
            let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1179_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1179_;
        }
    }
}
pub unsafe fn l_Int_Linear_Expr_ctorIdx___boxed(
    mut v_x_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Int_Linear_Expr_ctorIdx(v_x_1180_);
    crate::leanh::lean_dec_ref(v_x_1180_);
    return v_res_1181_;
}
pub unsafe fn l_Int_Linear_Expr_ctorElim___redArg(
    mut v_t_1182_: *mut crate::leanh::LeanObject,
    mut v_k_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1182_) {
        2 => {
            let mut v_a_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1184_ = crate::leanh::lean_ctor_get(v_t_1182_, 0);
            crate::leanh::lean_inc_ref(v_a_1184_);
            v_b_1185_ = crate::leanh::lean_ctor_get(v_t_1182_, 1);
            crate::leanh::lean_inc_ref(v_b_1185_);
            crate::leanh::lean_dec_ref_known(v_t_1182_, 2);
            v___x_1186_ = crate::leanh::lean_apply_2(v_k_1183_, v_a_1184_, v_b_1185_);
            return v___x_1186_;
        }
        3 => {
            let mut v_a_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1187_ = crate::leanh::lean_ctor_get(v_t_1182_, 0);
            crate::leanh::lean_inc_ref(v_a_1187_);
            v_b_1188_ = crate::leanh::lean_ctor_get(v_t_1182_, 1);
            crate::leanh::lean_inc_ref(v_b_1188_);
            crate::leanh::lean_dec_ref_known(v_t_1182_, 2);
            v___x_1189_ = crate::leanh::lean_apply_2(v_k_1183_, v_a_1187_, v_b_1188_);
            return v___x_1189_;
        }
        4 => {
            let mut v_a_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1190_ = crate::leanh::lean_ctor_get(v_t_1182_, 0);
            crate::leanh::lean_inc_ref(v_a_1190_);
            crate::leanh::lean_dec_ref_known(v_t_1182_, 1);
            v___x_1191_ = crate::leanh::lean_apply_1(v_k_1183_, v_a_1190_);
            return v___x_1191_;
        }
        5 => {
            let mut v_k_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_1192_ = crate::leanh::lean_ctor_get(v_t_1182_, 0);
            crate::leanh::lean_inc(v_k_1192_);
            v_a_1193_ = crate::leanh::lean_ctor_get(v_t_1182_, 1);
            crate::leanh::lean_inc_ref(v_a_1193_);
            crate::leanh::lean_dec_ref_known(v_t_1182_, 2);
            v___x_1194_ = crate::leanh::lean_apply_2(v_k_1183_, v_k_1192_, v_a_1193_);
            return v___x_1194_;
        }
        6 => {
            let mut v_a_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1195_ = crate::leanh::lean_ctor_get(v_t_1182_, 0);
            crate::leanh::lean_inc_ref(v_a_1195_);
            v_k_1196_ = crate::leanh::lean_ctor_get(v_t_1182_, 1);
            crate::leanh::lean_inc(v_k_1196_);
            crate::leanh::lean_dec_ref_known(v_t_1182_, 2);
            v___x_1197_ = crate::leanh::lean_apply_2(v_k_1183_, v_a_1195_, v_k_1196_);
            return v___x_1197_;
        }
        _ => {
            let mut v_v_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_1198_ = crate::leanh::lean_ctor_get(v_t_1182_, 0);
            crate::leanh::lean_inc(v_v_1198_);
            crate::leanh::lean_dec_ref(v_t_1182_);
            v___x_1199_ = crate::leanh::lean_apply_1(v_k_1183_, v_v_1198_);
            return v___x_1199_;
        }
    }
}
pub unsafe fn l_Int_Linear_Expr_ctorElim(
    mut v_motive_1200_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1201_: *mut crate::leanh::LeanObject,
    mut v_t_1202_: *mut crate::leanh::LeanObject,
    mut v_h_1203_: *mut crate::leanh::LeanObject,
    mut v_k_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1202_, v_k_1204_);
    return v___x_1205_;
}
pub unsafe fn l_Int_Linear_Expr_ctorElim___boxed(
    mut v_motive_1206_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1207_: *mut crate::leanh::LeanObject,
    mut v_t_1208_: *mut crate::leanh::LeanObject,
    mut v_h_1209_: *mut crate::leanh::LeanObject,
    mut v_k_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Int_Linear_Expr_ctorElim(
        v_motive_1206_,
        v_ctorIdx_1207_,
        v_t_1208_,
        v_h_1209_,
        v_k_1210_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1207_);
    return v_res_1211_;
}
pub unsafe fn l_Int_Linear_Expr_num_elim___redArg(
    mut v_t_1212_: *mut crate::leanh::LeanObject,
    mut v_num_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1212_, v_num_1213_);
    return v___x_1214_;
}
pub unsafe fn l_Int_Linear_Expr_num_elim(
    mut v_motive_1215_: *mut crate::leanh::LeanObject,
    mut v_t_1216_: *mut crate::leanh::LeanObject,
    mut v_h_1217_: *mut crate::leanh::LeanObject,
    mut v_num_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1216_, v_num_1218_);
    return v___x_1219_;
}
pub unsafe fn l_Int_Linear_Expr_var_elim___redArg(
    mut v_t_1220_: *mut crate::leanh::LeanObject,
    mut v_var_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1220_, v_var_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Int_Linear_Expr_var_elim(
    mut v_motive_1223_: *mut crate::leanh::LeanObject,
    mut v_t_1224_: *mut crate::leanh::LeanObject,
    mut v_h_1225_: *mut crate::leanh::LeanObject,
    mut v_var_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1224_, v_var_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Int_Linear_Expr_add_elim___redArg(
    mut v_t_1228_: *mut crate::leanh::LeanObject,
    mut v_add_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1228_, v_add_1229_);
    return v___x_1230_;
}
pub unsafe fn l_Int_Linear_Expr_add_elim(
    mut v_motive_1231_: *mut crate::leanh::LeanObject,
    mut v_t_1232_: *mut crate::leanh::LeanObject,
    mut v_h_1233_: *mut crate::leanh::LeanObject,
    mut v_add_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1232_, v_add_1234_);
    return v___x_1235_;
}
pub unsafe fn l_Int_Linear_Expr_sub_elim___redArg(
    mut v_t_1236_: *mut crate::leanh::LeanObject,
    mut v_sub_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1236_, v_sub_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Int_Linear_Expr_sub_elim(
    mut v_motive_1239_: *mut crate::leanh::LeanObject,
    mut v_t_1240_: *mut crate::leanh::LeanObject,
    mut v_h_1241_: *mut crate::leanh::LeanObject,
    mut v_sub_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1240_, v_sub_1242_);
    return v___x_1243_;
}
pub unsafe fn l_Int_Linear_Expr_neg_elim___redArg(
    mut v_t_1244_: *mut crate::leanh::LeanObject,
    mut v_neg_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1244_, v_neg_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Int_Linear_Expr_neg_elim(
    mut v_motive_1247_: *mut crate::leanh::LeanObject,
    mut v_t_1248_: *mut crate::leanh::LeanObject,
    mut v_h_1249_: *mut crate::leanh::LeanObject,
    mut v_neg_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1248_, v_neg_1250_);
    return v___x_1251_;
}
pub unsafe fn l_Int_Linear_Expr_mulL_elim___redArg(
    mut v_t_1252_: *mut crate::leanh::LeanObject,
    mut v_mulL_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1252_, v_mulL_1253_);
    return v___x_1254_;
}
pub unsafe fn l_Int_Linear_Expr_mulL_elim(
    mut v_motive_1255_: *mut crate::leanh::LeanObject,
    mut v_t_1256_: *mut crate::leanh::LeanObject,
    mut v_h_1257_: *mut crate::leanh::LeanObject,
    mut v_mulL_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1259_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1256_, v_mulL_1258_);
    return v___x_1259_;
}
pub unsafe fn l_Int_Linear_Expr_mulR_elim___redArg(
    mut v_t_1260_: *mut crate::leanh::LeanObject,
    mut v_mulR_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1260_, v_mulR_1261_);
    return v___x_1262_;
}
pub unsafe fn l_Int_Linear_Expr_mulR_elim(
    mut v_motive_1263_: *mut crate::leanh::LeanObject,
    mut v_t_1264_: *mut crate::leanh::LeanObject,
    mut v_h_1265_: *mut crate::leanh::LeanObject,
    mut v_mulR_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_1264_, v_mulR_1266_);
    return v___x_1267_;
}
pub unsafe fn _init_l_Int_Linear_instInhabitedExpr_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1269_ = lean_nat_to_int(v___x_1268_);
    return v___x_1269_;
}
pub unsafe fn _init_l_Int_Linear_instInhabitedExpr_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
    );
    v___x_1271_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
    return v___x_1271_;
}
pub unsafe fn _init_l_Int_Linear_instInhabitedExpr_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__1),
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__1_once),
        _init_l_Int_Linear_instInhabitedExpr_default___closed__1,
    );
    return v___x_1272_;
}
pub unsafe fn _init_l_Int_Linear_instInhabitedExpr() -> *mut crate::leanh::LeanObject {
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Int_Linear_instInhabitedExpr_default;
    return v___x_1273_;
}
pub unsafe fn l_Int_Linear_instBEqExpr_beq(
    mut v_x_1274_: *mut crate::leanh::LeanObject,
    mut v_x_1275_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v_v_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: u8 = 0;
    let mut v_i_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: u8 = 0;
    let mut v___x_1290_: u8 = 0;
    let mut v_a_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v_a_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: u8 = 0;
    let mut v_a_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: u8 = 0;
    let mut v_k_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut v___x_1311_: u8 = 0;
    let mut v_a_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: u8 = 0;
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1274_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_1275_) == 0 {
                        v_v_1283_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_v_1284_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                        v___x_1285_ = lean_int_dec_eq(v_v_1283_, v_v_1284_);
                        return v___x_1285_;
                    } else {
                        v___x_1286_ = 0;
                        return v___x_1286_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_1275_) == 1 {
                        v_i_1287_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_i_1288_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                        v___x_1289_ = lean_nat_dec_eq(v_i_1287_, v_i_1288_);
                        return v___x_1289_;
                    } else {
                        v___x_1290_ = 0;
                        return v___x_1290_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_1275_) == 2 {
                        v_a_1291_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_b_1292_ = crate::leanh::lean_ctor_get(v_x_1274_, 1);
                        v_a_1293_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                        v_b_1294_ = crate::leanh::lean_ctor_get(v_x_1275_, 1);
                        v_a_1277_ = v_a_1291_;
                        v_a_1278_ = v_b_1292_;
                        v_b_1279_ = v_a_1293_;
                        v_b_1280_ = v_b_1294_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1295_ = 0;
                        return v___x_1295_;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_x_1275_) == 3 {
                        v_a_1296_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_b_1297_ = crate::leanh::lean_ctor_get(v_x_1274_, 1);
                        v_a_1298_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                        v_b_1299_ = crate::leanh::lean_ctor_get(v_x_1275_, 1);
                        v_a_1277_ = v_a_1296_;
                        v_a_1278_ = v_b_1297_;
                        v_b_1279_ = v_a_1298_;
                        v_b_1280_ = v_b_1299_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1300_ = 0;
                        return v___x_1300_;
                    }
                }
                4 => {
                    if crate::leanh::lean_obj_tag(v_x_1275_) == 4 {
                        v_a_1301_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_a_1302_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                        v_x_1274_ = v_a_1301_;
                        v_x_1275_ = v_a_1302_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1304_ = 0;
                        return v___x_1304_;
                    }
                }
                5 => {
                    if crate::leanh::lean_obj_tag(v_x_1275_) == 5 {
                        v_k_1305_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_a_1306_ = crate::leanh::lean_ctor_get(v_x_1274_, 1);
                        v_k_1307_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                        v_a_1308_ = crate::leanh::lean_ctor_get(v_x_1275_, 1);
                        v___x_1309_ = lean_int_dec_eq(v_k_1305_, v_k_1307_);
                        if v___x_1309_ == 0 {
                            return v___x_1309_;
                        } else {
                            v_x_1274_ = v_a_1306_;
                            v_x_1275_ = v_a_1308_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1311_ = 0;
                        return v___x_1311_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_1275_) == 6 {
                        v_a_1312_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_k_1313_ = crate::leanh::lean_ctor_get(v_x_1274_, 1);
                        v_a_1314_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                        v_k_1315_ = crate::leanh::lean_ctor_get(v_x_1275_, 1);
                        v___x_1316_ = l_Int_Linear_instBEqExpr_beq(v_a_1312_, v_a_1314_);
                        if v___x_1316_ == 0 {
                            return v___x_1316_;
                        } else {
                            v___x_1317_ = lean_int_dec_eq(v_k_1313_, v_k_1315_);
                            return v___x_1317_;
                        }
                    } else {
                        v___x_1318_ = 0;
                        return v___x_1318_;
                    }
                }
            },
            1 => {
                v___x_1281_ = l_Int_Linear_instBEqExpr_beq(v_a_1277_, v_b_1279_);
                if v___x_1281_ == 0 {
                    return v___x_1281_;
                } else {
                    v_x_1274_ = v_a_1278_;
                    v_x_1275_ = v_b_1280_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_instBEqExpr_beq___boxed(
    mut v_x_1319_: *mut crate::leanh::LeanObject,
    mut v_x_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1321_: u8 = 0;
    let mut v_r_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Int_Linear_instBEqExpr_beq(v_x_1319_, v_x_1320_);
    crate::leanh::lean_dec_ref(v_x_1320_);
    crate::leanh::lean_dec_ref(v_x_1319_);
    v_r_1322_ = crate::leanh::lean_box((v_res_1321_) as usize);
    return v_r_1322_;
}
pub unsafe fn l_Int_Linear_Expr_denote(
    mut v_ctx_1325_: *mut crate::leanh::LeanObject,
    mut v_x_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1326_) {
        0 => {
            let mut v_v_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_1327_ = crate::leanh::lean_ctor_get(v_x_1326_, 0);
            crate::leanh::lean_inc(v_v_1327_);
            return v_v_1327_;
        }
        1 => {
            let mut v_i_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_1328_ = crate::leanh::lean_ctor_get(v_x_1326_, 0);
            v___x_1329_ = l_Lean_RArray_getImpl___redArg(v_ctx_1325_, v_i_1328_);
            return v___x_1329_;
        }
        2 => {
            let mut v_a_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1330_ = crate::leanh::lean_ctor_get(v_x_1326_, 0);
            v_b_1331_ = crate::leanh::lean_ctor_get(v_x_1326_, 1);
            v___x_1332_ = l_Int_Linear_Expr_denote(v_ctx_1325_, v_a_1330_);
            v___x_1333_ = l_Int_Linear_Expr_denote(v_ctx_1325_, v_b_1331_);
            v___x_1334_ = lean_int_add(v___x_1332_, v___x_1333_);
            crate::leanh::lean_dec(v___x_1333_);
            crate::leanh::lean_dec(v___x_1332_);
            return v___x_1334_;
        }
        3 => {
            let mut v_a_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1335_ = crate::leanh::lean_ctor_get(v_x_1326_, 0);
            v_b_1336_ = crate::leanh::lean_ctor_get(v_x_1326_, 1);
            v___x_1337_ = l_Int_Linear_Expr_denote(v_ctx_1325_, v_a_1335_);
            v___x_1338_ = l_Int_Linear_Expr_denote(v_ctx_1325_, v_b_1336_);
            v___x_1339_ = lean_int_sub(v___x_1337_, v___x_1338_);
            crate::leanh::lean_dec(v___x_1338_);
            crate::leanh::lean_dec(v___x_1337_);
            return v___x_1339_;
        }
        4 => {
            let mut v_a_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1340_ = crate::leanh::lean_ctor_get(v_x_1326_, 0);
            v___x_1341_ = l_Int_Linear_Expr_denote(v_ctx_1325_, v_a_1340_);
            v___x_1342_ = lean_int_neg(v___x_1341_);
            crate::leanh::lean_dec(v___x_1341_);
            return v___x_1342_;
        }
        5 => {
            let mut v_k_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_1343_ = crate::leanh::lean_ctor_get(v_x_1326_, 0);
            v_a_1344_ = crate::leanh::lean_ctor_get(v_x_1326_, 1);
            v___x_1345_ = l_Int_Linear_Expr_denote(v_ctx_1325_, v_a_1344_);
            v___x_1346_ = lean_int_mul(v_k_1343_, v___x_1345_);
            crate::leanh::lean_dec(v___x_1345_);
            return v___x_1346_;
        }
        _ => {
            let mut v_a_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1347_ = crate::leanh::lean_ctor_get(v_x_1326_, 0);
            v_k_1348_ = crate::leanh::lean_ctor_get(v_x_1326_, 1);
            v___x_1349_ = l_Int_Linear_Expr_denote(v_ctx_1325_, v_a_1347_);
            v___x_1350_ = lean_int_mul(v___x_1349_, v_k_1348_);
            crate::leanh::lean_dec(v___x_1349_);
            return v___x_1350_;
        }
    }
}
pub unsafe fn l_Int_Linear_Expr_denote___boxed(
    mut v_ctx_1351_: *mut crate::leanh::LeanObject,
    mut v_x_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1353_ = l_Int_Linear_Expr_denote(v_ctx_1351_, v_x_1352_);
    crate::leanh::lean_dec_ref(v_x_1352_);
    crate::leanh::lean_dec_ref(v_ctx_1351_);
    return v_res_1353_;
}
pub unsafe fn l_Int_Linear_Poly_ctorIdx(
    mut v_x_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1354_) == 0 {
        let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1355_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1355_;
    } else {
        let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1356_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1356_;
    }
}
pub unsafe fn l_Int_Linear_Poly_ctorIdx___boxed(
    mut v_x_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Int_Linear_Poly_ctorIdx(v_x_1357_);
    crate::leanh::lean_dec_ref(v_x_1357_);
    return v_res_1358_;
}
pub unsafe fn l_Int_Linear_Poly_ctorElim___redArg(
    mut v_t_1359_: *mut crate::leanh::LeanObject,
    mut v_k_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1359_) == 0 {
        let mut v_k_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1361_ = crate::leanh::lean_ctor_get(v_t_1359_, 0);
        crate::leanh::lean_inc(v_k_1361_);
        crate::leanh::lean_dec_ref_known(v_t_1359_, 1);
        v___x_1362_ = crate::leanh::lean_apply_1(v_k_1360_, v_k_1361_);
        return v___x_1362_;
    } else {
        let mut v_k_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1363_ = crate::leanh::lean_ctor_get(v_t_1359_, 0);
        crate::leanh::lean_inc(v_k_1363_);
        v_v_1364_ = crate::leanh::lean_ctor_get(v_t_1359_, 1);
        crate::leanh::lean_inc(v_v_1364_);
        v_p_1365_ = crate::leanh::lean_ctor_get(v_t_1359_, 2);
        crate::leanh::lean_inc_ref(v_p_1365_);
        crate::leanh::lean_dec_ref_known(v_t_1359_, 3);
        v___x_1366_ = crate::leanh::lean_apply_3(v_k_1360_, v_k_1363_, v_v_1364_, v_p_1365_);
        return v___x_1366_;
    }
}
pub unsafe fn l_Int_Linear_Poly_ctorElim(
    mut v_motive_1367_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1368_: *mut crate::leanh::LeanObject,
    mut v_t_1369_: *mut crate::leanh::LeanObject,
    mut v_h_1370_: *mut crate::leanh::LeanObject,
    mut v_k_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_1369_, v_k_1371_);
    return v___x_1372_;
}
pub unsafe fn l_Int_Linear_Poly_ctorElim___boxed(
    mut v_motive_1373_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1374_: *mut crate::leanh::LeanObject,
    mut v_t_1375_: *mut crate::leanh::LeanObject,
    mut v_h_1376_: *mut crate::leanh::LeanObject,
    mut v_k_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1378_ = l_Int_Linear_Poly_ctorElim(
        v_motive_1373_,
        v_ctorIdx_1374_,
        v_t_1375_,
        v_h_1376_,
        v_k_1377_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1374_);
    return v_res_1378_;
}
pub unsafe fn l_Int_Linear_Poly_num_elim___redArg(
    mut v_t_1379_: *mut crate::leanh::LeanObject,
    mut v_num_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_1379_, v_num_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Int_Linear_Poly_num_elim(
    mut v_motive_1382_: *mut crate::leanh::LeanObject,
    mut v_t_1383_: *mut crate::leanh::LeanObject,
    mut v_h_1384_: *mut crate::leanh::LeanObject,
    mut v_num_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_1383_, v_num_1385_);
    return v___x_1386_;
}
pub unsafe fn l_Int_Linear_Poly_add_elim___redArg(
    mut v_t_1387_: *mut crate::leanh::LeanObject,
    mut v_add_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_1387_, v_add_1388_);
    return v___x_1389_;
}
pub unsafe fn l_Int_Linear_Poly_add_elim(
    mut v_motive_1390_: *mut crate::leanh::LeanObject,
    mut v_t_1391_: *mut crate::leanh::LeanObject,
    mut v_h_1392_: *mut crate::leanh::LeanObject,
    mut v_add_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_1391_, v_add_1393_);
    return v___x_1394_;
}
pub unsafe fn l_Int_Linear_instBEqPoly_beq(
    mut v_x_1395_: *mut crate::leanh::LeanObject,
    mut v_x_1396_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: u8 = 0;
    let mut v_k_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1395_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_1396_) == 0 {
                        v_k_1397_ = crate::leanh::lean_ctor_get(v_x_1395_, 0);
                        v_k_1398_ = crate::leanh::lean_ctor_get(v_x_1396_, 0);
                        v___x_1399_ = lean_int_dec_eq(v_k_1397_, v_k_1398_);
                        return v___x_1399_;
                    } else {
                        v___x_1400_ = 0;
                        return v___x_1400_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1396_) == 1 {
                        v_k_1401_ = crate::leanh::lean_ctor_get(v_x_1395_, 0);
                        v_v_1402_ = crate::leanh::lean_ctor_get(v_x_1395_, 1);
                        v_p_1403_ = crate::leanh::lean_ctor_get(v_x_1395_, 2);
                        v_k_1404_ = crate::leanh::lean_ctor_get(v_x_1396_, 0);
                        v_v_1405_ = crate::leanh::lean_ctor_get(v_x_1396_, 1);
                        v_p_1406_ = crate::leanh::lean_ctor_get(v_x_1396_, 2);
                        v___x_1407_ = lean_int_dec_eq(v_k_1401_, v_k_1404_);
                        if v___x_1407_ == 0 {
                            return v___x_1407_;
                        } else {
                            v___x_1408_ = lean_nat_dec_eq(v_v_1402_, v_v_1405_);
                            if v___x_1408_ == 0 {
                                return v___x_1408_;
                            } else {
                                v_x_1395_ = v_p_1403_;
                                v_x_1396_ = v_p_1406_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v___x_1410_ = 0;
                        return v___x_1410_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_instBEqPoly_beq___boxed(
    mut v_x_1411_: *mut crate::leanh::LeanObject,
    mut v_x_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1413_: u8 = 0;
    let mut v_r_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_Int_Linear_instBEqPoly_beq(v_x_1411_, v_x_1412_);
    crate::leanh::lean_dec_ref(v_x_1412_);
    crate::leanh::lean_dec_ref(v_x_1411_);
    v_r_1414_ = crate::leanh::lean_box((v_res_1413_) as usize);
    return v_r_1414_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_instBEqPoly_beq_match__1_splitter___redArg(
    mut v_x_1417_: *mut crate::leanh::LeanObject,
    mut v_x_1418_: *mut crate::leanh::LeanObject,
    mut v_h__1_1419_: *mut crate::leanh::LeanObject,
    mut v_h__2_1420_: *mut crate::leanh::LeanObject,
    mut v_h__3_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1417_) == 0 {
        crate::leanh::lean_dec(v_h__2_1420_);
        if crate::leanh::lean_obj_tag(v_x_1418_) == 0 {
            let mut v_k_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1421_);
            v_k_1422_ = crate::leanh::lean_ctor_get(v_x_1417_, 0);
            crate::leanh::lean_inc(v_k_1422_);
            crate::leanh::lean_dec_ref_known(v_x_1417_, 1);
            v_k_1423_ = crate::leanh::lean_ctor_get(v_x_1418_, 0);
            crate::leanh::lean_inc(v_k_1423_);
            crate::leanh::lean_dec_ref_known(v_x_1418_, 1);
            v___x_1424_ = crate::leanh::lean_apply_2(v_h__1_1419_, v_k_1422_, v_k_1423_);
            return v___x_1424_;
        } else {
            let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1419_);
            v___x_1425_ = crate::leanh::lean_apply_4(
                v_h__3_1421_,
                v_x_1417_,
                v_x_1418_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1425_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_1419_);
        if crate::leanh::lean_obj_tag(v_x_1418_) == 1 {
            let mut v_k_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1421_);
            v_k_1426_ = crate::leanh::lean_ctor_get(v_x_1417_, 0);
            crate::leanh::lean_inc(v_k_1426_);
            v_v_1427_ = crate::leanh::lean_ctor_get(v_x_1417_, 1);
            crate::leanh::lean_inc(v_v_1427_);
            v_p_1428_ = crate::leanh::lean_ctor_get(v_x_1417_, 2);
            crate::leanh::lean_inc_ref(v_p_1428_);
            crate::leanh::lean_dec_ref_known(v_x_1417_, 3);
            v_k_1429_ = crate::leanh::lean_ctor_get(v_x_1418_, 0);
            crate::leanh::lean_inc(v_k_1429_);
            v_v_1430_ = crate::leanh::lean_ctor_get(v_x_1418_, 1);
            crate::leanh::lean_inc(v_v_1430_);
            v_p_1431_ = crate::leanh::lean_ctor_get(v_x_1418_, 2);
            crate::leanh::lean_inc_ref(v_p_1431_);
            crate::leanh::lean_dec_ref_known(v_x_1418_, 3);
            v___x_1432_ = crate::leanh::lean_apply_6(
                v_h__2_1420_,
                v_k_1426_,
                v_v_1427_,
                v_p_1428_,
                v_k_1429_,
                v_v_1430_,
                v_p_1431_,
            );
            return v___x_1432_;
        } else {
            let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1420_);
            v___x_1433_ = crate::leanh::lean_apply_4(
                v_h__3_1421_,
                v_x_1417_,
                v_x_1418_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1433_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_instBEqPoly_beq_match__1_splitter(
    mut v_motive_1434_: *mut crate::leanh::LeanObject,
    mut v_x_1435_: *mut crate::leanh::LeanObject,
    mut v_x_1436_: *mut crate::leanh::LeanObject,
    mut v_h__1_1437_: *mut crate::leanh::LeanObject,
    mut v_h__2_1438_: *mut crate::leanh::LeanObject,
    mut v_h__3_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1435_) == 0 {
        crate::leanh::lean_dec(v_h__2_1438_);
        if crate::leanh::lean_obj_tag(v_x_1436_) == 0 {
            let mut v_k_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1439_);
            v_k_1440_ = crate::leanh::lean_ctor_get(v_x_1435_, 0);
            crate::leanh::lean_inc(v_k_1440_);
            crate::leanh::lean_dec_ref_known(v_x_1435_, 1);
            v_k_1441_ = crate::leanh::lean_ctor_get(v_x_1436_, 0);
            crate::leanh::lean_inc(v_k_1441_);
            crate::leanh::lean_dec_ref_known(v_x_1436_, 1);
            v___x_1442_ = crate::leanh::lean_apply_2(v_h__1_1437_, v_k_1440_, v_k_1441_);
            return v___x_1442_;
        } else {
            let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1437_);
            v___x_1443_ = crate::leanh::lean_apply_4(
                v_h__3_1439_,
                v_x_1435_,
                v_x_1436_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1443_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_1437_);
        if crate::leanh::lean_obj_tag(v_x_1436_) == 1 {
            let mut v_k_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1439_);
            v_k_1444_ = crate::leanh::lean_ctor_get(v_x_1435_, 0);
            crate::leanh::lean_inc(v_k_1444_);
            v_v_1445_ = crate::leanh::lean_ctor_get(v_x_1435_, 1);
            crate::leanh::lean_inc(v_v_1445_);
            v_p_1446_ = crate::leanh::lean_ctor_get(v_x_1435_, 2);
            crate::leanh::lean_inc_ref(v_p_1446_);
            crate::leanh::lean_dec_ref_known(v_x_1435_, 3);
            v_k_1447_ = crate::leanh::lean_ctor_get(v_x_1436_, 0);
            crate::leanh::lean_inc(v_k_1447_);
            v_v_1448_ = crate::leanh::lean_ctor_get(v_x_1436_, 1);
            crate::leanh::lean_inc(v_v_1448_);
            v_p_1449_ = crate::leanh::lean_ctor_get(v_x_1436_, 2);
            crate::leanh::lean_inc_ref(v_p_1449_);
            crate::leanh::lean_dec_ref_known(v_x_1436_, 3);
            v___x_1450_ = crate::leanh::lean_apply_6(
                v_h__2_1438_,
                v_k_1444_,
                v_v_1445_,
                v_p_1446_,
                v_k_1447_,
                v_v_1448_,
                v_p_1449_,
            );
            return v___x_1450_;
        } else {
            let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1438_);
            v___x_1451_ = crate::leanh::lean_apply_4(
                v_h__3_1439_,
                v_x_1435_,
                v_x_1436_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1451_;
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_denote(
    mut v_ctx_1452_: *mut crate::leanh::LeanObject,
    mut v_p_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1453_) == 0 {
        let mut v_k_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1454_ = crate::leanh::lean_ctor_get(v_p_1453_, 0);
        crate::leanh::lean_inc(v_k_1454_);
        return v_k_1454_;
    } else {
        let mut v_k_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1455_ = crate::leanh::lean_ctor_get(v_p_1453_, 0);
        v_v_1456_ = crate::leanh::lean_ctor_get(v_p_1453_, 1);
        v_p_1457_ = crate::leanh::lean_ctor_get(v_p_1453_, 2);
        v___x_1458_ = l_Lean_RArray_getImpl___redArg(v_ctx_1452_, v_v_1456_);
        v___x_1459_ = lean_int_mul(v_k_1455_, v___x_1458_);
        crate::leanh::lean_dec(v___x_1458_);
        v___x_1460_ = l_Int_Linear_Poly_denote(v_ctx_1452_, v_p_1457_);
        v___x_1461_ = lean_int_add(v___x_1459_, v___x_1460_);
        crate::leanh::lean_dec(v___x_1460_);
        crate::leanh::lean_dec(v___x_1459_);
        return v___x_1461_;
    }
}
pub unsafe fn l_Int_Linear_Poly_denote___boxed(
    mut v_ctx_1462_: *mut crate::leanh::LeanObject,
    mut v_p_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1464_ = l_Int_Linear_Poly_denote(v_ctx_1462_, v_p_1463_);
    crate::leanh::lean_dec_ref(v_p_1463_);
    crate::leanh::lean_dec_ref(v_ctx_1462_);
    return v_res_1464_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter___redArg(
    mut v_p_1465_: *mut crate::leanh::LeanObject,
    mut v_h__1_1466_: *mut crate::leanh::LeanObject,
    mut v_h__2_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1465_) == 0 {
        let mut v_k_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1467_);
        v_k_1468_ = crate::leanh::lean_ctor_get(v_p_1465_, 0);
        crate::leanh::lean_inc(v_k_1468_);
        crate::leanh::lean_dec_ref_known(v_p_1465_, 1);
        v___x_1469_ = crate::leanh::lean_apply_1(v_h__1_1466_, v_k_1468_);
        return v___x_1469_;
    } else {
        let mut v_k_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1466_);
        v_k_1470_ = crate::leanh::lean_ctor_get(v_p_1465_, 0);
        crate::leanh::lean_inc(v_k_1470_);
        v_v_1471_ = crate::leanh::lean_ctor_get(v_p_1465_, 1);
        crate::leanh::lean_inc(v_v_1471_);
        v_p_1472_ = crate::leanh::lean_ctor_get(v_p_1465_, 2);
        crate::leanh::lean_inc_ref(v_p_1472_);
        crate::leanh::lean_dec_ref_known(v_p_1465_, 3);
        v___x_1473_ = crate::leanh::lean_apply_3(v_h__2_1467_, v_k_1470_, v_v_1471_, v_p_1472_);
        return v___x_1473_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter(
    mut v_motive_1474_: *mut crate::leanh::LeanObject,
    mut v_p_1475_: *mut crate::leanh::LeanObject,
    mut v_h__1_1476_: *mut crate::leanh::LeanObject,
    mut v_h__2_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1475_) == 0 {
        let mut v_k_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1477_);
        v_k_1478_ = crate::leanh::lean_ctor_get(v_p_1475_, 0);
        crate::leanh::lean_inc(v_k_1478_);
        crate::leanh::lean_dec_ref_known(v_p_1475_, 1);
        v___x_1479_ = crate::leanh::lean_apply_1(v_h__1_1476_, v_k_1478_);
        return v___x_1479_;
    } else {
        let mut v_k_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1476_);
        v_k_1480_ = crate::leanh::lean_ctor_get(v_p_1475_, 0);
        crate::leanh::lean_inc(v_k_1480_);
        v_v_1481_ = crate::leanh::lean_ctor_get(v_p_1475_, 1);
        crate::leanh::lean_inc(v_v_1481_);
        v_p_1482_ = crate::leanh::lean_ctor_get(v_p_1475_, 2);
        crate::leanh::lean_inc_ref(v_p_1482_);
        crate::leanh::lean_dec_ref_known(v_p_1475_, 3);
        v___x_1483_ = crate::leanh::lean_apply_3(v_h__2_1477_, v_k_1480_, v_v_1481_, v_p_1482_);
        return v___x_1483_;
    }
}
pub unsafe fn l_Int_Linear_Poly_addConst(
    mut v_p_1484_: *mut crate::leanh::LeanObject,
    mut v_k_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1489_: u8 = 0;
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v_k_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_1484_) == 0 {
                    v_k_1486_ = crate::leanh::lean_ctor_get(v_p_1484_, 0);
                    v_isSharedCheck_1494_ = (!crate::leanh::lean_is_exclusive(v_p_1484_)) as u8;
                    if v_isSharedCheck_1494_ == 0 {
                        v___x_1488_ = v_p_1484_;
                        v_isShared_1489_ = v_isSharedCheck_1494_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_1486_);
                        crate::leanh::lean_dec(v_p_1484_);
                        v___x_1488_ = crate::leanh::lean_box(0);
                        v_isShared_1489_ = v_isSharedCheck_1494_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_1495_ = crate::leanh::lean_ctor_get(v_p_1484_, 0);
                    v_v_1496_ = crate::leanh::lean_ctor_get(v_p_1484_, 1);
                    v_p_1497_ = crate::leanh::lean_ctor_get(v_p_1484_, 2);
                    v_isSharedCheck_1505_ = (!crate::leanh::lean_is_exclusive(v_p_1484_)) as u8;
                    if v_isSharedCheck_1505_ == 0 {
                        v___x_1499_ = v_p_1484_;
                        v_isShared_1500_ = v_isSharedCheck_1505_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_1497_);
                        crate::leanh::lean_inc(v_v_1496_);
                        crate::leanh::lean_inc(v_k_1495_);
                        crate::leanh::lean_dec(v_p_1484_);
                        v___x_1499_ = crate::leanh::lean_box(0);
                        v_isShared_1500_ = v_isSharedCheck_1505_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1490_ = lean_int_add(v_k_1485_, v_k_1486_);
                crate::leanh::lean_dec(v_k_1486_);
                if v_isShared_1489_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1488_, 0, v___x_1490_);
                    v___x_1492_ = v___x_1488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1492_;
            }
            3 => {
                v___x_1501_ = l_Int_Linear_Poly_addConst(v_p_1497_, v_k_1485_);
                if v_isShared_1500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1499_, 2, v___x_1501_);
                    v___x_1503_ = v___x_1499_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1504_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_k_1495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_v_1496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 2, v___x_1501_);
                    v___x_1503_ = v_reuseFailAlloc_1504_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_addConst___boxed(
    mut v_p_1506_: *mut crate::leanh::LeanObject,
    mut v_k_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Int_Linear_Poly_addConst(v_p_1506_, v_k_1507_);
    crate::leanh::lean_dec(v_k_1507_);
    return v_res_1508_;
}
pub unsafe fn l_Int_Linear_Poly_insert(
    mut v_k_1509_: *mut crate::leanh::LeanObject,
    mut v_v_1510_: *mut crate::leanh::LeanObject,
    mut v_p_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_unused_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_1511_) == 0 {
                    v___x_1512_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1512_, 0, v_k_1509_);
                    crate::leanh::lean_ctor_set(v___x_1512_, 1, v_v_1510_);
                    crate::leanh::lean_ctor_set(v___x_1512_, 2, v_p_1511_);
                    return v___x_1512_;
                } else {
                    v_k_1513_ = crate::leanh::lean_ctor_get(v_p_1511_, 0);
                    v_v_1514_ = crate::leanh::lean_ctor_get(v_p_1511_, 1);
                    v_p_1515_ = crate::leanh::lean_ctor_get(v_p_1511_, 2);
                    v___x_1516_ = l_Nat_blt(v_v_1514_, v_v_1510_);
                    if v___x_1516_ == 0 {
                        crate::leanh::lean_inc_ref(v_p_1515_);
                        crate::leanh::lean_inc(v_v_1514_);
                        crate::leanh::lean_inc(v_k_1513_);
                        v_isSharedCheck_1531_ = (!crate::leanh::lean_is_exclusive(v_p_1511_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v_unused_1532_ = crate::leanh::lean_ctor_get(v_p_1511_, 2);
                            crate::leanh::lean_dec(v_unused_1532_);
                            v_unused_1533_ = crate::leanh::lean_ctor_get(v_p_1511_, 1);
                            crate::leanh::lean_dec(v_unused_1533_);
                            v_unused_1534_ = crate::leanh::lean_ctor_get(v_p_1511_, 0);
                            crate::leanh::lean_dec(v_unused_1534_);
                            v___x_1518_ = v_p_1511_;
                            v_isShared_1519_ = v_isSharedCheck_1531_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_p_1511_);
                            v___x_1518_ = crate::leanh::lean_box(0);
                            v_isShared_1519_ = v_isSharedCheck_1531_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1535_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1535_, 0, v_k_1509_);
                        crate::leanh::lean_ctor_set(v___x_1535_, 1, v_v_1510_);
                        crate::leanh::lean_ctor_set(v___x_1535_, 2, v_p_1511_);
                        return v___x_1535_;
                    }
                }
            }
            1 => {
                v___x_1520_ = lean_nat_dec_eq(v_v_1510_, v_v_1514_);
                if v___x_1520_ == 0 {
                    v___x_1521_ = l_Int_Linear_Poly_insert(v_k_1509_, v_v_1510_, v_p_1515_);
                    if v_isShared_1519_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1518_, 2, v___x_1521_);
                        v___x_1523_ = v___x_1518_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1524_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_k_1513_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_v_1514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v___x_1521_);
                        v___x_1523_ = v_reuseFailAlloc_1524_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_v_1510_);
                    v___x_1525_ = lean_int_add(v_k_1509_, v_k_1513_);
                    crate::leanh::lean_dec(v_k_1513_);
                    crate::leanh::lean_dec(v_k_1509_);
                    v___x_1526_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    v___x_1527_ = lean_int_dec_eq(v___x_1525_, v___x_1526_);
                    if v___x_1527_ == 0 {
                        if v_isShared_1519_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1525_);
                            v___x_1529_ = v___x_1518_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1530_ =
                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1525_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_v_1514_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_p_1515_);
                            v___x_1529_ = v_reuseFailAlloc_1530_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1525_);
                        crate::leanh::lean_del_object(v___x_1518_);
                        crate::leanh::lean_dec(v_v_1514_);
                        return v_p_1515_;
                    }
                }
            }
            2 => {
                return v___x_1523_;
            }
            3 => {
                return v___x_1529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_norm(
    mut v_p_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1536_) == 0 {
        return v_p_1536_;
    } else {
        let mut v_k_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1537_ = crate::leanh::lean_ctor_get(v_p_1536_, 0);
        crate::leanh::lean_inc(v_k_1537_);
        v_v_1538_ = crate::leanh::lean_ctor_get(v_p_1536_, 1);
        crate::leanh::lean_inc(v_v_1538_);
        v_p_1539_ = crate::leanh::lean_ctor_get(v_p_1536_, 2);
        crate::leanh::lean_inc_ref(v_p_1539_);
        crate::leanh::lean_dec_ref_known(v_p_1536_, 3);
        v___x_1540_ = l_Int_Linear_Poly_norm(v_p_1539_);
        v___x_1541_ = l_Int_Linear_Poly_insert(v_k_1537_, v_v_1538_, v___x_1540_);
        return v___x_1541_;
    }
}
pub unsafe fn l_Int_Linear_Poly_append(
    mut v_p_u2081_1542_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_1542_) == 0 {
                    v_k_1544_ = crate::leanh::lean_ctor_get(v_p_u2081_1542_, 0);
                    crate::leanh::lean_inc(v_k_1544_);
                    crate::leanh::lean_dec_ref_known(v_p_u2081_1542_, 1);
                    v___x_1545_ = l_Int_Linear_Poly_addConst(v_p_u2082_1543_, v_k_1544_);
                    crate::leanh::lean_dec(v_k_1544_);
                    return v___x_1545_;
                } else {
                    v_k_1546_ = crate::leanh::lean_ctor_get(v_p_u2081_1542_, 0);
                    v_v_1547_ = crate::leanh::lean_ctor_get(v_p_u2081_1542_, 1);
                    v_p_1548_ = crate::leanh::lean_ctor_get(v_p_u2081_1542_, 2);
                    v_isSharedCheck_1556_ =
                        (!crate::leanh::lean_is_exclusive(v_p_u2081_1542_)) as u8;
                    if v_isSharedCheck_1556_ == 0 {
                        v___x_1550_ = v_p_u2081_1542_;
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_1548_);
                        crate::leanh::lean_inc(v_v_1547_);
                        crate::leanh::lean_inc(v_k_1546_);
                        crate::leanh::lean_dec(v_p_u2081_1542_);
                        v___x_1550_ = crate::leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1552_ = l_Int_Linear_Poly_append(v_p_1548_, v_p_u2082_1543_);
                if v_isShared_1551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1550_, 2, v___x_1552_);
                    v___x_1554_ = v___x_1550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_k_1546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_v_1547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 2, v___x_1552_);
                    v___x_1554_ = v_reuseFailAlloc_1555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_combine_x27(
    mut v_fuel_1557_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_1558_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1561_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_k_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut v_k_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut v_k_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_unused_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut v_unused_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v_a_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_unused_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1560_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1561_ = lean_nat_dec_eq(v_fuel_1557_, v_zero_1560_);
                if v_isZero_1561_ == 1 {
                    crate::leanh::lean_dec(v_fuel_1557_);
                    v___x_1562_ = l_Int_Linear_Poly_append(v_p_u2081_1558_, v_p_u2082_1559_);
                    return v___x_1562_;
                } else {
                    v_one_1563_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1564_ = lean_nat_sub(v_fuel_1557_, v_one_1563_);
                    crate::leanh::lean_dec(v_fuel_1557_);
                    if crate::leanh::lean_obj_tag(v_p_u2081_1558_) == 0 {
                        if crate::leanh::lean_obj_tag(v_p_u2082_1559_) == 0 {
                            crate::leanh::lean_dec(v_n_1564_);
                            v_k_1565_ = crate::leanh::lean_ctor_get(v_p_u2081_1558_, 0);
                            crate::leanh::lean_inc(v_k_1565_);
                            crate::leanh::lean_dec_ref_known(v_p_u2081_1558_, 1);
                            v_k_1566_ = crate::leanh::lean_ctor_get(v_p_u2082_1559_, 0);
                            v_isSharedCheck_1574_ =
                                (!crate::leanh::lean_is_exclusive(v_p_u2082_1559_)) as u8;
                            if v_isSharedCheck_1574_ == 0 {
                                v___x_1568_ = v_p_u2082_1559_;
                                v_isShared_1569_ = v_isSharedCheck_1574_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_1566_);
                                crate::leanh::lean_dec(v_p_u2082_1559_);
                                v___x_1568_ = crate::leanh::lean_box(0);
                                v_isShared_1569_ = v_isSharedCheck_1574_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_k_1575_ = crate::leanh::lean_ctor_get(v_p_u2082_1559_, 0);
                            v_v_1576_ = crate::leanh::lean_ctor_get(v_p_u2082_1559_, 1);
                            v_p_1577_ = crate::leanh::lean_ctor_get(v_p_u2082_1559_, 2);
                            v_isSharedCheck_1585_ =
                                (!crate::leanh::lean_is_exclusive(v_p_u2082_1559_)) as u8;
                            if v_isSharedCheck_1585_ == 0 {
                                v___x_1579_ = v_p_u2082_1559_;
                                v_isShared_1580_ = v_isSharedCheck_1585_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_p_1577_);
                                crate::leanh::lean_inc(v_v_1576_);
                                crate::leanh::lean_inc(v_k_1575_);
                                crate::leanh::lean_dec(v_p_u2082_1559_);
                                v___x_1579_ = crate::leanh::lean_box(0);
                                v_isShared_1580_ = v_isSharedCheck_1585_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_p_u2082_1559_) == 0 {
                            v_k_1586_ = crate::leanh::lean_ctor_get(v_p_u2081_1558_, 0);
                            v_v_1587_ = crate::leanh::lean_ctor_get(v_p_u2081_1558_, 1);
                            v_p_1588_ = crate::leanh::lean_ctor_get(v_p_u2081_1558_, 2);
                            v_isSharedCheck_1596_ =
                                (!crate::leanh::lean_is_exclusive(v_p_u2081_1558_)) as u8;
                            if v_isSharedCheck_1596_ == 0 {
                                v___x_1590_ = v_p_u2081_1558_;
                                v_isShared_1591_ = v_isSharedCheck_1596_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_p_1588_);
                                crate::leanh::lean_inc(v_v_1587_);
                                crate::leanh::lean_inc(v_k_1586_);
                                crate::leanh::lean_dec(v_p_u2081_1558_);
                                v___x_1590_ = crate::leanh::lean_box(0);
                                v_isShared_1591_ = v_isSharedCheck_1596_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_k_1597_ = crate::leanh::lean_ctor_get(v_p_u2081_1558_, 0);
                            v_v_1598_ = crate::leanh::lean_ctor_get(v_p_u2081_1558_, 1);
                            v_p_1599_ = crate::leanh::lean_ctor_get(v_p_u2081_1558_, 2);
                            v_k_1600_ = crate::leanh::lean_ctor_get(v_p_u2082_1559_, 0);
                            v_v_1601_ = crate::leanh::lean_ctor_get(v_p_u2082_1559_, 1);
                            v_p_1602_ = crate::leanh::lean_ctor_get(v_p_u2082_1559_, 2);
                            v___x_1603_ = lean_nat_dec_eq(v_v_1598_, v_v_1601_);
                            if v___x_1603_ == 0 {
                                v___x_1604_ = l_Nat_blt(v_v_1601_, v_v_1598_);
                                if v___x_1604_ == 0 {
                                    crate::leanh::lean_inc_ref(v_p_1602_);
                                    crate::leanh::lean_inc(v_v_1601_);
                                    crate::leanh::lean_inc(v_k_1600_);
                                    v_isSharedCheck_1612_ =
                                        (!crate::leanh::lean_is_exclusive(v_p_u2082_1559_)) as u8;
                                    if v_isSharedCheck_1612_ == 0 {
                                        v_unused_1613_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_1559_, 2);
                                        crate::leanh::lean_dec(v_unused_1613_);
                                        v_unused_1614_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_1559_, 1);
                                        crate::leanh::lean_dec(v_unused_1614_);
                                        v_unused_1615_ =
                                            crate::leanh::lean_ctor_get(v_p_u2082_1559_, 0);
                                        crate::leanh::lean_dec(v_unused_1615_);
                                        v___x_1606_ = v_p_u2082_1559_;
                                        v_isShared_1607_ = v_isSharedCheck_1612_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_p_u2082_1559_);
                                        v___x_1606_ = crate::leanh::lean_box(0);
                                        v_isShared_1607_ = v_isSharedCheck_1612_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc_ref(v_p_1599_);
                                    crate::leanh::lean_inc(v_v_1598_);
                                    crate::leanh::lean_inc(v_k_1597_);
                                    v_isSharedCheck_1623_ =
                                        (!crate::leanh::lean_is_exclusive(v_p_u2081_1558_)) as u8;
                                    if v_isSharedCheck_1623_ == 0 {
                                        v_unused_1624_ =
                                            crate::leanh::lean_ctor_get(v_p_u2081_1558_, 2);
                                        crate::leanh::lean_dec(v_unused_1624_);
                                        v_unused_1625_ =
                                            crate::leanh::lean_ctor_get(v_p_u2081_1558_, 1);
                                        crate::leanh::lean_dec(v_unused_1625_);
                                        v_unused_1626_ =
                                            crate::leanh::lean_ctor_get(v_p_u2081_1558_, 0);
                                        crate::leanh::lean_dec(v_unused_1626_);
                                        v___x_1617_ = v_p_u2081_1558_;
                                        v_isShared_1618_ = v_isSharedCheck_1623_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_p_u2081_1558_);
                                        v___x_1617_ = crate::leanh::lean_box(0);
                                        v_isShared_1618_ = v_isSharedCheck_1623_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_inc_ref(v_p_1602_);
                                crate::leanh::lean_inc(v_k_1600_);
                                crate::leanh::lean_inc_ref(v_p_1599_);
                                crate::leanh::lean_inc(v_v_1598_);
                                crate::leanh::lean_inc(v_k_1597_);
                                crate::leanh::lean_dec_ref_known(v_p_u2081_1558_, 3);
                                v_isSharedCheck_1638_ =
                                    (!crate::leanh::lean_is_exclusive(v_p_u2082_1559_)) as u8;
                                if v_isSharedCheck_1638_ == 0 {
                                    v_unused_1639_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_1559_, 2);
                                    crate::leanh::lean_dec(v_unused_1639_);
                                    v_unused_1640_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_1559_, 1);
                                    crate::leanh::lean_dec(v_unused_1640_);
                                    v_unused_1641_ =
                                        crate::leanh::lean_ctor_get(v_p_u2082_1559_, 0);
                                    crate::leanh::lean_dec(v_unused_1641_);
                                    v___x_1628_ = v_p_u2082_1559_;
                                    v_isShared_1629_ = v_isSharedCheck_1638_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_p_u2082_1559_);
                                    v___x_1628_ = crate::leanh::lean_box(0);
                                    v_isShared_1629_ = v_isSharedCheck_1638_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1570_ = lean_int_add(v_k_1565_, v_k_1566_);
                crate::leanh::lean_dec(v_k_1566_);
                crate::leanh::lean_dec(v_k_1565_);
                if v_isShared_1569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1568_, 0, v___x_1570_);
                    v___x_1572_ = v___x_1568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
                    v___x_1572_ = v_reuseFailAlloc_1573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1572_;
            }
            3 => {
                v___x_1581_ = l_Int_Linear_Poly_combine_x27(v_n_1564_, v_p_u2081_1558_, v_p_1577_);
                if v_isShared_1580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1579_, 2, v___x_1581_);
                    v___x_1583_ = v___x_1579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_k_1575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_v_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 2, v___x_1581_);
                    v___x_1583_ = v_reuseFailAlloc_1584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1583_;
            }
            5 => {
                v___x_1592_ = l_Int_Linear_Poly_combine_x27(v_n_1564_, v_p_1588_, v_p_u2082_1559_);
                if v_isShared_1591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1590_, 2, v___x_1592_);
                    v___x_1594_ = v___x_1590_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_k_1586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_v_1587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 2, v___x_1592_);
                    v___x_1594_ = v_reuseFailAlloc_1595_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1594_;
            }
            7 => {
                v___x_1608_ = l_Int_Linear_Poly_combine_x27(v_n_1564_, v_p_u2081_1558_, v_p_1602_);
                if v_isShared_1607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1606_, 2, v___x_1608_);
                    v___x_1610_ = v___x_1606_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_k_1600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_v_1601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 2, v___x_1608_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1610_;
            }
            9 => {
                v___x_1619_ = l_Int_Linear_Poly_combine_x27(v_n_1564_, v_p_1599_, v_p_u2082_1559_);
                if v_isShared_1618_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1617_, 2, v___x_1619_);
                    v___x_1621_ = v___x_1617_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_k_1597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_v_1598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 2, v___x_1619_);
                    v___x_1621_ = v_reuseFailAlloc_1622_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1621_;
            }
            11 => {
                v_a_1630_ = lean_int_add(v_k_1597_, v_k_1600_);
                crate::leanh::lean_dec(v_k_1600_);
                crate::leanh::lean_dec(v_k_1597_);
                v___x_1631_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Int_Linear_instInhabitedExpr_default___closed__0_once
                    ),
                    _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                );
                v___x_1632_ = lean_int_dec_eq(v_a_1630_, v___x_1631_);
                if v___x_1632_ == 0 {
                    v___x_1633_ = l_Int_Linear_Poly_combine_x27(v_n_1564_, v_p_1599_, v_p_1602_);
                    if v_isShared_1629_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1628_, 2, v___x_1633_);
                        crate::leanh::lean_ctor_set(v___x_1628_, 1, v_v_1598_);
                        crate::leanh::lean_ctor_set(v___x_1628_, 0, v_a_1630_);
                        v___x_1635_ = v___x_1628_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1636_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_v_1598_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 2, v___x_1633_);
                        v___x_1635_ = v_reuseFailAlloc_1636_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1630_);
                    crate::leanh::lean_del_object(v___x_1628_);
                    crate::leanh::lean_dec(v_v_1598_);
                    v_fuel_1557_ = v_n_1564_;
                    v_p_u2081_1558_ = v_p_1599_;
                    v_p_u2082_1559_ = v_p_1602_;
                    state = 0;
                    continue;
                }
            }
            12 => {
                return v___x_1635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Int_Linear_hugeFuel() -> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = crate::leanh::lean_unsigned_to_nat(100000000);
    return v___x_1642_;
}
pub unsafe fn l_Int_Linear_Poly_combine(
    mut v_p_u2081_1643_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = crate::leanh::lean_unsigned_to_nat(100000000);
    v___x_1646_ = l_Int_Linear_Poly_combine_x27(v___x_1645_, v_p_u2081_1643_, v_p_u2082_1644_);
    return v___x_1646_;
}
pub unsafe fn l_Int_Linear_Expr_toPoly_x27_go(
    mut v_coeff_1647_: *mut crate::leanh::LeanObject,
    mut v_a_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: u8 = 0;
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_1648_) {
                0 => {
                    v_v_1650_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                    v___x_1651_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    v___x_1652_ = lean_int_dec_eq(v_v_1650_, v___x_1651_);
                    if v___x_1652_ == 0 {
                        v___x_1653_ = lean_int_mul(v_coeff_1647_, v_v_1650_);
                        crate::leanh::lean_dec(v_coeff_1647_);
                        v___x_1654_ = l_Int_Linear_Poly_addConst(v_a_1649_, v___x_1653_);
                        crate::leanh::lean_dec(v___x_1653_);
                        return v___x_1654_;
                    } else {
                        crate::leanh::lean_dec(v_coeff_1647_);
                        return v_a_1649_;
                    }
                }
                1 => {
                    v_i_1655_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                    crate::leanh::lean_inc(v_i_1655_);
                    v___x_1656_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1656_, 0, v_coeff_1647_);
                    crate::leanh::lean_ctor_set(v___x_1656_, 1, v_i_1655_);
                    crate::leanh::lean_ctor_set(v___x_1656_, 2, v_a_1649_);
                    return v___x_1656_;
                }
                2 => {
                    v_a_1657_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                    v_b_1658_ = crate::leanh::lean_ctor_get(v_a_1648_, 1);
                    crate::leanh::lean_inc(v_coeff_1647_);
                    v___x_1659_ =
                        l_Int_Linear_Expr_toPoly_x27_go(v_coeff_1647_, v_b_1658_, v_a_1649_);
                    v_a_1648_ = v_a_1657_;
                    v_a_1649_ = v___x_1659_;
                    state = 0;
                    continue;
                }
                3 => {
                    v_a_1661_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                    v_b_1662_ = crate::leanh::lean_ctor_get(v_a_1648_, 1);
                    v___x_1663_ = lean_int_neg(v_coeff_1647_);
                    v___x_1664_ =
                        l_Int_Linear_Expr_toPoly_x27_go(v___x_1663_, v_b_1662_, v_a_1649_);
                    v_a_1648_ = v_a_1661_;
                    v_a_1649_ = v___x_1664_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_a_1666_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                    v___x_1667_ = lean_int_neg(v_coeff_1647_);
                    crate::leanh::lean_dec(v_coeff_1647_);
                    v_coeff_1647_ = v___x_1667_;
                    v_a_1648_ = v_a_1666_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_k_1669_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                    v_a_1670_ = crate::leanh::lean_ctor_get(v_a_1648_, 1);
                    v___x_1671_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    v___x_1672_ = lean_int_dec_eq(v_k_1669_, v___x_1671_);
                    if v___x_1672_ == 0 {
                        v___x_1673_ = lean_int_mul(v_coeff_1647_, v_k_1669_);
                        crate::leanh::lean_dec(v_coeff_1647_);
                        v_coeff_1647_ = v___x_1673_;
                        v_a_1648_ = v_a_1670_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_coeff_1647_);
                        return v_a_1649_;
                    }
                }
                _ => {
                    v_a_1675_ = crate::leanh::lean_ctor_get(v_a_1648_, 0);
                    v_k_1676_ = crate::leanh::lean_ctor_get(v_a_1648_, 1);
                    v___x_1677_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    v___x_1678_ = lean_int_dec_eq(v_k_1676_, v___x_1677_);
                    if v___x_1678_ == 0 {
                        v___x_1679_ = lean_int_mul(v_coeff_1647_, v_k_1676_);
                        crate::leanh::lean_dec(v_coeff_1647_);
                        v_coeff_1647_ = v___x_1679_;
                        v_a_1648_ = v_a_1675_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_coeff_1647_);
                        return v_a_1649_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Expr_toPoly_x27_go___boxed(
    mut v_coeff_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
    mut v_a_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Int_Linear_Expr_toPoly_x27_go(v_coeff_1681_, v_a_1682_, v_a_1683_);
    crate::leanh::lean_dec_ref(v_a_1682_);
    return v_res_1684_;
}
pub unsafe fn _init_l_Int_Linear_Expr_toPoly_x27___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1686_ = lean_nat_to_int(v___x_1685_);
    return v___x_1686_;
}
pub unsafe fn _init_l_Int_Linear_Expr_toPoly_x27___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
    );
    v___x_1688_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Int_Linear_Expr_toPoly_x27(
    mut v_e_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0_once),
        _init_l_Int_Linear_Expr_toPoly_x27___closed__0,
    );
    v___x_1691_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__1),
        core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__1_once),
        _init_l_Int_Linear_Expr_toPoly_x27___closed__1,
    );
    v___x_1692_ = l_Int_Linear_Expr_toPoly_x27_go(v___x_1690_, v_e_1689_, v___x_1691_);
    return v___x_1692_;
}
pub unsafe fn l_Int_Linear_Expr_toPoly_x27___boxed(
    mut v_e_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_Int_Linear_Expr_toPoly_x27(v_e_1693_);
    crate::leanh::lean_dec_ref(v_e_1693_);
    return v_res_1694_;
}
pub unsafe fn l_Int_Linear_Expr_norm(
    mut v_e_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = l_Int_Linear_Expr_toPoly_x27(v_e_1695_);
    v___x_1697_ = l_Int_Linear_Poly_norm(v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn l_Int_Linear_Expr_norm___boxed(
    mut v_e_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1699_ = l_Int_Linear_Expr_norm(v_e_1698_);
    crate::leanh::lean_dec_ref(v_e_1698_);
    return v_res_1699_;
}
pub unsafe fn l_Int_Linear_cdiv(
    mut v_a_1700_: *mut crate::leanh::LeanObject,
    mut v_b_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = lean_int_neg(v_a_1700_);
    v___x_1703_ = lean_int_ediv(v___x_1702_, v_b_1701_);
    crate::leanh::lean_dec(v___x_1702_);
    v___x_1704_ = lean_int_neg(v___x_1703_);
    crate::leanh::lean_dec(v___x_1703_);
    return v___x_1704_;
}
pub unsafe fn l_Int_Linear_cdiv___boxed(
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_b_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Int_Linear_cdiv(v_a_1705_, v_b_1706_);
    crate::leanh::lean_dec(v_b_1706_);
    crate::leanh::lean_dec(v_a_1705_);
    return v_res_1707_;
}
pub unsafe fn l_Int_Linear_cmod(
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_b_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = lean_int_neg(v_a_1708_);
    v___x_1711_ = lean_int_emod(v___x_1710_, v_b_1709_);
    crate::leanh::lean_dec(v___x_1710_);
    v___x_1712_ = lean_int_neg(v___x_1711_);
    crate::leanh::lean_dec(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn l_Int_Linear_cmod___boxed(
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_b_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Int_Linear_cmod(v_a_1713_, v_b_1714_);
    crate::leanh::lean_dec(v_b_1714_);
    crate::leanh::lean_dec(v_a_1713_);
    return v_res_1715_;
}
pub unsafe fn l_Int_Linear_Poly_getConst(
    mut v_x_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1716_) == 0 {
                    v_k_1717_ = crate::leanh::lean_ctor_get(v_x_1716_, 0);
                    crate::leanh::lean_inc(v_k_1717_);
                    return v_k_1717_;
                } else {
                    v_p_1718_ = crate::leanh::lean_ctor_get(v_x_1716_, 2);
                    v_x_1716_ = v_p_1718_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_getConst___boxed(
    mut v_x_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Int_Linear_Poly_getConst(v_x_1720_);
    crate::leanh::lean_dec_ref(v_x_1720_);
    return v_res_1721_;
}
pub unsafe fn l_Int_Linear_Poly_div(
    mut v_k_1722_: *mut crate::leanh::LeanObject,
    mut v_x_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_k_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1723_) == 0 {
                    v_k_1724_ = crate::leanh::lean_ctor_get(v_x_1723_, 0);
                    v_isSharedCheck_1732_ = (!crate::leanh::lean_is_exclusive(v_x_1723_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1726_ = v_x_1723_;
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_1724_);
                        crate::leanh::lean_dec(v_x_1723_);
                        v___x_1726_ = crate::leanh::lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_1733_ = crate::leanh::lean_ctor_get(v_x_1723_, 0);
                    v_v_1734_ = crate::leanh::lean_ctor_get(v_x_1723_, 1);
                    v_p_1735_ = crate::leanh::lean_ctor_get(v_x_1723_, 2);
                    v_isSharedCheck_1744_ = (!crate::leanh::lean_is_exclusive(v_x_1723_)) as u8;
                    if v_isSharedCheck_1744_ == 0 {
                        v___x_1737_ = v_x_1723_;
                        v_isShared_1738_ = v_isSharedCheck_1744_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_1735_);
                        crate::leanh::lean_inc(v_v_1734_);
                        crate::leanh::lean_inc(v_k_1733_);
                        crate::leanh::lean_dec(v_x_1723_);
                        v___x_1737_ = crate::leanh::lean_box(0);
                        v_isShared_1738_ = v_isSharedCheck_1744_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1728_ = l_Int_Linear_cdiv(v_k_1724_, v_k_1722_);
                crate::leanh::lean_dec(v_k_1724_);
                if v_isShared_1727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1726_, 0, v___x_1728_);
                    v___x_1730_ = v___x_1726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1730_;
            }
            3 => {
                v___x_1739_ = lean_int_ediv(v_k_1733_, v_k_1722_);
                crate::leanh::lean_dec(v_k_1733_);
                v___x_1740_ = l_Int_Linear_Poly_div(v_k_1722_, v_p_1735_);
                if v_isShared_1738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1737_, 2, v___x_1740_);
                    crate::leanh::lean_ctor_set(v___x_1737_, 0, v___x_1739_);
                    v___x_1742_ = v___x_1737_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_v_1734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 2, v___x_1740_);
                    v___x_1742_ = v_reuseFailAlloc_1743_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_div___boxed(
    mut v_k_1745_: *mut crate::leanh::LeanObject,
    mut v_x_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Int_Linear_Poly_div(v_k_1745_, v_x_1746_);
    crate::leanh::lean_dec(v_k_1745_);
    return v_res_1747_;
}
pub unsafe fn l_Int_Linear_Poly_divAll(
    mut v_k_1748_: *mut crate::leanh::LeanObject,
    mut v_x_1749_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    let mut v_k_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1749_) == 0 {
                    v_k_1750_ = crate::leanh::lean_ctor_get(v_x_1749_, 0);
                    v___x_1751_ = lean_int_emod(v_k_1750_, v_k_1748_);
                    v___x_1752_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    v___x_1753_ = lean_int_dec_eq(v___x_1751_, v___x_1752_);
                    crate::leanh::lean_dec(v___x_1751_);
                    return v___x_1753_;
                } else {
                    v_k_1754_ = crate::leanh::lean_ctor_get(v_x_1749_, 0);
                    v_p_1755_ = crate::leanh::lean_ctor_get(v_x_1749_, 2);
                    v___x_1756_ = lean_int_emod(v_k_1754_, v_k_1748_);
                    v___x_1757_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    v___x_1758_ = lean_int_dec_eq(v___x_1756_, v___x_1757_);
                    crate::leanh::lean_dec(v___x_1756_);
                    if v___x_1758_ == 0 {
                        return v___x_1758_;
                    } else {
                        v_x_1749_ = v_p_1755_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_divAll___boxed(
    mut v_k_1760_: *mut crate::leanh::LeanObject,
    mut v_x_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1762_: u8 = 0;
    let mut v_r_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Int_Linear_Poly_divAll(v_k_1760_, v_x_1761_);
    crate::leanh::lean_dec_ref(v_x_1761_);
    crate::leanh::lean_dec(v_k_1760_);
    v_r_1763_ = crate::leanh::lean_box((v_res_1762_) as usize);
    return v_r_1763_;
}
pub unsafe fn l_Int_Linear_Poly_divCoeffs(
    mut v_k_1764_: *mut crate::leanh::LeanObject,
    mut v_x_1765_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1766_: u8 = 0;
    let mut v_k_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1765_) == 0 {
                    v___x_1766_ = 1;
                    return v___x_1766_;
                } else {
                    v_k_1767_ = crate::leanh::lean_ctor_get(v_x_1765_, 0);
                    v_p_1768_ = crate::leanh::lean_ctor_get(v_x_1765_, 2);
                    v___x_1769_ = lean_int_emod(v_k_1767_, v_k_1764_);
                    v___x_1770_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    v___x_1771_ = lean_int_dec_eq(v___x_1769_, v___x_1770_);
                    crate::leanh::lean_dec(v___x_1769_);
                    if v___x_1771_ == 0 {
                        return v___x_1771_;
                    } else {
                        v_x_1765_ = v_p_1768_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_divCoeffs___boxed(
    mut v_k_1773_: *mut crate::leanh::LeanObject,
    mut v_x_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1775_: u8 = 0;
    let mut v_r_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1775_ = l_Int_Linear_Poly_divCoeffs(v_k_1773_, v_x_1774_);
    crate::leanh::lean_dec_ref(v_x_1774_);
    crate::leanh::lean_dec(v_k_1773_);
    v_r_1776_ = crate::leanh::lean_box((v_res_1775_) as usize);
    return v_r_1776_;
}
pub unsafe fn l_Int_Linear_Poly_mul_x27(
    mut v_p_1777_: *mut crate::leanh::LeanObject,
    mut v_k_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut v_k_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_1777_) == 0 {
                    v_k_1779_ = crate::leanh::lean_ctor_get(v_p_1777_, 0);
                    v_isSharedCheck_1787_ = (!crate::leanh::lean_is_exclusive(v_p_1777_)) as u8;
                    if v_isSharedCheck_1787_ == 0 {
                        v___x_1781_ = v_p_1777_;
                        v_isShared_1782_ = v_isSharedCheck_1787_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_1779_);
                        crate::leanh::lean_dec(v_p_1777_);
                        v___x_1781_ = crate::leanh::lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1787_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_1788_ = crate::leanh::lean_ctor_get(v_p_1777_, 0);
                    v_v_1789_ = crate::leanh::lean_ctor_get(v_p_1777_, 1);
                    v_p_1790_ = crate::leanh::lean_ctor_get(v_p_1777_, 2);
                    v_isSharedCheck_1799_ = (!crate::leanh::lean_is_exclusive(v_p_1777_)) as u8;
                    if v_isSharedCheck_1799_ == 0 {
                        v___x_1792_ = v_p_1777_;
                        v_isShared_1793_ = v_isSharedCheck_1799_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_1790_);
                        crate::leanh::lean_inc(v_v_1789_);
                        crate::leanh::lean_inc(v_k_1788_);
                        crate::leanh::lean_dec(v_p_1777_);
                        v___x_1792_ = crate::leanh::lean_box(0);
                        v_isShared_1793_ = v_isSharedCheck_1799_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1783_ = lean_int_mul(v_k_1778_, v_k_1779_);
                crate::leanh::lean_dec(v_k_1779_);
                if v_isShared_1782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1781_, 0, v___x_1783_);
                    v___x_1785_ = v___x_1781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
                    v___x_1785_ = v_reuseFailAlloc_1786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1785_;
            }
            3 => {
                v___x_1794_ = lean_int_mul(v_k_1778_, v_k_1788_);
                crate::leanh::lean_dec(v_k_1788_);
                v___x_1795_ = l_Int_Linear_Poly_mul_x27(v_p_1790_, v_k_1778_);
                if v_isShared_1793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1792_, 2, v___x_1795_);
                    crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1794_);
                    v___x_1797_ = v___x_1792_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1798_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_v_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 2, v___x_1795_);
                    v___x_1797_ = v_reuseFailAlloc_1798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_mul_x27___boxed(
    mut v_p_1800_: *mut crate::leanh::LeanObject,
    mut v_k_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Int_Linear_Poly_mul_x27(v_p_1800_, v_k_1801_);
    crate::leanh::lean_dec(v_k_1801_);
    return v_res_1802_;
}
pub unsafe fn l_Int_Linear_Poly_mul(
    mut v_p_1803_: *mut crate::leanh::LeanObject,
    mut v_k_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    v___x_1805_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
    );
    v___x_1806_ = lean_int_dec_eq(v_k_1804_, v___x_1805_);
    if v___x_1806_ == 0 {
        let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1807_ = l_Int_Linear_Poly_mul_x27(v_p_1803_, v_k_1804_);
        return v___x_1807_;
    } else {
        let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_1803_);
        v___x_1808_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__1),
            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__1_once),
            _init_l_Int_Linear_Expr_toPoly_x27___closed__1,
        );
        return v___x_1808_;
    }
}
pub unsafe fn l_Int_Linear_Poly_mul___boxed(
    mut v_p_1809_: *mut crate::leanh::LeanObject,
    mut v_k_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1811_ = l_Int_Linear_Poly_mul(v_p_1809_, v_k_1810_);
    crate::leanh::lean_dec(v_k_1810_);
    return v_res_1811_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(
    mut v_fuel_1812_: *mut crate::leanh::LeanObject,
    mut v_h__1_1813_: *mut crate::leanh::LeanObject,
    mut v_h__2_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1816_: u8 = 0;
    v_zero_1815_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1816_ = lean_nat_dec_eq(v_fuel_1812_, v_zero_1815_);
    if v_isZero_1816_ == 1 {
        let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1814_);
        v___x_1817_ = crate::leanh::lean_box(0);
        v___x_1818_ = crate::leanh::lean_apply_1(v_h__1_1813_, v___x_1817_);
        return v___x_1818_;
    } else {
        let mut v_one_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1813_);
        v_one_1819_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1820_ = lean_nat_sub(v_fuel_1812_, v_one_1819_);
        v___x_1821_ = crate::leanh::lean_apply_1(v_h__2_1814_, v_n_1820_);
        return v___x_1821_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(
    mut v_fuel_1822_: *mut crate::leanh::LeanObject,
    mut v_h__1_1823_: *mut crate::leanh::LeanObject,
    mut v_h__2_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1825_ =
        l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(
            v_fuel_1822_,
            v_h__1_1823_,
            v_h__2_1824_,
        );
    crate::leanh::lean_dec(v_fuel_1822_);
    return v_res_1825_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(
    mut v_motive_1826_: *mut crate::leanh::LeanObject,
    mut v_fuel_1827_: *mut crate::leanh::LeanObject,
    mut v_h__1_1828_: *mut crate::leanh::LeanObject,
    mut v_h__2_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1831_: u8 = 0;
    v_zero_1830_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1831_ = lean_nat_dec_eq(v_fuel_1827_, v_zero_1830_);
    if v_isZero_1831_ == 1 {
        let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1829_);
        v___x_1832_ = crate::leanh::lean_box(0);
        v___x_1833_ = crate::leanh::lean_apply_1(v_h__1_1828_, v___x_1832_);
        return v___x_1833_;
    } else {
        let mut v_one_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1828_);
        v_one_1834_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1835_ = lean_nat_sub(v_fuel_1827_, v_one_1834_);
        v___x_1836_ = crate::leanh::lean_apply_1(v_h__2_1829_, v_n_1835_);
        return v___x_1836_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___boxed(
    mut v_motive_1837_: *mut crate::leanh::LeanObject,
    mut v_fuel_1838_: *mut crate::leanh::LeanObject,
    mut v_h__1_1839_: *mut crate::leanh::LeanObject,
    mut v_h__2_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(
        v_motive_1837_,
        v_fuel_1838_,
        v_h__1_1839_,
        v_h__2_1840_,
    );
    crate::leanh::lean_dec(v_fuel_1838_);
    return v_res_1841_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(
    mut v_p_u2081_1842_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_1843_: *mut crate::leanh::LeanObject,
    mut v_h__1_1844_: *mut crate::leanh::LeanObject,
    mut v_h__2_1845_: *mut crate::leanh::LeanObject,
    mut v_h__3_1846_: *mut crate::leanh::LeanObject,
    mut v_h__4_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_1842_) == 0 {
        crate::leanh::lean_dec(v_h__4_1847_);
        crate::leanh::lean_dec(v_h__3_1846_);
        if crate::leanh::lean_obj_tag(v_p_u2082_1843_) == 0 {
            let mut v_k_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1845_);
            v_k_1848_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 0);
            crate::leanh::lean_inc(v_k_1848_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1842_, 1);
            v_k_1849_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 0);
            crate::leanh::lean_inc(v_k_1849_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1843_, 1);
            v___x_1850_ = crate::leanh::lean_apply_2(v_h__1_1844_, v_k_1848_, v_k_1849_);
            return v___x_1850_;
        } else {
            let mut v_k_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1844_);
            v_k_1851_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 0);
            crate::leanh::lean_inc(v_k_1851_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1842_, 1);
            v_k_1852_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 0);
            crate::leanh::lean_inc(v_k_1852_);
            v_v_1853_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 1);
            crate::leanh::lean_inc(v_v_1853_);
            v_p_1854_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 2);
            crate::leanh::lean_inc_ref(v_p_1854_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1843_, 3);
            v___x_1855_ = crate::leanh::lean_apply_4(
                v_h__2_1845_,
                v_k_1851_,
                v_k_1852_,
                v_v_1853_,
                v_p_1854_,
            );
            return v___x_1855_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1845_);
        crate::leanh::lean_dec(v_h__1_1844_);
        if crate::leanh::lean_obj_tag(v_p_u2082_1843_) == 0 {
            let mut v_k_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1847_);
            v_k_1856_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 0);
            crate::leanh::lean_inc(v_k_1856_);
            v_v_1857_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 1);
            crate::leanh::lean_inc(v_v_1857_);
            v_p_1858_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 2);
            crate::leanh::lean_inc_ref(v_p_1858_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1842_, 3);
            v_k_1859_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 0);
            crate::leanh::lean_inc(v_k_1859_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1843_, 1);
            v___x_1860_ = crate::leanh::lean_apply_4(
                v_h__3_1846_,
                v_k_1856_,
                v_v_1857_,
                v_p_1858_,
                v_k_1859_,
            );
            return v___x_1860_;
        } else {
            let mut v_k_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1846_);
            v_k_1861_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 0);
            crate::leanh::lean_inc(v_k_1861_);
            v_v_1862_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 1);
            crate::leanh::lean_inc(v_v_1862_);
            v_p_1863_ = crate::leanh::lean_ctor_get(v_p_u2081_1842_, 2);
            crate::leanh::lean_inc_ref(v_p_1863_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1842_, 3);
            v_k_1864_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 0);
            crate::leanh::lean_inc(v_k_1864_);
            v_v_1865_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 1);
            crate::leanh::lean_inc(v_v_1865_);
            v_p_1866_ = crate::leanh::lean_ctor_get(v_p_u2082_1843_, 2);
            crate::leanh::lean_inc_ref(v_p_1866_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1843_, 3);
            v___x_1867_ = crate::leanh::lean_apply_6(
                v_h__4_1847_,
                v_k_1861_,
                v_v_1862_,
                v_p_1863_,
                v_k_1864_,
                v_v_1865_,
                v_p_1866_,
            );
            return v___x_1867_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter(
    mut v_motive_1868_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_1869_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_1870_: *mut crate::leanh::LeanObject,
    mut v_h__1_1871_: *mut crate::leanh::LeanObject,
    mut v_h__2_1872_: *mut crate::leanh::LeanObject,
    mut v_h__3_1873_: *mut crate::leanh::LeanObject,
    mut v_h__4_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_1869_) == 0 {
        crate::leanh::lean_dec(v_h__4_1874_);
        crate::leanh::lean_dec(v_h__3_1873_);
        if crate::leanh::lean_obj_tag(v_p_u2082_1870_) == 0 {
            let mut v_k_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1872_);
            v_k_1875_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 0);
            crate::leanh::lean_inc(v_k_1875_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1869_, 1);
            v_k_1876_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 0);
            crate::leanh::lean_inc(v_k_1876_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1870_, 1);
            v___x_1877_ = crate::leanh::lean_apply_2(v_h__1_1871_, v_k_1875_, v_k_1876_);
            return v___x_1877_;
        } else {
            let mut v_k_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1871_);
            v_k_1878_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 0);
            crate::leanh::lean_inc(v_k_1878_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1869_, 1);
            v_k_1879_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 0);
            crate::leanh::lean_inc(v_k_1879_);
            v_v_1880_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 1);
            crate::leanh::lean_inc(v_v_1880_);
            v_p_1881_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 2);
            crate::leanh::lean_inc_ref(v_p_1881_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1870_, 3);
            v___x_1882_ = crate::leanh::lean_apply_4(
                v_h__2_1872_,
                v_k_1878_,
                v_k_1879_,
                v_v_1880_,
                v_p_1881_,
            );
            return v___x_1882_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1872_);
        crate::leanh::lean_dec(v_h__1_1871_);
        if crate::leanh::lean_obj_tag(v_p_u2082_1870_) == 0 {
            let mut v_k_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1874_);
            v_k_1883_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 0);
            crate::leanh::lean_inc(v_k_1883_);
            v_v_1884_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 1);
            crate::leanh::lean_inc(v_v_1884_);
            v_p_1885_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 2);
            crate::leanh::lean_inc_ref(v_p_1885_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1869_, 3);
            v_k_1886_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 0);
            crate::leanh::lean_inc(v_k_1886_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1870_, 1);
            v___x_1887_ = crate::leanh::lean_apply_4(
                v_h__3_1873_,
                v_k_1883_,
                v_v_1884_,
                v_p_1885_,
                v_k_1886_,
            );
            return v___x_1887_;
        } else {
            let mut v_k_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1873_);
            v_k_1888_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 0);
            crate::leanh::lean_inc(v_k_1888_);
            v_v_1889_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 1);
            crate::leanh::lean_inc(v_v_1889_);
            v_p_1890_ = crate::leanh::lean_ctor_get(v_p_u2081_1869_, 2);
            crate::leanh::lean_inc_ref(v_p_1890_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_1869_, 3);
            v_k_1891_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 0);
            crate::leanh::lean_inc(v_k_1891_);
            v_v_1892_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 1);
            crate::leanh::lean_inc(v_v_1892_);
            v_p_1893_ = crate::leanh::lean_ctor_get(v_p_u2082_1870_, 2);
            crate::leanh::lean_inc_ref(v_p_1893_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_1870_, 3);
            v___x_1894_ = crate::leanh::lean_apply_6(
                v_h__4_1874_,
                v_k_1888_,
                v_v_1889_,
                v_p_1890_,
                v_k_1891_,
                v_v_1892_,
                v_p_1893_,
            );
            return v___x_1894_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(
    mut v_x_1895_: *mut crate::leanh::LeanObject,
    mut v_h__1_1896_: *mut crate::leanh::LeanObject,
    mut v_h__2_1897_: *mut crate::leanh::LeanObject,
    mut v_h__3_1898_: *mut crate::leanh::LeanObject,
    mut v_h__4_1899_: *mut crate::leanh::LeanObject,
    mut v_h__5_1900_: *mut crate::leanh::LeanObject,
    mut v_h__6_1901_: *mut crate::leanh::LeanObject,
    mut v_h__7_1902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1895_) {
        0 => {
            let mut v_v_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1902_);
            crate::leanh::lean_dec(v_h__6_1901_);
            crate::leanh::lean_dec(v_h__5_1900_);
            crate::leanh::lean_dec(v_h__3_1898_);
            crate::leanh::lean_dec(v_h__2_1897_);
            crate::leanh::lean_dec(v_h__1_1896_);
            v_v_1903_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
            crate::leanh::lean_inc(v_v_1903_);
            crate::leanh::lean_dec_ref_known(v_x_1895_, 1);
            v___x_1904_ = crate::leanh::lean_apply_1(v_h__4_1899_, v_v_1903_);
            return v___x_1904_;
        }
        1 => {
            let mut v_i_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1902_);
            crate::leanh::lean_dec(v_h__6_1901_);
            crate::leanh::lean_dec(v_h__4_1899_);
            crate::leanh::lean_dec(v_h__3_1898_);
            crate::leanh::lean_dec(v_h__2_1897_);
            crate::leanh::lean_dec(v_h__1_1896_);
            v_i_1905_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
            crate::leanh::lean_inc(v_i_1905_);
            crate::leanh::lean_dec_ref_known(v_x_1895_, 1);
            v___x_1906_ = crate::leanh::lean_apply_1(v_h__5_1900_, v_i_1905_);
            return v___x_1906_;
        }
        2 => {
            let mut v_a_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1902_);
            crate::leanh::lean_dec(v_h__6_1901_);
            crate::leanh::lean_dec(v_h__5_1900_);
            crate::leanh::lean_dec(v_h__4_1899_);
            crate::leanh::lean_dec(v_h__3_1898_);
            crate::leanh::lean_dec(v_h__2_1897_);
            v_a_1907_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
            crate::leanh::lean_inc_ref(v_a_1907_);
            v_b_1908_ = crate::leanh::lean_ctor_get(v_x_1895_, 1);
            crate::leanh::lean_inc_ref(v_b_1908_);
            crate::leanh::lean_dec_ref_known(v_x_1895_, 2);
            v___x_1909_ = crate::leanh::lean_apply_2(v_h__1_1896_, v_a_1907_, v_b_1908_);
            return v___x_1909_;
        }
        3 => {
            let mut v_a_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1902_);
            crate::leanh::lean_dec(v_h__6_1901_);
            crate::leanh::lean_dec(v_h__5_1900_);
            crate::leanh::lean_dec(v_h__4_1899_);
            crate::leanh::lean_dec(v_h__3_1898_);
            crate::leanh::lean_dec(v_h__1_1896_);
            v_a_1910_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
            crate::leanh::lean_inc_ref(v_a_1910_);
            v_b_1911_ = crate::leanh::lean_ctor_get(v_x_1895_, 1);
            crate::leanh::lean_inc_ref(v_b_1911_);
            crate::leanh::lean_dec_ref_known(v_x_1895_, 2);
            v___x_1912_ = crate::leanh::lean_apply_2(v_h__2_1897_, v_a_1910_, v_b_1911_);
            return v___x_1912_;
        }
        4 => {
            let mut v_a_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1902_);
            crate::leanh::lean_dec(v_h__6_1901_);
            crate::leanh::lean_dec(v_h__5_1900_);
            crate::leanh::lean_dec(v_h__4_1899_);
            crate::leanh::lean_dec(v_h__2_1897_);
            crate::leanh::lean_dec(v_h__1_1896_);
            v_a_1913_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
            crate::leanh::lean_inc_ref(v_a_1913_);
            crate::leanh::lean_dec_ref_known(v_x_1895_, 1);
            v___x_1914_ = crate::leanh::lean_apply_1(v_h__3_1898_, v_a_1913_);
            return v___x_1914_;
        }
        5 => {
            let mut v_k_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1902_);
            crate::leanh::lean_dec(v_h__5_1900_);
            crate::leanh::lean_dec(v_h__4_1899_);
            crate::leanh::lean_dec(v_h__3_1898_);
            crate::leanh::lean_dec(v_h__2_1897_);
            crate::leanh::lean_dec(v_h__1_1896_);
            v_k_1915_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
            crate::leanh::lean_inc(v_k_1915_);
            v_a_1916_ = crate::leanh::lean_ctor_get(v_x_1895_, 1);
            crate::leanh::lean_inc_ref(v_a_1916_);
            crate::leanh::lean_dec_ref_known(v_x_1895_, 2);
            v___x_1917_ = crate::leanh::lean_apply_2(v_h__6_1901_, v_k_1915_, v_a_1916_);
            return v___x_1917_;
        }
        _ => {
            let mut v_a_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_1901_);
            crate::leanh::lean_dec(v_h__5_1900_);
            crate::leanh::lean_dec(v_h__4_1899_);
            crate::leanh::lean_dec(v_h__3_1898_);
            crate::leanh::lean_dec(v_h__2_1897_);
            crate::leanh::lean_dec(v_h__1_1896_);
            v_a_1918_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
            crate::leanh::lean_inc_ref(v_a_1918_);
            v_k_1919_ = crate::leanh::lean_ctor_get(v_x_1895_, 1);
            crate::leanh::lean_inc(v_k_1919_);
            crate::leanh::lean_dec_ref_known(v_x_1895_, 2);
            v___x_1920_ = crate::leanh::lean_apply_2(v_h__7_1902_, v_a_1918_, v_k_1919_);
            return v___x_1920_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter(
    mut v_motive_1921_: *mut crate::leanh::LeanObject,
    mut v_x_1922_: *mut crate::leanh::LeanObject,
    mut v_h__1_1923_: *mut crate::leanh::LeanObject,
    mut v_h__2_1924_: *mut crate::leanh::LeanObject,
    mut v_h__3_1925_: *mut crate::leanh::LeanObject,
    mut v_h__4_1926_: *mut crate::leanh::LeanObject,
    mut v_h__5_1927_: *mut crate::leanh::LeanObject,
    mut v_h__6_1928_: *mut crate::leanh::LeanObject,
    mut v_h__7_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1922_) {
        0 => {
            let mut v_v_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1929_);
            crate::leanh::lean_dec(v_h__6_1928_);
            crate::leanh::lean_dec(v_h__5_1927_);
            crate::leanh::lean_dec(v_h__3_1925_);
            crate::leanh::lean_dec(v_h__2_1924_);
            crate::leanh::lean_dec(v_h__1_1923_);
            v_v_1930_ = crate::leanh::lean_ctor_get(v_x_1922_, 0);
            crate::leanh::lean_inc(v_v_1930_);
            crate::leanh::lean_dec_ref_known(v_x_1922_, 1);
            v___x_1931_ = crate::leanh::lean_apply_1(v_h__4_1926_, v_v_1930_);
            return v___x_1931_;
        }
        1 => {
            let mut v_i_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1929_);
            crate::leanh::lean_dec(v_h__6_1928_);
            crate::leanh::lean_dec(v_h__4_1926_);
            crate::leanh::lean_dec(v_h__3_1925_);
            crate::leanh::lean_dec(v_h__2_1924_);
            crate::leanh::lean_dec(v_h__1_1923_);
            v_i_1932_ = crate::leanh::lean_ctor_get(v_x_1922_, 0);
            crate::leanh::lean_inc(v_i_1932_);
            crate::leanh::lean_dec_ref_known(v_x_1922_, 1);
            v___x_1933_ = crate::leanh::lean_apply_1(v_h__5_1927_, v_i_1932_);
            return v___x_1933_;
        }
        2 => {
            let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1929_);
            crate::leanh::lean_dec(v_h__6_1928_);
            crate::leanh::lean_dec(v_h__5_1927_);
            crate::leanh::lean_dec(v_h__4_1926_);
            crate::leanh::lean_dec(v_h__3_1925_);
            crate::leanh::lean_dec(v_h__2_1924_);
            v_a_1934_ = crate::leanh::lean_ctor_get(v_x_1922_, 0);
            crate::leanh::lean_inc_ref(v_a_1934_);
            v_b_1935_ = crate::leanh::lean_ctor_get(v_x_1922_, 1);
            crate::leanh::lean_inc_ref(v_b_1935_);
            crate::leanh::lean_dec_ref_known(v_x_1922_, 2);
            v___x_1936_ = crate::leanh::lean_apply_2(v_h__1_1923_, v_a_1934_, v_b_1935_);
            return v___x_1936_;
        }
        3 => {
            let mut v_a_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1929_);
            crate::leanh::lean_dec(v_h__6_1928_);
            crate::leanh::lean_dec(v_h__5_1927_);
            crate::leanh::lean_dec(v_h__4_1926_);
            crate::leanh::lean_dec(v_h__3_1925_);
            crate::leanh::lean_dec(v_h__1_1923_);
            v_a_1937_ = crate::leanh::lean_ctor_get(v_x_1922_, 0);
            crate::leanh::lean_inc_ref(v_a_1937_);
            v_b_1938_ = crate::leanh::lean_ctor_get(v_x_1922_, 1);
            crate::leanh::lean_inc_ref(v_b_1938_);
            crate::leanh::lean_dec_ref_known(v_x_1922_, 2);
            v___x_1939_ = crate::leanh::lean_apply_2(v_h__2_1924_, v_a_1937_, v_b_1938_);
            return v___x_1939_;
        }
        4 => {
            let mut v_a_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1929_);
            crate::leanh::lean_dec(v_h__6_1928_);
            crate::leanh::lean_dec(v_h__5_1927_);
            crate::leanh::lean_dec(v_h__4_1926_);
            crate::leanh::lean_dec(v_h__2_1924_);
            crate::leanh::lean_dec(v_h__1_1923_);
            v_a_1940_ = crate::leanh::lean_ctor_get(v_x_1922_, 0);
            crate::leanh::lean_inc_ref(v_a_1940_);
            crate::leanh::lean_dec_ref_known(v_x_1922_, 1);
            v___x_1941_ = crate::leanh::lean_apply_1(v_h__3_1925_, v_a_1940_);
            return v___x_1941_;
        }
        5 => {
            let mut v_k_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1929_);
            crate::leanh::lean_dec(v_h__5_1927_);
            crate::leanh::lean_dec(v_h__4_1926_);
            crate::leanh::lean_dec(v_h__3_1925_);
            crate::leanh::lean_dec(v_h__2_1924_);
            crate::leanh::lean_dec(v_h__1_1923_);
            v_k_1942_ = crate::leanh::lean_ctor_get(v_x_1922_, 0);
            crate::leanh::lean_inc(v_k_1942_);
            v_a_1943_ = crate::leanh::lean_ctor_get(v_x_1922_, 1);
            crate::leanh::lean_inc_ref(v_a_1943_);
            crate::leanh::lean_dec_ref_known(v_x_1922_, 2);
            v___x_1944_ = crate::leanh::lean_apply_2(v_h__6_1928_, v_k_1942_, v_a_1943_);
            return v___x_1944_;
        }
        _ => {
            let mut v_a_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_1928_);
            crate::leanh::lean_dec(v_h__5_1927_);
            crate::leanh::lean_dec(v_h__4_1926_);
            crate::leanh::lean_dec(v_h__3_1925_);
            crate::leanh::lean_dec(v_h__2_1924_);
            crate::leanh::lean_dec(v_h__1_1923_);
            v_a_1945_ = crate::leanh::lean_ctor_get(v_x_1922_, 0);
            crate::leanh::lean_inc_ref(v_a_1945_);
            v_k_1946_ = crate::leanh::lean_ctor_get(v_x_1922_, 1);
            crate::leanh::lean_inc(v_k_1946_);
            crate::leanh::lean_dec_ref_known(v_x_1922_, 2);
            v___x_1947_ = crate::leanh::lean_apply_2(v_h__7_1929_, v_a_1945_, v_k_1946_);
            return v___x_1947_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(
    mut v_x_1948_: *mut crate::leanh::LeanObject,
    mut v_h__1_1949_: *mut crate::leanh::LeanObject,
    mut v_h__2_1950_: *mut crate::leanh::LeanObject,
    mut v_h__3_1951_: *mut crate::leanh::LeanObject,
    mut v_h__4_1952_: *mut crate::leanh::LeanObject,
    mut v_h__5_1953_: *mut crate::leanh::LeanObject,
    mut v_h__6_1954_: *mut crate::leanh::LeanObject,
    mut v_h__7_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1948_) {
        0 => {
            let mut v_v_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1955_);
            crate::leanh::lean_dec(v_h__6_1954_);
            crate::leanh::lean_dec(v_h__5_1953_);
            crate::leanh::lean_dec(v_h__4_1952_);
            crate::leanh::lean_dec(v_h__3_1951_);
            crate::leanh::lean_dec(v_h__2_1950_);
            v_v_1956_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
            crate::leanh::lean_inc(v_v_1956_);
            crate::leanh::lean_dec_ref_known(v_x_1948_, 1);
            v___x_1957_ = crate::leanh::lean_apply_1(v_h__1_1949_, v_v_1956_);
            return v___x_1957_;
        }
        1 => {
            let mut v_i_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1955_);
            crate::leanh::lean_dec(v_h__6_1954_);
            crate::leanh::lean_dec(v_h__5_1953_);
            crate::leanh::lean_dec(v_h__4_1952_);
            crate::leanh::lean_dec(v_h__3_1951_);
            crate::leanh::lean_dec(v_h__1_1949_);
            v_i_1958_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
            crate::leanh::lean_inc(v_i_1958_);
            crate::leanh::lean_dec_ref_known(v_x_1948_, 1);
            v___x_1959_ = crate::leanh::lean_apply_1(v_h__2_1950_, v_i_1958_);
            return v___x_1959_;
        }
        2 => {
            let mut v_a_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1955_);
            crate::leanh::lean_dec(v_h__6_1954_);
            crate::leanh::lean_dec(v_h__5_1953_);
            crate::leanh::lean_dec(v_h__4_1952_);
            crate::leanh::lean_dec(v_h__2_1950_);
            crate::leanh::lean_dec(v_h__1_1949_);
            v_a_1960_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
            crate::leanh::lean_inc_ref(v_a_1960_);
            v_b_1961_ = crate::leanh::lean_ctor_get(v_x_1948_, 1);
            crate::leanh::lean_inc_ref(v_b_1961_);
            crate::leanh::lean_dec_ref_known(v_x_1948_, 2);
            v___x_1962_ = crate::leanh::lean_apply_2(v_h__3_1951_, v_a_1960_, v_b_1961_);
            return v___x_1962_;
        }
        3 => {
            let mut v_a_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1955_);
            crate::leanh::lean_dec(v_h__6_1954_);
            crate::leanh::lean_dec(v_h__5_1953_);
            crate::leanh::lean_dec(v_h__3_1951_);
            crate::leanh::lean_dec(v_h__2_1950_);
            crate::leanh::lean_dec(v_h__1_1949_);
            v_a_1963_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
            crate::leanh::lean_inc_ref(v_a_1963_);
            v_b_1964_ = crate::leanh::lean_ctor_get(v_x_1948_, 1);
            crate::leanh::lean_inc_ref(v_b_1964_);
            crate::leanh::lean_dec_ref_known(v_x_1948_, 2);
            v___x_1965_ = crate::leanh::lean_apply_2(v_h__4_1952_, v_a_1963_, v_b_1964_);
            return v___x_1965_;
        }
        4 => {
            let mut v_a_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_1954_);
            crate::leanh::lean_dec(v_h__5_1953_);
            crate::leanh::lean_dec(v_h__4_1952_);
            crate::leanh::lean_dec(v_h__3_1951_);
            crate::leanh::lean_dec(v_h__2_1950_);
            crate::leanh::lean_dec(v_h__1_1949_);
            v_a_1966_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
            crate::leanh::lean_inc_ref(v_a_1966_);
            crate::leanh::lean_dec_ref_known(v_x_1948_, 1);
            v___x_1967_ = crate::leanh::lean_apply_1(v_h__7_1955_, v_a_1966_);
            return v___x_1967_;
        }
        5 => {
            let mut v_k_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1955_);
            crate::leanh::lean_dec(v_h__6_1954_);
            crate::leanh::lean_dec(v_h__4_1952_);
            crate::leanh::lean_dec(v_h__3_1951_);
            crate::leanh::lean_dec(v_h__2_1950_);
            crate::leanh::lean_dec(v_h__1_1949_);
            v_k_1968_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
            crate::leanh::lean_inc(v_k_1968_);
            v_a_1969_ = crate::leanh::lean_ctor_get(v_x_1948_, 1);
            crate::leanh::lean_inc_ref(v_a_1969_);
            crate::leanh::lean_dec_ref_known(v_x_1948_, 2);
            v___x_1970_ = crate::leanh::lean_apply_2(v_h__5_1953_, v_k_1968_, v_a_1969_);
            return v___x_1970_;
        }
        _ => {
            let mut v_a_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1955_);
            crate::leanh::lean_dec(v_h__5_1953_);
            crate::leanh::lean_dec(v_h__4_1952_);
            crate::leanh::lean_dec(v_h__3_1951_);
            crate::leanh::lean_dec(v_h__2_1950_);
            crate::leanh::lean_dec(v_h__1_1949_);
            v_a_1971_ = crate::leanh::lean_ctor_get(v_x_1948_, 0);
            crate::leanh::lean_inc_ref(v_a_1971_);
            v_k_1972_ = crate::leanh::lean_ctor_get(v_x_1948_, 1);
            crate::leanh::lean_inc(v_k_1972_);
            crate::leanh::lean_dec_ref_known(v_x_1948_, 2);
            v___x_1973_ = crate::leanh::lean_apply_2(v_h__6_1954_, v_a_1971_, v_k_1972_);
            return v___x_1973_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter(
    mut v_motive_1974_: *mut crate::leanh::LeanObject,
    mut v_x_1975_: *mut crate::leanh::LeanObject,
    mut v_h__1_1976_: *mut crate::leanh::LeanObject,
    mut v_h__2_1977_: *mut crate::leanh::LeanObject,
    mut v_h__3_1978_: *mut crate::leanh::LeanObject,
    mut v_h__4_1979_: *mut crate::leanh::LeanObject,
    mut v_h__5_1980_: *mut crate::leanh::LeanObject,
    mut v_h__6_1981_: *mut crate::leanh::LeanObject,
    mut v_h__7_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1975_) {
        0 => {
            let mut v_v_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1982_);
            crate::leanh::lean_dec(v_h__6_1981_);
            crate::leanh::lean_dec(v_h__5_1980_);
            crate::leanh::lean_dec(v_h__4_1979_);
            crate::leanh::lean_dec(v_h__3_1978_);
            crate::leanh::lean_dec(v_h__2_1977_);
            v_v_1983_ = crate::leanh::lean_ctor_get(v_x_1975_, 0);
            crate::leanh::lean_inc(v_v_1983_);
            crate::leanh::lean_dec_ref_known(v_x_1975_, 1);
            v___x_1984_ = crate::leanh::lean_apply_1(v_h__1_1976_, v_v_1983_);
            return v___x_1984_;
        }
        1 => {
            let mut v_i_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1982_);
            crate::leanh::lean_dec(v_h__6_1981_);
            crate::leanh::lean_dec(v_h__5_1980_);
            crate::leanh::lean_dec(v_h__4_1979_);
            crate::leanh::lean_dec(v_h__3_1978_);
            crate::leanh::lean_dec(v_h__1_1976_);
            v_i_1985_ = crate::leanh::lean_ctor_get(v_x_1975_, 0);
            crate::leanh::lean_inc(v_i_1985_);
            crate::leanh::lean_dec_ref_known(v_x_1975_, 1);
            v___x_1986_ = crate::leanh::lean_apply_1(v_h__2_1977_, v_i_1985_);
            return v___x_1986_;
        }
        2 => {
            let mut v_a_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1982_);
            crate::leanh::lean_dec(v_h__6_1981_);
            crate::leanh::lean_dec(v_h__5_1980_);
            crate::leanh::lean_dec(v_h__4_1979_);
            crate::leanh::lean_dec(v_h__2_1977_);
            crate::leanh::lean_dec(v_h__1_1976_);
            v_a_1987_ = crate::leanh::lean_ctor_get(v_x_1975_, 0);
            crate::leanh::lean_inc_ref(v_a_1987_);
            v_b_1988_ = crate::leanh::lean_ctor_get(v_x_1975_, 1);
            crate::leanh::lean_inc_ref(v_b_1988_);
            crate::leanh::lean_dec_ref_known(v_x_1975_, 2);
            v___x_1989_ = crate::leanh::lean_apply_2(v_h__3_1978_, v_a_1987_, v_b_1988_);
            return v___x_1989_;
        }
        3 => {
            let mut v_a_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1982_);
            crate::leanh::lean_dec(v_h__6_1981_);
            crate::leanh::lean_dec(v_h__5_1980_);
            crate::leanh::lean_dec(v_h__3_1978_);
            crate::leanh::lean_dec(v_h__2_1977_);
            crate::leanh::lean_dec(v_h__1_1976_);
            v_a_1990_ = crate::leanh::lean_ctor_get(v_x_1975_, 0);
            crate::leanh::lean_inc_ref(v_a_1990_);
            v_b_1991_ = crate::leanh::lean_ctor_get(v_x_1975_, 1);
            crate::leanh::lean_inc_ref(v_b_1991_);
            crate::leanh::lean_dec_ref_known(v_x_1975_, 2);
            v___x_1992_ = crate::leanh::lean_apply_2(v_h__4_1979_, v_a_1990_, v_b_1991_);
            return v___x_1992_;
        }
        4 => {
            let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_1981_);
            crate::leanh::lean_dec(v_h__5_1980_);
            crate::leanh::lean_dec(v_h__4_1979_);
            crate::leanh::lean_dec(v_h__3_1978_);
            crate::leanh::lean_dec(v_h__2_1977_);
            crate::leanh::lean_dec(v_h__1_1976_);
            v_a_1993_ = crate::leanh::lean_ctor_get(v_x_1975_, 0);
            crate::leanh::lean_inc_ref(v_a_1993_);
            crate::leanh::lean_dec_ref_known(v_x_1975_, 1);
            v___x_1994_ = crate::leanh::lean_apply_1(v_h__7_1982_, v_a_1993_);
            return v___x_1994_;
        }
        5 => {
            let mut v_k_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1982_);
            crate::leanh::lean_dec(v_h__6_1981_);
            crate::leanh::lean_dec(v_h__4_1979_);
            crate::leanh::lean_dec(v_h__3_1978_);
            crate::leanh::lean_dec(v_h__2_1977_);
            crate::leanh::lean_dec(v_h__1_1976_);
            v_k_1995_ = crate::leanh::lean_ctor_get(v_x_1975_, 0);
            crate::leanh::lean_inc(v_k_1995_);
            v_a_1996_ = crate::leanh::lean_ctor_get(v_x_1975_, 1);
            crate::leanh::lean_inc_ref(v_a_1996_);
            crate::leanh::lean_dec_ref_known(v_x_1975_, 2);
            v___x_1997_ = crate::leanh::lean_apply_2(v_h__5_1980_, v_k_1995_, v_a_1996_);
            return v___x_1997_;
        }
        _ => {
            let mut v_a_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1982_);
            crate::leanh::lean_dec(v_h__5_1980_);
            crate::leanh::lean_dec(v_h__4_1979_);
            crate::leanh::lean_dec(v_h__3_1978_);
            crate::leanh::lean_dec(v_h__2_1977_);
            crate::leanh::lean_dec(v_h__1_1976_);
            v_a_1998_ = crate::leanh::lean_ctor_get(v_x_1975_, 0);
            crate::leanh::lean_inc_ref(v_a_1998_);
            v_k_1999_ = crate::leanh::lean_ctor_get(v_x_1975_, 1);
            crate::leanh::lean_inc(v_k_1999_);
            crate::leanh::lean_dec_ref_known(v_x_1975_, 2);
            v___x_2000_ = crate::leanh::lean_apply_2(v_h__6_1981_, v_a_1998_, v_k_1999_);
            return v___x_2000_;
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_isUnsatEq(mut v_p_2001_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_2001_) == 0 {
        let mut v_k_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2004_: u8 = 0;
        v_k_2002_ = crate::leanh::lean_ctor_get(v_p_2001_, 0);
        v___x_2003_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
            _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
        );
        v___x_2004_ = lean_int_dec_eq(v_k_2002_, v___x_2003_);
        if v___x_2004_ == 0 {
            let mut v___x_2005_: u8 = 0;
            v___x_2005_ = 1;
            return v___x_2005_;
        } else {
            let mut v___x_2006_: u8 = 0;
            v___x_2006_ = 0;
            return v___x_2006_;
        }
    } else {
        let mut v___x_2007_: u8 = 0;
        v___x_2007_ = 0;
        return v___x_2007_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isUnsatEq___boxed(
    mut v_p_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: u8 = 0;
    let mut v_r_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Int_Linear_Poly_isUnsatEq(v_p_2008_);
    crate::leanh::lean_dec_ref(v_p_2008_);
    v_r_2010_ = crate::leanh::lean_box((v_res_2009_) as usize);
    return v_r_2010_;
}
pub unsafe fn l_Int_Linear_Poly_isValidEq(mut v_p_2011_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_2011_) == 0 {
        let mut v_k_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: u8 = 0;
        v_k_2012_ = crate::leanh::lean_ctor_get(v_p_2011_, 0);
        v___x_2013_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
            _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
        );
        v___x_2014_ = lean_int_dec_eq(v_k_2012_, v___x_2013_);
        return v___x_2014_;
    } else {
        let mut v___x_2015_: u8 = 0;
        v___x_2015_ = 0;
        return v___x_2015_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isValidEq___boxed(
    mut v_p_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2017_: u8 = 0;
    let mut v_r_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2017_ = l_Int_Linear_Poly_isValidEq(v_p_2016_);
    crate::leanh::lean_dec_ref(v_p_2016_);
    v_r_2018_ = crate::leanh::lean_box((v_res_2017_) as usize);
    return v_r_2018_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter___redArg(
    mut v_p_2019_: *mut crate::leanh::LeanObject,
    mut v_h__1_2020_: *mut crate::leanh::LeanObject,
    mut v_h__2_2021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2019_) == 0 {
        let mut v_k_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2021_);
        v_k_2022_ = crate::leanh::lean_ctor_get(v_p_2019_, 0);
        crate::leanh::lean_inc(v_k_2022_);
        crate::leanh::lean_dec_ref_known(v_p_2019_, 1);
        v___x_2023_ = crate::leanh::lean_apply_1(v_h__1_2020_, v_k_2022_);
        return v___x_2023_;
    } else {
        let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2020_);
        v___x_2024_ =
            crate::leanh::lean_apply_2(v_h__2_2021_, v_p_2019_, crate::leanh::lean_box(0));
        return v___x_2024_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter(
    mut v_motive_2025_: *mut crate::leanh::LeanObject,
    mut v_p_2026_: *mut crate::leanh::LeanObject,
    mut v_h__1_2027_: *mut crate::leanh::LeanObject,
    mut v_h__2_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2026_) == 0 {
        let mut v_k_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2028_);
        v_k_2029_ = crate::leanh::lean_ctor_get(v_p_2026_, 0);
        crate::leanh::lean_inc(v_k_2029_);
        crate::leanh::lean_dec_ref_known(v_p_2026_, 1);
        v___x_2030_ = crate::leanh::lean_apply_1(v_h__1_2027_, v_k_2029_);
        return v___x_2030_;
    } else {
        let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2027_);
        v___x_2031_ =
            crate::leanh::lean_apply_2(v_h__2_2028_, v_p_2026_, crate::leanh::lean_box(0));
        return v___x_2031_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isUnsatLe(mut v_p_2032_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_2032_) == 0 {
        let mut v_k_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: u8 = 0;
        v_k_2033_ = crate::leanh::lean_ctor_get(v_p_2032_, 0);
        v___x_2034_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
            _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
        );
        v___x_2035_ = lean_int_dec_lt(v___x_2034_, v_k_2033_);
        return v___x_2035_;
    } else {
        let mut v___x_2036_: u8 = 0;
        v___x_2036_ = 0;
        return v___x_2036_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isUnsatLe___boxed(
    mut v_p_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2038_: u8 = 0;
    let mut v_r_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Int_Linear_Poly_isUnsatLe(v_p_2037_);
    crate::leanh::lean_dec_ref(v_p_2037_);
    v_r_2039_ = crate::leanh::lean_box((v_res_2038_) as usize);
    return v_r_2039_;
}
pub unsafe fn l_Int_Linear_Poly_isValidLe(mut v_p_2040_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_2040_) == 0 {
        let mut v_k_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: u8 = 0;
        v_k_2041_ = crate::leanh::lean_ctor_get(v_p_2040_, 0);
        v___x_2042_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
            _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
        );
        v___x_2043_ = lean_int_dec_le(v_k_2041_, v___x_2042_);
        return v___x_2043_;
    } else {
        let mut v___x_2044_: u8 = 0;
        v___x_2044_ = 0;
        return v___x_2044_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isValidLe___boxed(
    mut v_p_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2046_: u8 = 0;
    let mut v_r_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Int_Linear_Poly_isValidLe(v_p_2045_);
    crate::leanh::lean_dec_ref(v_p_2045_);
    v_r_2047_ = crate::leanh::lean_box((v_res_2046_) as usize);
    return v_r_2047_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(
    mut v_a_2048_: *mut crate::leanh::LeanObject,
    mut v_b_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_Int_gcd(v_a_2048_, v_b_2049_);
    v___x_2051_ = lean_nat_to_int(v___x_2050_);
    return v___x_2051_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_gcd___boxed(
    mut v_a_2052_: *mut crate::leanh::LeanObject,
    mut v_b_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2054_ = l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(v_a_2052_, v_b_2053_);
    crate::leanh::lean_dec(v_b_2053_);
    crate::leanh::lean_dec(v_a_2052_);
    return v_res_2054_;
}
pub unsafe fn l_Int_Linear_Poly_gcdCoeffs(
    mut v_x_2055_: *mut crate::leanh::LeanObject,
    mut v_x_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2055_) == 0 {
                    return v_x_2056_;
                } else {
                    v_k_2057_ = crate::leanh::lean_ctor_get(v_x_2055_, 0);
                    v_p_2058_ = crate::leanh::lean_ctor_get(v_x_2055_, 2);
                    v___x_2059_ = l_Int_gcd(v_k_2057_, v_x_2056_);
                    crate::leanh::lean_dec(v_x_2056_);
                    v___x_2060_ = lean_nat_to_int(v___x_2059_);
                    v_x_2055_ = v_p_2058_;
                    v_x_2056_ = v___x_2060_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_gcdCoeffs___boxed(
    mut v_x_2062_: *mut crate::leanh::LeanObject,
    mut v_x_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Int_Linear_Poly_gcdCoeffs(v_x_2062_, v_x_2063_);
    crate::leanh::lean_dec_ref(v_x_2062_);
    return v_res_2064_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(
    mut v_x_2065_: *mut crate::leanh::LeanObject,
    mut v_x_2066_: *mut crate::leanh::LeanObject,
    mut v_h__1_2067_: *mut crate::leanh::LeanObject,
    mut v_h__2_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2065_) == 0 {
        let mut v_k_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2068_);
        v_k_2069_ = crate::leanh::lean_ctor_get(v_x_2065_, 0);
        crate::leanh::lean_inc(v_k_2069_);
        crate::leanh::lean_dec_ref_known(v_x_2065_, 1);
        v___x_2070_ = crate::leanh::lean_apply_2(v_h__1_2067_, v_k_2069_, v_x_2066_);
        return v___x_2070_;
    } else {
        let mut v_k_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2067_);
        v_k_2071_ = crate::leanh::lean_ctor_get(v_x_2065_, 0);
        crate::leanh::lean_inc(v_k_2071_);
        v_v_2072_ = crate::leanh::lean_ctor_get(v_x_2065_, 1);
        crate::leanh::lean_inc(v_v_2072_);
        v_p_2073_ = crate::leanh::lean_ctor_get(v_x_2065_, 2);
        crate::leanh::lean_inc_ref(v_p_2073_);
        crate::leanh::lean_dec_ref_known(v_x_2065_, 3);
        v___x_2074_ =
            crate::leanh::lean_apply_4(v_h__2_2068_, v_k_2071_, v_v_2072_, v_p_2073_, v_x_2066_);
        return v___x_2074_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter(
    mut v_motive_2075_: *mut crate::leanh::LeanObject,
    mut v_x_2076_: *mut crate::leanh::LeanObject,
    mut v_x_2077_: *mut crate::leanh::LeanObject,
    mut v_h__1_2078_: *mut crate::leanh::LeanObject,
    mut v_h__2_2079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2076_) == 0 {
        let mut v_k_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2079_);
        v_k_2080_ = crate::leanh::lean_ctor_get(v_x_2076_, 0);
        crate::leanh::lean_inc(v_k_2080_);
        crate::leanh::lean_dec_ref_known(v_x_2076_, 1);
        v___x_2081_ = crate::leanh::lean_apply_2(v_h__1_2078_, v_k_2080_, v_x_2077_);
        return v___x_2081_;
    } else {
        let mut v_k_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2078_);
        v_k_2082_ = crate::leanh::lean_ctor_get(v_x_2076_, 0);
        crate::leanh::lean_inc(v_k_2082_);
        v_v_2083_ = crate::leanh::lean_ctor_get(v_x_2076_, 1);
        crate::leanh::lean_inc(v_v_2083_);
        v_p_2084_ = crate::leanh::lean_ctor_get(v_x_2076_, 2);
        crate::leanh::lean_inc_ref(v_p_2084_);
        crate::leanh::lean_dec_ref_known(v_x_2076_, 3);
        v___x_2085_ =
            crate::leanh::lean_apply_4(v_h__2_2079_, v_k_2082_, v_v_2083_, v_p_2084_, v_x_2077_);
        return v___x_2085_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isUnsatDvd(
    mut v_k_2086_: *mut crate::leanh::LeanObject,
    mut v_p_2087_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    v___x_2088_ = l_Int_Linear_Poly_getConst(v_p_2087_);
    v___x_2089_ = l_Int_Linear_Poly_gcdCoeffs(v_p_2087_, v_k_2086_);
    v___x_2090_ = lean_int_emod(v___x_2088_, v___x_2089_);
    crate::leanh::lean_dec(v___x_2089_);
    crate::leanh::lean_dec(v___x_2088_);
    v___x_2091_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
    );
    v___x_2092_ = lean_int_dec_eq(v___x_2090_, v___x_2091_);
    crate::leanh::lean_dec(v___x_2090_);
    if v___x_2092_ == 0 {
        let mut v___x_2093_: u8 = 0;
        v___x_2093_ = 1;
        return v___x_2093_;
    } else {
        let mut v___x_2094_: u8 = 0;
        v___x_2094_ = 0;
        return v___x_2094_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isUnsatDvd___boxed(
    mut v_k_2095_: *mut crate::leanh::LeanObject,
    mut v_p_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2097_: u8 = 0;
    let mut v_r_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2097_ = l_Int_Linear_Poly_isUnsatDvd(v_k_2095_, v_p_2096_);
    crate::leanh::lean_dec_ref(v_p_2096_);
    v_r_2098_ = crate::leanh::lean_box((v_res_2097_) as usize);
    return v_r_2098_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(
    mut v_p_u2081_2099_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2100_: *mut crate::leanh::LeanObject,
    mut v_h__1_2101_: *mut crate::leanh::LeanObject,
    mut v_h__2_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_2099_) == 1 {
        if crate::leanh::lean_obj_tag(v_p_u2082_2100_) == 1 {
            let mut v_k_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2102_);
            v_k_2103_ = crate::leanh::lean_ctor_get(v_p_u2081_2099_, 0);
            crate::leanh::lean_inc(v_k_2103_);
            v_v_2104_ = crate::leanh::lean_ctor_get(v_p_u2081_2099_, 1);
            crate::leanh::lean_inc(v_v_2104_);
            v_p_2105_ = crate::leanh::lean_ctor_get(v_p_u2081_2099_, 2);
            crate::leanh::lean_inc_ref(v_p_2105_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2099_, 3);
            v_k_2106_ = crate::leanh::lean_ctor_get(v_p_u2082_2100_, 0);
            crate::leanh::lean_inc(v_k_2106_);
            v_v_2107_ = crate::leanh::lean_ctor_get(v_p_u2082_2100_, 1);
            crate::leanh::lean_inc(v_v_2107_);
            v_p_2108_ = crate::leanh::lean_ctor_get(v_p_u2082_2100_, 2);
            crate::leanh::lean_inc_ref(v_p_2108_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2100_, 3);
            v___x_2109_ = crate::leanh::lean_apply_6(
                v_h__1_2101_,
                v_k_2103_,
                v_v_2104_,
                v_p_2105_,
                v_k_2106_,
                v_v_2107_,
                v_p_2108_,
            );
            return v___x_2109_;
        } else {
            let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_2101_);
            v___x_2110_ = crate::leanh::lean_apply_3(
                v_h__2_2102_,
                v_p_u2081_2099_,
                v_p_u2082_2100_,
                crate::leanh::lean_box(0),
            );
            return v___x_2110_;
        }
    } else {
        let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2101_);
        v___x_2111_ = crate::leanh::lean_apply_3(
            v_h__2_2102_,
            v_p_u2081_2099_,
            v_p_u2082_2100_,
            crate::leanh::lean_box(0),
        );
        return v___x_2111_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter(
    mut v_motive_2112_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2113_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2114_: *mut crate::leanh::LeanObject,
    mut v_h__1_2115_: *mut crate::leanh::LeanObject,
    mut v_h__2_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_2113_) == 1 {
        if crate::leanh::lean_obj_tag(v_p_u2082_2114_) == 1 {
            let mut v_k_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2116_);
            v_k_2117_ = crate::leanh::lean_ctor_get(v_p_u2081_2113_, 0);
            crate::leanh::lean_inc(v_k_2117_);
            v_v_2118_ = crate::leanh::lean_ctor_get(v_p_u2081_2113_, 1);
            crate::leanh::lean_inc(v_v_2118_);
            v_p_2119_ = crate::leanh::lean_ctor_get(v_p_u2081_2113_, 2);
            crate::leanh::lean_inc_ref(v_p_2119_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2113_, 3);
            v_k_2120_ = crate::leanh::lean_ctor_get(v_p_u2082_2114_, 0);
            crate::leanh::lean_inc(v_k_2120_);
            v_v_2121_ = crate::leanh::lean_ctor_get(v_p_u2082_2114_, 1);
            crate::leanh::lean_inc(v_v_2121_);
            v_p_2122_ = crate::leanh::lean_ctor_get(v_p_u2082_2114_, 2);
            crate::leanh::lean_inc_ref(v_p_2122_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2114_, 3);
            v___x_2123_ = crate::leanh::lean_apply_6(
                v_h__1_2115_,
                v_k_2117_,
                v_v_2118_,
                v_p_2119_,
                v_k_2120_,
                v_v_2121_,
                v_p_2122_,
            );
            return v___x_2123_;
        } else {
            let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_2115_);
            v___x_2124_ = crate::leanh::lean_apply_3(
                v_h__2_2116_,
                v_p_u2081_2113_,
                v_p_u2082_2114_,
                crate::leanh::lean_box(0),
            );
            return v___x_2124_;
        }
    } else {
        let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2115_);
        v___x_2125_ = crate::leanh::lean_apply_3(
            v_h__2_2116_,
            v_p_u2081_2113_,
            v_p_u2082_2114_,
            crate::leanh::lean_box(0),
        );
        return v___x_2125_;
    }
}
pub unsafe fn l_Int_Linear_Poly_leadCoeff(
    mut v_p_2126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2126_) == 1 {
        let mut v_k_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_2127_ = crate::leanh::lean_ctor_get(v_p_2126_, 0);
        crate::leanh::lean_inc(v_k_2127_);
        return v_k_2127_;
    } else {
        let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2128_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0_once),
            _init_l_Int_Linear_Expr_toPoly_x27___closed__0,
        );
        return v___x_2128_;
    }
}
pub unsafe fn l_Int_Linear_Poly_leadCoeff___boxed(
    mut v_p_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2130_ = l_Int_Linear_Poly_leadCoeff(v_p_2129_);
    crate::leanh::lean_dec_ref(v_p_2129_);
    return v_res_2130_;
}
pub unsafe fn l_Int_Linear_Poly_coeff(
    mut v_p_2131_: *mut crate::leanh::LeanObject,
    mut v_x_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_2131_) == 0 {
                    v___x_2133_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_instInhabitedExpr_default___closed__0_once
                        ),
                        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
                    );
                    return v___x_2133_;
                } else {
                    v_k_2134_ = crate::leanh::lean_ctor_get(v_p_2131_, 0);
                    v_v_2135_ = crate::leanh::lean_ctor_get(v_p_2131_, 1);
                    v_p_2136_ = crate::leanh::lean_ctor_get(v_p_2131_, 2);
                    v___x_2137_ = lean_nat_dec_eq(v_x_2132_, v_v_2135_);
                    if v___x_2137_ == 0 {
                        v_p_2131_ = v_p_2136_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_2134_);
                        return v_k_2134_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_coeff___boxed(
    mut v_p_2139_: *mut crate::leanh::LeanObject,
    mut v_x_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Int_Linear_Poly_coeff(v_p_2139_, v_x_2140_);
    crate::leanh::lean_dec(v_x_2140_);
    crate::leanh::lean_dec_ref(v_p_2139_);
    return v_res_2141_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter___redArg(
    mut v_p_2142_: *mut crate::leanh::LeanObject,
    mut v_h__1_2143_: *mut crate::leanh::LeanObject,
    mut v_h__2_2144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2142_) == 0 {
        let mut v_k_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2143_);
        v_k_2145_ = crate::leanh::lean_ctor_get(v_p_2142_, 0);
        crate::leanh::lean_inc(v_k_2145_);
        crate::leanh::lean_dec_ref_known(v_p_2142_, 1);
        v___x_2146_ = crate::leanh::lean_apply_1(v_h__2_2144_, v_k_2145_);
        return v___x_2146_;
    } else {
        let mut v_k_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2144_);
        v_k_2147_ = crate::leanh::lean_ctor_get(v_p_2142_, 0);
        crate::leanh::lean_inc(v_k_2147_);
        v_v_2148_ = crate::leanh::lean_ctor_get(v_p_2142_, 1);
        crate::leanh::lean_inc(v_v_2148_);
        v_p_2149_ = crate::leanh::lean_ctor_get(v_p_2142_, 2);
        crate::leanh::lean_inc_ref(v_p_2149_);
        crate::leanh::lean_dec_ref_known(v_p_2142_, 3);
        v___x_2150_ = crate::leanh::lean_apply_3(v_h__1_2143_, v_k_2147_, v_v_2148_, v_p_2149_);
        return v___x_2150_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter(
    mut v_motive_2151_: *mut crate::leanh::LeanObject,
    mut v_p_2152_: *mut crate::leanh::LeanObject,
    mut v_h__1_2153_: *mut crate::leanh::LeanObject,
    mut v_h__2_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2152_) == 0 {
        let mut v_k_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2153_);
        v_k_2155_ = crate::leanh::lean_ctor_get(v_p_2152_, 0);
        crate::leanh::lean_inc(v_k_2155_);
        crate::leanh::lean_dec_ref_known(v_p_2152_, 1);
        v___x_2156_ = crate::leanh::lean_apply_1(v_h__2_2154_, v_k_2155_);
        return v___x_2156_;
    } else {
        let mut v_k_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2154_);
        v_k_2157_ = crate::leanh::lean_ctor_get(v_p_2152_, 0);
        crate::leanh::lean_inc(v_k_2157_);
        v_v_2158_ = crate::leanh::lean_ctor_get(v_p_2152_, 1);
        crate::leanh::lean_inc(v_v_2158_);
        v_p_2159_ = crate::leanh::lean_ctor_get(v_p_2152_, 2);
        crate::leanh::lean_inc_ref(v_p_2159_);
        crate::leanh::lean_dec_ref_known(v_p_2152_, 3);
        v___x_2160_ = crate::leanh::lean_apply_3(v_h__1_2153_, v_k_2157_, v_v_2158_, v_p_2159_);
        return v___x_2160_;
    }
}
pub unsafe fn l_Int_Linear_abs(
    mut v_x_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2162_ = lean_nat_abs(v_x_2161_);
    v___x_2163_ = lean_nat_to_int(v___x_2162_);
    return v___x_2163_;
}
pub unsafe fn l_Int_Linear_abs___boxed(
    mut v_x_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2165_ = l_Int_Linear_abs(v_x_2164_);
    crate::leanh::lean_dec(v_x_2164_);
    return v_res_2165_;
}
pub unsafe fn l_Int_Linear_Poly_isUnsatDiseq(mut v_p_2166_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_2166_) == 0 {
        let mut v_k_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: u8 = 0;
        v_k_2167_ = crate::leanh::lean_ctor_get(v_p_2166_, 0);
        v___x_2168_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
            _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
        );
        v___x_2169_ = lean_int_dec_eq(v_k_2167_, v___x_2168_);
        return v___x_2169_;
    } else {
        let mut v___x_2170_: u8 = 0;
        v___x_2170_ = 0;
        return v___x_2170_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isUnsatDiseq___boxed(
    mut v_p_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2172_: u8 = 0;
    let mut v_r_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2172_ = l_Int_Linear_Poly_isUnsatDiseq(v_p_2171_);
    crate::leanh::lean_dec_ref(v_p_2171_);
    v_r_2173_ = crate::leanh::lean_box((v_res_2172_) as usize);
    return v_r_2173_;
}
pub unsafe fn l_Int_Linear_Poly_tail(
    mut v_p_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2174_) == 1 {
        let mut v_p_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_2175_ = crate::leanh::lean_ctor_get(v_p_2174_, 2);
        crate::leanh::lean_inc_ref(v_p_2175_);
        return v_p_2175_;
    } else {
        crate::leanh::lean_inc_ref(v_p_2174_);
        return v_p_2174_;
    }
}
pub unsafe fn l_Int_Linear_Poly_tail___boxed(
    mut v_p_2176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2177_ = l_Int_Linear_Poly_tail(v_p_2176_);
    crate::leanh::lean_dec_ref(v_p_2176_);
    return v_res_2177_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter___redArg(
    mut v_p_2178_: *mut crate::leanh::LeanObject,
    mut v_h__1_2179_: *mut crate::leanh::LeanObject,
    mut v_h__2_2180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2178_) == 1 {
        let mut v_k_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2180_);
        v_k_2181_ = crate::leanh::lean_ctor_get(v_p_2178_, 0);
        crate::leanh::lean_inc(v_k_2181_);
        v_v_2182_ = crate::leanh::lean_ctor_get(v_p_2178_, 1);
        crate::leanh::lean_inc(v_v_2182_);
        v_p_2183_ = crate::leanh::lean_ctor_get(v_p_2178_, 2);
        crate::leanh::lean_inc_ref(v_p_2183_);
        crate::leanh::lean_dec_ref_known(v_p_2178_, 3);
        v___x_2184_ = crate::leanh::lean_apply_3(v_h__1_2179_, v_k_2181_, v_v_2182_, v_p_2183_);
        return v___x_2184_;
    } else {
        let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2179_);
        v___x_2185_ =
            crate::leanh::lean_apply_2(v_h__2_2180_, v_p_2178_, crate::leanh::lean_box(0));
        return v___x_2185_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter(
    mut v_motive_2186_: *mut crate::leanh::LeanObject,
    mut v_p_2187_: *mut crate::leanh::LeanObject,
    mut v_h__1_2188_: *mut crate::leanh::LeanObject,
    mut v_h__2_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_2187_) == 1 {
        let mut v_k_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2189_);
        v_k_2190_ = crate::leanh::lean_ctor_get(v_p_2187_, 0);
        crate::leanh::lean_inc(v_k_2190_);
        v_v_2191_ = crate::leanh::lean_ctor_get(v_p_2187_, 1);
        crate::leanh::lean_inc(v_v_2191_);
        v_p_2192_ = crate::leanh::lean_ctor_get(v_p_2187_, 2);
        crate::leanh::lean_inc_ref(v_p_2192_);
        crate::leanh::lean_dec_ref_known(v_p_2187_, 3);
        v___x_2193_ = crate::leanh::lean_apply_3(v_h__1_2188_, v_k_2190_, v_v_2191_, v_p_2192_);
        return v___x_2193_;
    } else {
        let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2188_);
        v___x_2194_ =
            crate::leanh::lean_apply_2(v_h__2_2189_, v_p_2187_, crate::leanh::lean_box(0));
        return v___x_2194_;
    }
}
pub unsafe fn l_Int_Linear_Poly_casesOnAdd(
    mut v_p_2195_: *mut crate::leanh::LeanObject,
    mut v_k_2196_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_2195_) == 0 {
        let mut v___x_2197_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v_p_2195_, 1);
        crate::leanh::lean_dec_ref(v_k_2196_);
        v___x_2197_ = 0;
        return v___x_2197_;
    } else {
        let mut v_a_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2202_: u8 = 0;
        v_a_2198_ = crate::leanh::lean_ctor_get(v_p_2195_, 0);
        crate::leanh::lean_inc(v_a_2198_);
        v_a_2199_ = crate::leanh::lean_ctor_get(v_p_2195_, 1);
        crate::leanh::lean_inc(v_a_2199_);
        v_a_2200_ = crate::leanh::lean_ctor_get(v_p_2195_, 2);
        crate::leanh::lean_inc_ref(v_a_2200_);
        crate::leanh::lean_dec_ref_known(v_p_2195_, 3);
        v___x_2201_ = crate::leanh::lean_apply_3(v_k_2196_, v_a_2198_, v_a_2199_, v_a_2200_);
        v___x_2202_ = (crate::leanh::lean_unbox(v___x_2201_) as u8);
        return v___x_2202_;
    }
}
pub unsafe fn l_Int_Linear_Poly_casesOnAdd___boxed(
    mut v_p_2203_: *mut crate::leanh::LeanObject,
    mut v_k_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2205_: u8 = 0;
    let mut v_r_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Int_Linear_Poly_casesOnAdd(v_p_2203_, v_k_2204_);
    v_r_2206_ = crate::leanh::lean_box((v_res_2205_) as usize);
    return v_r_2206_;
}
pub unsafe fn l_Int_Linear_Poly_casesOnNum(
    mut v_p_2207_: *mut crate::leanh::LeanObject,
    mut v_k_2208_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_2207_) == 0 {
        let mut v_a_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: u8 = 0;
        v_a_2209_ = crate::leanh::lean_ctor_get(v_p_2207_, 0);
        crate::leanh::lean_inc(v_a_2209_);
        crate::leanh::lean_dec_ref_known(v_p_2207_, 1);
        v___x_2210_ = crate::leanh::lean_apply_1(v_k_2208_, v_a_2209_);
        v___x_2211_ = (crate::leanh::lean_unbox(v___x_2210_) as u8);
        return v___x_2211_;
    } else {
        let mut v___x_2212_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v_p_2207_, 3);
        crate::leanh::lean_dec_ref(v_k_2208_);
        v___x_2212_ = 0;
        return v___x_2212_;
    }
}
pub unsafe fn l_Int_Linear_Poly_casesOnNum___boxed(
    mut v_p_2213_: *mut crate::leanh::LeanObject,
    mut v_k_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2215_: u8 = 0;
    let mut v_r_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Int_Linear_Poly_casesOnNum(v_p_2213_, v_k_2214_);
    v_r_2216_ = crate::leanh::lean_box((v_res_2215_) as usize);
    return v_r_2216_;
}
pub unsafe fn l_Int_Linear_emod__le__cert(
    mut v_y_2217_: *mut crate::leanh::LeanObject,
    mut v_n_2218_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    v___x_2219_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_instInhabitedExpr_default___closed__0_once),
        _init_l_Int_Linear_instInhabitedExpr_default___closed__0,
    );
    v___x_2220_ = lean_int_dec_eq(v_y_2217_, v___x_2219_);
    if v___x_2220_ == 0 {
        let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2225_: u8 = 0;
        v___x_2221_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0_once),
            _init_l_Int_Linear_Expr_toPoly_x27___closed__0,
        );
        v___x_2222_ = lean_nat_abs(v_y_2217_);
        v___x_2223_ = lean_nat_to_int(v___x_2222_);
        v___x_2224_ = lean_int_sub(v___x_2221_, v___x_2223_);
        crate::leanh::lean_dec(v___x_2223_);
        v___x_2225_ = lean_int_dec_eq(v_n_2218_, v___x_2224_);
        crate::leanh::lean_dec(v___x_2224_);
        return v___x_2225_;
    } else {
        let mut v___x_2226_: u8 = 0;
        v___x_2226_ = 0;
        return v___x_2226_;
    }
}
pub unsafe fn l_Int_Linear_emod__le__cert___boxed(
    mut v_y_2227_: *mut crate::leanh::LeanObject,
    mut v_n_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2229_: u8 = 0;
    let mut v_r_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2229_ = l_Int_Linear_emod__le__cert(v_y_2227_, v_n_2228_);
    crate::leanh::lean_dec(v_n_2228_);
    crate::leanh::lean_dec(v_y_2227_);
    v_r_2230_ = crate::leanh::lean_box((v_res_2229_) as usize);
    return v_r_2230_;
}
pub unsafe fn l_Int_Linear_le__of__le__cert(
    mut v_p_u2081_2231_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2232_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: u8 = 0;
    let mut v_k_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_2231_) == 0 {
                    if crate::leanh::lean_obj_tag(v_p_u2082_2232_) == 0 {
                        v_k_2233_ = crate::leanh::lean_ctor_get(v_p_u2081_2231_, 0);
                        v_k_2234_ = crate::leanh::lean_ctor_get(v_p_u2082_2232_, 0);
                        v___x_2235_ = lean_int_dec_le(v_k_2234_, v_k_2233_);
                        return v___x_2235_;
                    } else {
                        v___x_2236_ = 0;
                        return v___x_2236_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_p_u2082_2232_) == 0 {
                        v___x_2237_ = 0;
                        return v___x_2237_;
                    } else {
                        v_k_2238_ = crate::leanh::lean_ctor_get(v_p_u2081_2231_, 0);
                        v_v_2239_ = crate::leanh::lean_ctor_get(v_p_u2081_2231_, 1);
                        v_p_2240_ = crate::leanh::lean_ctor_get(v_p_u2081_2231_, 2);
                        v_k_2241_ = crate::leanh::lean_ctor_get(v_p_u2082_2232_, 0);
                        v_v_2242_ = crate::leanh::lean_ctor_get(v_p_u2082_2232_, 1);
                        v_p_2243_ = crate::leanh::lean_ctor_get(v_p_u2082_2232_, 2);
                        v___x_2247_ = lean_int_dec_eq(v_k_2238_, v_k_2241_);
                        if v___x_2247_ == 0 {
                            v___y_2245_ = v___x_2247_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2248_ = lean_nat_dec_eq(v_v_2239_, v_v_2242_);
                            v___y_2245_ = v___x_2248_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_2245_ == 0 {
                    return v___y_2245_;
                } else {
                    v_p_u2081_2231_ = v_p_2240_;
                    v_p_u2082_2232_ = v_p_2243_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_le__of__le__cert___boxed(
    mut v_p_u2081_2249_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2251_: u8 = 0;
    let mut v_r_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2251_ = l_Int_Linear_le__of__le__cert(v_p_u2081_2249_, v_p_u2082_2250_);
    crate::leanh::lean_dec_ref(v_p_u2082_2250_);
    crate::leanh::lean_dec_ref(v_p_u2081_2249_);
    v_r_2252_ = crate::leanh::lean_box((v_res_2251_) as usize);
    return v_r_2252_;
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter___redArg(
    mut v_p_u2081_2253_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2254_: *mut crate::leanh::LeanObject,
    mut v_h__1_2255_: *mut crate::leanh::LeanObject,
    mut v_h__2_2256_: *mut crate::leanh::LeanObject,
    mut v_h__3_2257_: *mut crate::leanh::LeanObject,
    mut v_h__4_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_2253_) == 0 {
        crate::leanh::lean_dec(v_h__4_2258_);
        crate::leanh::lean_dec(v_h__1_2255_);
        if crate::leanh::lean_obj_tag(v_p_u2082_2254_) == 0 {
            let mut v_k_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2256_);
            v_k_2259_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 0);
            crate::leanh::lean_inc(v_k_2259_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2253_, 1);
            v_k_2260_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 0);
            crate::leanh::lean_inc(v_k_2260_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2254_, 1);
            v___x_2261_ = crate::leanh::lean_apply_2(v_h__3_2257_, v_k_2259_, v_k_2260_);
            return v___x_2261_;
        } else {
            let mut v_k_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2257_);
            v_k_2262_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 0);
            crate::leanh::lean_inc(v_k_2262_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2253_, 1);
            v_k_2263_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 0);
            crate::leanh::lean_inc(v_k_2263_);
            v_v_2264_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 1);
            crate::leanh::lean_inc(v_v_2264_);
            v_p_2265_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 2);
            crate::leanh::lean_inc_ref(v_p_2265_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2254_, 3);
            v___x_2266_ = crate::leanh::lean_apply_4(
                v_h__2_2256_,
                v_k_2262_,
                v_k_2263_,
                v_v_2264_,
                v_p_2265_,
            );
            return v___x_2266_;
        }
    } else {
        crate::leanh::lean_dec(v_h__3_2257_);
        crate::leanh::lean_dec(v_h__2_2256_);
        if crate::leanh::lean_obj_tag(v_p_u2082_2254_) == 0 {
            let mut v_k_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_2258_);
            v_k_2267_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 0);
            crate::leanh::lean_inc(v_k_2267_);
            v_v_2268_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 1);
            crate::leanh::lean_inc(v_v_2268_);
            v_p_2269_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 2);
            crate::leanh::lean_inc_ref(v_p_2269_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2253_, 3);
            v_k_2270_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 0);
            crate::leanh::lean_inc(v_k_2270_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2254_, 1);
            v___x_2271_ = crate::leanh::lean_apply_4(
                v_h__1_2255_,
                v_k_2267_,
                v_v_2268_,
                v_p_2269_,
                v_k_2270_,
            );
            return v___x_2271_;
        } else {
            let mut v_k_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_2255_);
            v_k_2272_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 0);
            crate::leanh::lean_inc(v_k_2272_);
            v_v_2273_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 1);
            crate::leanh::lean_inc(v_v_2273_);
            v_p_2274_ = crate::leanh::lean_ctor_get(v_p_u2081_2253_, 2);
            crate::leanh::lean_inc_ref(v_p_2274_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2253_, 3);
            v_k_2275_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 0);
            crate::leanh::lean_inc(v_k_2275_);
            v_v_2276_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 1);
            crate::leanh::lean_inc(v_v_2276_);
            v_p_2277_ = crate::leanh::lean_ctor_get(v_p_u2082_2254_, 2);
            crate::leanh::lean_inc_ref(v_p_2277_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2254_, 3);
            v___x_2278_ = crate::leanh::lean_apply_6(
                v_h__4_2258_,
                v_k_2272_,
                v_v_2273_,
                v_p_2274_,
                v_k_2275_,
                v_v_2276_,
                v_p_2277_,
            );
            return v___x_2278_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter(
    mut v_motive_2279_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_2280_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2281_: *mut crate::leanh::LeanObject,
    mut v_h__1_2282_: *mut crate::leanh::LeanObject,
    mut v_h__2_2283_: *mut crate::leanh::LeanObject,
    mut v_h__3_2284_: *mut crate::leanh::LeanObject,
    mut v_h__4_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_u2081_2280_) == 0 {
        crate::leanh::lean_dec(v_h__4_2285_);
        crate::leanh::lean_dec(v_h__1_2282_);
        if crate::leanh::lean_obj_tag(v_p_u2082_2281_) == 0 {
            let mut v_k_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2283_);
            v_k_2286_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 0);
            crate::leanh::lean_inc(v_k_2286_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2280_, 1);
            v_k_2287_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 0);
            crate::leanh::lean_inc(v_k_2287_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2281_, 1);
            v___x_2288_ = crate::leanh::lean_apply_2(v_h__3_2284_, v_k_2286_, v_k_2287_);
            return v___x_2288_;
        } else {
            let mut v_k_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2284_);
            v_k_2289_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 0);
            crate::leanh::lean_inc(v_k_2289_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2280_, 1);
            v_k_2290_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 0);
            crate::leanh::lean_inc(v_k_2290_);
            v_v_2291_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 1);
            crate::leanh::lean_inc(v_v_2291_);
            v_p_2292_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 2);
            crate::leanh::lean_inc_ref(v_p_2292_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2281_, 3);
            v___x_2293_ = crate::leanh::lean_apply_4(
                v_h__2_2283_,
                v_k_2289_,
                v_k_2290_,
                v_v_2291_,
                v_p_2292_,
            );
            return v___x_2293_;
        }
    } else {
        crate::leanh::lean_dec(v_h__3_2284_);
        crate::leanh::lean_dec(v_h__2_2283_);
        if crate::leanh::lean_obj_tag(v_p_u2082_2281_) == 0 {
            let mut v_k_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_2285_);
            v_k_2294_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 0);
            crate::leanh::lean_inc(v_k_2294_);
            v_v_2295_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 1);
            crate::leanh::lean_inc(v_v_2295_);
            v_p_2296_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 2);
            crate::leanh::lean_inc_ref(v_p_2296_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2280_, 3);
            v_k_2297_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 0);
            crate::leanh::lean_inc(v_k_2297_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2281_, 1);
            v___x_2298_ = crate::leanh::lean_apply_4(
                v_h__1_2282_,
                v_k_2294_,
                v_v_2295_,
                v_p_2296_,
                v_k_2297_,
            );
            return v___x_2298_;
        } else {
            let mut v_k_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_2282_);
            v_k_2299_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 0);
            crate::leanh::lean_inc(v_k_2299_);
            v_v_2300_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 1);
            crate::leanh::lean_inc(v_v_2300_);
            v_p_2301_ = crate::leanh::lean_ctor_get(v_p_u2081_2280_, 2);
            crate::leanh::lean_inc_ref(v_p_2301_);
            crate::leanh::lean_dec_ref_known(v_p_u2081_2280_, 3);
            v_k_2302_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 0);
            crate::leanh::lean_inc(v_k_2302_);
            v_v_2303_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 1);
            crate::leanh::lean_inc(v_v_2303_);
            v_p_2304_ = crate::leanh::lean_ctor_get(v_p_u2082_2281_, 2);
            crate::leanh::lean_inc_ref(v_p_2304_);
            crate::leanh::lean_dec_ref_known(v_p_u2082_2281_, 3);
            v___x_2305_ = crate::leanh::lean_apply_6(
                v_h__4_2285_,
                v_k_2299_,
                v_v_2300_,
                v_p_2301_,
                v_k_2302_,
                v_v_2303_,
                v_p_2304_,
            );
            return v___x_2305_;
        }
    }
}
pub unsafe fn l_Int_Linear_not__le__of__le__cert(
    mut v_p_u2081_2306_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2307_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: u8 = 0;
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v_k_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_2306_) == 0 {
                    if crate::leanh::lean_obj_tag(v_p_u2082_2307_) == 0 {
                        v_k_2308_ = crate::leanh::lean_ctor_get(v_p_u2081_2306_, 0);
                        v_k_2309_ = crate::leanh::lean_ctor_get(v_p_u2082_2307_, 0);
                        v___x_2310_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0),
                            core::ptr::addr_of_mut!(l_Int_Linear_Expr_toPoly_x27___closed__0_once),
                            _init_l_Int_Linear_Expr_toPoly_x27___closed__0,
                        );
                        v___x_2311_ = lean_int_sub(v___x_2310_, v_k_2309_);
                        v___x_2312_ = lean_int_dec_le(v___x_2311_, v_k_2308_);
                        crate::leanh::lean_dec(v___x_2311_);
                        return v___x_2312_;
                    } else {
                        v___x_2313_ = 0;
                        return v___x_2313_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_p_u2082_2307_) == 0 {
                        v___x_2314_ = 0;
                        return v___x_2314_;
                    } else {
                        v_k_2315_ = crate::leanh::lean_ctor_get(v_p_u2081_2306_, 0);
                        v_v_2316_ = crate::leanh::lean_ctor_get(v_p_u2081_2306_, 1);
                        v_p_2317_ = crate::leanh::lean_ctor_get(v_p_u2081_2306_, 2);
                        v_k_2318_ = crate::leanh::lean_ctor_get(v_p_u2082_2307_, 0);
                        v_v_2319_ = crate::leanh::lean_ctor_get(v_p_u2082_2307_, 1);
                        v_p_2320_ = crate::leanh::lean_ctor_get(v_p_u2082_2307_, 2);
                        v___x_2324_ = lean_int_neg(v_k_2318_);
                        v___x_2325_ = lean_int_dec_eq(v_k_2315_, v___x_2324_);
                        crate::leanh::lean_dec(v___x_2324_);
                        if v___x_2325_ == 0 {
                            v___y_2322_ = v___x_2325_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2326_ = lean_nat_dec_eq(v_v_2316_, v_v_2319_);
                            v___y_2322_ = v___x_2326_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_2322_ == 0 {
                    return v___y_2322_;
                } else {
                    v_p_u2081_2306_ = v_p_2317_;
                    v_p_u2082_2307_ = v_p_2320_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_not__le__of__le__cert___boxed(
    mut v_p_u2081_2327_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2329_: u8 = 0;
    let mut v_r_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Int_Linear_not__le__of__le__cert(v_p_u2081_2327_, v_p_u2082_2328_);
    crate::leanh::lean_dec_ref(v_p_u2082_2328_);
    crate::leanh::lean_dec_ref(v_p_u2081_2327_);
    v_r_2330_ = crate::leanh::lean_box((v_res_2329_) as usize);
    return v_r_2330_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Linear(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Cooper(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Int_Linear_instInhabitedExpr_default = _init_l_Int_Linear_instInhabitedExpr_default();
    crate::leanh::lean_mark_persistent(l_Int_Linear_instInhabitedExpr_default);
    l_Int_Linear_instInhabitedExpr = _init_l_Int_Linear_instInhabitedExpr();
    crate::leanh::lean_mark_persistent(l_Int_Linear_instInhabitedExpr);
    l_Int_Linear_hugeFuel = _init_l_Int_Linear_hugeFuel();
    crate::leanh::lean_mark_persistent(l_Int_Linear_hugeFuel);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Linear(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Linear(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Cooper(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_Linear(builtin);
}

// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareCommon
// Imports: Lean.Meta.Sym.ExprPtr
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_ptr_addr, lean_uint64_mix_hash, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_eqv;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_findEntry_x3f___redArg, l_Lean_PersistentHashMap_findKeyDAux___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_hash,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_instBEqBinderInfo_beq, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    initialize_Lean_Meta_Sym_ExprPtr,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
    runtime_initialize_Lean_Meta_Sym_ExprPtr,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg;
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0: u64 =
    0;
pub static l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_instHashableAlphaKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instHashableAlphaKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instBEqAlphaKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instBEqAlphaKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [95, 95, 100, 117, 109, 109, 121, 95, 95, 0],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value
        ) as *mut leanh::LeanObject,
        9304292590189383094 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value:
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
    m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value:
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
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
    mut v_e_1186_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_e_1186_) {
        5 => {
            let mut v___x_1187_: u64 = 0;
            v___x_1187_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1187_;
        }
        6 => {
            let mut v___x_1188_: u64 = 0;
            v___x_1188_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1188_;
        }
        7 => {
            let mut v___x_1189_: u64 = 0;
            v___x_1189_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1189_;
        }
        8 => {
            let mut v___x_1190_: u64 = 0;
            v___x_1190_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1190_;
        }
        10 => {
            let mut v___x_1191_: u64 = 0;
            v___x_1191_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1191_;
        }
        11 => {
            let mut v___x_1192_: u64 = 0;
            v___x_1192_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1192_;
        }
        _ => {
            let mut v___x_1193_: u64 = 0;
            v___x_1193_ = l_Lean_Expr_hash(v_e_1186_);
            return v___x_1193_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(
    mut v_e_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1195_: u64 = 0;
    let mut v_r_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_e_1194_);
    leanh::lean_dec_ref(v_e_1194_);
    v_r_1196_ = leanh::lean_box_uint64(v_res_1195_);
    return v_r_1196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0()
-> u64 {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u64 = 0;
    v___x_1197_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1198_ = lean_uint64_of_nat(v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
    mut v_e_1199_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_d_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u64 = 0;
    let mut v___x_1204_: u64 = 0;
    let mut v___x_1205_: u64 = 0;
    let mut v_fn_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: u64 = 0;
    let mut v___x_1209_: u64 = 0;
    let mut v___x_1210_: u64 = 0;
    let mut v_binderType_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u64 = 0;
    let mut v___x_1218_: u64 = 0;
    let mut v___x_1219_: u64 = 0;
    let mut v_expr_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: u64 = 0;
    let mut v___x_1222_: u64 = 0;
    let mut v___x_1223_: u64 = 0;
    let mut v_typeName_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1228_: u64 = 0;
    let mut v___x_1229_: u64 = 0;
    let mut v___x_1230_: u64 = 0;
    let mut v___x_1231_: u64 = 0;
    let mut v___x_1232_: u64 = 0;
    let mut v___x_1233_: u64 = 0;
    let mut v_hash_1234_: u64 = 0;
    let mut v___x_1235_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_1199_) {
                5 => {
                    v_fn_1206_ = leanh::lean_ctor_get(v_e_1199_, 0);
                    v_arg_1207_ = leanh::lean_ctor_get(v_e_1199_, 1);
                    v___x_1208_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_fn_1206_,
                        );
                    v___x_1209_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_arg_1207_,
                        );
                    v___x_1210_ = lean_uint64_mix_hash(v___x_1208_, v___x_1209_);
                    return v___x_1210_;
                }
                6 => {
                    v_binderType_1211_ = leanh::lean_ctor_get(v_e_1199_, 1);
                    v_body_1212_ = leanh::lean_ctor_get(v_e_1199_, 2);
                    v_d_1201_ = v_binderType_1211_;
                    v_b_1202_ = v_body_1212_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_binderType_1213_ = leanh::lean_ctor_get(v_e_1199_, 1);
                    v_body_1214_ = leanh::lean_ctor_get(v_e_1199_, 2);
                    v_d_1201_ = v_binderType_1213_;
                    v_b_1202_ = v_body_1214_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_value_1215_ = leanh::lean_ctor_get(v_e_1199_, 2);
                    v_body_1216_ = leanh::lean_ctor_get(v_e_1199_, 3);
                    v___x_1217_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_value_1215_,
                        );
                    v___x_1218_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_body_1216_,
                        );
                    v___x_1219_ = lean_uint64_mix_hash(v___x_1217_, v___x_1218_);
                    return v___x_1219_;
                }
                10 => {
                    v_expr_1220_ = leanh::lean_ctor_get(v_e_1199_, 1);
                    v___x_1221_ = 13u64;
                    v___x_1222_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_expr_1220_,
                        );
                    v___x_1223_ = lean_uint64_mix_hash(v___x_1221_, v___x_1222_);
                    return v___x_1223_;
                }
                11 => {
                    v_typeName_1224_ = leanh::lean_ctor_get(v_e_1199_, 0);
                    v_idx_1225_ = leanh::lean_ctor_get(v_e_1199_, 1);
                    v_struct_1226_ = leanh::lean_ctor_get(v_e_1199_, 2);
                    if leanh::lean_obj_tag(v_typeName_1224_) == 0 {
                        v___x_1233_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once), _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0);
                        v___y_1228_ = v___x_1233_;
                        state = 2;
                        continue;
                    } else {
                        v_hash_1234_ = leanh::lean_ctor_get_uint64(
                            v_typeName_1224_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1228_ = v_hash_1234_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_1235_ = l_Lean_Expr_hash(v_e_1199_);
                    return v___x_1235_;
                }
            },
            1 => {
                v___x_1203_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                    v_d_1201_,
                );
                v___x_1204_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                    v_b_1202_,
                );
                v___x_1205_ = lean_uint64_mix_hash(v___x_1203_, v___x_1204_);
                return v___x_1205_;
            }
            2 => {
                v___x_1229_ = lean_uint64_of_nat(v_idx_1225_);
                v___x_1230_ = lean_uint64_mix_hash(v___y_1228_, v___x_1229_);
                v___x_1231_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                    v_struct_1226_,
                );
                v___x_1232_ = lean_uint64_mix_hash(v___x_1230_, v___x_1231_);
                return v___x_1232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(
    mut v_e_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1237_: u64 = 0;
    let mut v_r_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1236_);
    leanh::lean_dec_ref(v_e_1236_);
    v_r_1238_ = leanh::lean_box_uint64(v_res_1237_);
    return v_r_1238_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
    mut v_e_u2081_1239_: *mut leanh::LeanObject,
    mut v_e_u2082_1240_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fn_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: u8 = 0;
    let mut v___x_1247_: u8 = 0;
    let mut v_binderType_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1253_: u8 = 0;
    let mut v___x_1254_: u8 = 0;
    let mut v_binderType_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: u8 = 0;
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: u8 = 0;
    let mut v_value_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: u8 = 0;
    let mut v___x_1268_: u8 = 0;
    let mut v_data_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut v___x_1274_: u8 = 0;
    let mut v___x_1275_: u8 = 0;
    let mut v_typeName_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1283_: u8 = 0;
    let mut v___x_1284_: u8 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: u8 = 0;
    let mut v___x_1288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_e_u2081_1239_) {
                    5 => {
                        if leanh::lean_obj_tag(v_e_u2082_1240_) == 5 {
                            v_fn_1241_ = leanh::lean_ctor_get(v_e_u2081_1239_, 0);
                            leanh::lean_inc_ref(v_fn_1241_);
                            v_arg_1242_ = leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            leanh::lean_inc_ref(v_arg_1242_);
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            v_fn_1243_ = leanh::lean_ctor_get(v_e_u2082_1240_, 0);
                            leanh::lean_inc_ref(v_fn_1243_);
                            v_arg_1244_ = leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            leanh::lean_inc_ref(v_arg_1244_);
                            leanh::lean_dec_ref_known(v_e_u2082_1240_, 2);
                            v___x_1245_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1241_, v_fn_1243_);
                            leanh::lean_dec_ref(v_fn_1243_);
                            leanh::lean_dec_ref(v_fn_1241_);
                            if v___x_1245_ == 0 {
                                leanh::lean_dec_ref(v_arg_1244_);
                                leanh::lean_dec_ref(v_arg_1242_);
                                return v___x_1245_;
                            } else {
                                v___x_1246_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1242_, v_arg_1244_);
                                leanh::lean_dec_ref(v_arg_1244_);
                                leanh::lean_dec_ref(v_arg_1242_);
                                return v___x_1246_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1247_ = 0;
                            return v___x_1247_;
                        }
                    }
                    6 => {
                        if leanh::lean_obj_tag(v_e_u2082_1240_) == 6 {
                            v_binderType_1248_ = leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            leanh::lean_inc_ref(v_binderType_1248_);
                            v_body_1249_ = leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            leanh::lean_inc_ref(v_body_1249_);
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            v_binderType_1250_ = leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            leanh::lean_inc_ref(v_binderType_1250_);
                            v_body_1251_ = leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            leanh::lean_inc_ref(v_body_1251_);
                            leanh::lean_dec_ref_known(v_e_u2082_1240_, 3);
                            v___x_1252_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1248_, v_binderType_1250_);
                            leanh::lean_dec_ref(v_binderType_1250_);
                            leanh::lean_dec_ref(v_binderType_1248_);
                            if v___x_1252_ == 0 {
                                leanh::lean_dec_ref(v_body_1251_);
                                leanh::lean_dec_ref(v_body_1249_);
                                return v___x_1252_;
                            } else {
                                v___x_1253_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1249_, v_body_1251_);
                                leanh::lean_dec_ref(v_body_1251_);
                                leanh::lean_dec_ref(v_body_1249_);
                                return v___x_1253_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1254_ = 0;
                            return v___x_1254_;
                        }
                    }
                    7 => {
                        if leanh::lean_obj_tag(v_e_u2082_1240_) == 7 {
                            v_binderType_1255_ = leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            leanh::lean_inc_ref(v_binderType_1255_);
                            v_body_1256_ = leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            leanh::lean_inc_ref(v_body_1256_);
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            v_binderType_1257_ = leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            leanh::lean_inc_ref(v_binderType_1257_);
                            v_body_1258_ = leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            leanh::lean_inc_ref(v_body_1258_);
                            leanh::lean_dec_ref_known(v_e_u2082_1240_, 3);
                            v___x_1259_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1255_, v_binderType_1257_);
                            leanh::lean_dec_ref(v_binderType_1257_);
                            leanh::lean_dec_ref(v_binderType_1255_);
                            if v___x_1259_ == 0 {
                                leanh::lean_dec_ref(v_body_1258_);
                                leanh::lean_dec_ref(v_body_1256_);
                                return v___x_1259_;
                            } else {
                                v___x_1260_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1256_, v_body_1258_);
                                leanh::lean_dec_ref(v_body_1258_);
                                leanh::lean_dec_ref(v_body_1256_);
                                return v___x_1260_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1261_ = 0;
                            return v___x_1261_;
                        }
                    }
                    8 => {
                        if leanh::lean_obj_tag(v_e_u2082_1240_) == 8 {
                            v_value_1262_ = leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            leanh::lean_inc_ref(v_value_1262_);
                            v_body_1263_ = leanh::lean_ctor_get(v_e_u2081_1239_, 3);
                            leanh::lean_inc_ref(v_body_1263_);
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 4);
                            v_value_1264_ = leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            leanh::lean_inc_ref(v_value_1264_);
                            v_body_1265_ = leanh::lean_ctor_get(v_e_u2082_1240_, 3);
                            leanh::lean_inc_ref(v_body_1265_);
                            leanh::lean_dec_ref_known(v_e_u2082_1240_, 4);
                            v___x_1266_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1262_, v_value_1264_);
                            leanh::lean_dec_ref(v_value_1264_);
                            leanh::lean_dec_ref(v_value_1262_);
                            if v___x_1266_ == 0 {
                                leanh::lean_dec_ref(v_body_1265_);
                                leanh::lean_dec_ref(v_body_1263_);
                                return v___x_1266_;
                            } else {
                                v___x_1267_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1263_, v_body_1265_);
                                leanh::lean_dec_ref(v_body_1265_);
                                leanh::lean_dec_ref(v_body_1263_);
                                return v___x_1267_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 4);
                            leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1268_ = 0;
                            return v___x_1268_;
                        }
                    }
                    10 => {
                        if leanh::lean_obj_tag(v_e_u2082_1240_) == 10 {
                            v_data_1269_ = leanh::lean_ctor_get(v_e_u2081_1239_, 0);
                            leanh::lean_inc(v_data_1269_);
                            v_expr_1270_ = leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            leanh::lean_inc_ref(v_expr_1270_);
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            v_data_1271_ = leanh::lean_ctor_get(v_e_u2082_1240_, 0);
                            leanh::lean_inc(v_data_1271_);
                            v_expr_1272_ = leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            leanh::lean_inc_ref(v_expr_1272_);
                            leanh::lean_dec_ref_known(v_e_u2082_1240_, 2);
                            v___x_1273_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1270_, v_expr_1272_);
                            leanh::lean_dec_ref(v_expr_1272_);
                            leanh::lean_dec_ref(v_expr_1270_);
                            if v___x_1273_ == 0 {
                                leanh::lean_dec(v_data_1271_);
                                leanh::lean_dec(v_data_1269_);
                                return v___x_1273_;
                            } else {
                                v___x_1274_ = l_Lean_KVMap_eqv(v_data_1269_, v_data_1271_);
                                return v___x_1274_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1275_ = 0;
                            return v___x_1275_;
                        }
                    }
                    11 => {
                        if leanh::lean_obj_tag(v_e_u2082_1240_) == 11 {
                            v_typeName_1276_ = leanh::lean_ctor_get(v_e_u2081_1239_, 0);
                            leanh::lean_inc(v_typeName_1276_);
                            v_idx_1277_ = leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            leanh::lean_inc(v_idx_1277_);
                            v_struct_1278_ = leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            leanh::lean_inc_ref(v_struct_1278_);
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            v_typeName_1279_ = leanh::lean_ctor_get(v_e_u2082_1240_, 0);
                            leanh::lean_inc(v_typeName_1279_);
                            v_idx_1280_ = leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            leanh::lean_inc(v_idx_1280_);
                            v_struct_1281_ = leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            leanh::lean_inc_ref(v_struct_1281_);
                            leanh::lean_dec_ref_known(v_e_u2082_1240_, 3);
                            v___x_1285_ = lean_name_eq(v_typeName_1276_, v_typeName_1279_);
                            leanh::lean_dec(v_typeName_1279_);
                            leanh::lean_dec(v_typeName_1276_);
                            if v___x_1285_ == 0 {
                                leanh::lean_dec(v_idx_1280_);
                                leanh::lean_dec(v_idx_1277_);
                                v___y_1283_ = v___x_1285_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1286_ = lean_nat_dec_eq(v_idx_1277_, v_idx_1280_);
                                leanh::lean_dec(v_idx_1280_);
                                leanh::lean_dec(v_idx_1277_);
                                v___y_1283_ = v___x_1286_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1287_ = 0;
                            return v___x_1287_;
                        }
                    }
                    _ => {
                        v___x_1288_ = lean_expr_eqv(v_e_u2081_1239_, v_e_u2082_1240_);
                        leanh::lean_dec_ref(v_e_u2082_1240_);
                        leanh::lean_dec_ref(v_e_u2081_1239_);
                        return v___x_1288_;
                    }
                }
            }
            1 => {
                if v___y_1283_ == 0 {
                    leanh::lean_dec_ref(v_struct_1281_);
                    leanh::lean_dec_ref(v_struct_1278_);
                    return v___y_1283_;
                } else {
                    v___x_1284_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_struct_1278_,
                            v_struct_1281_,
                        );
                    leanh::lean_dec_ref(v_struct_1281_);
                    leanh::lean_dec_ref(v_struct_1278_);
                    return v___x_1284_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(
    mut v_e_u2081_1289_: *mut leanh::LeanObject,
    mut v_e_u2082_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1291_: u8 = 0;
    let mut v_r_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
        v_e_u2081_1289_,
        v_e_u2082_1290_,
    );
    v_r_1292_ = leanh::lean_box((v_res_1291_) as usize);
    return v_r_1292_;
}
pub unsafe fn l_Lean_Meta_Sym_instHashableAlphaKey___private__1(
    mut v_k_1293_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_1294_: u64 = 0;
    v___x_1294_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(
    mut v_k_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1296_: u64 = 0;
    let mut v_r_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_1295_);
    leanh::lean_dec_ref(v_k_1295_);
    v_r_1297_ = leanh::lean_box_uint64(v_res_1296_);
    return v_r_1297_;
}
pub unsafe fn l_Lean_Meta_Sym_instBEqAlphaKey___private__1(
    mut v_k_u2081_1300_: *mut leanh::LeanObject,
    mut v_k_u2082_1301_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1302_: u8 = 0;
    v___x_1302_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
        v_k_u2081_1300_,
        v_k_u2082_1301_,
    );
    return v___x_1302_;
}
pub unsafe fn l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(
    mut v_k_u2081_1303_: *mut leanh::LeanObject,
    mut v_k_u2082_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1305_: u8 = 0;
    let mut v_r_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1305_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_1303_, v_k_u2082_1304_);
    v_r_1306_ = leanh::lean_box((v_res_1305_) as usize);
    return v_r_1306_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = leanh::lean_box(0);
    v___x_1313_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1;
    v___x_1314_ = l_Lean_mkConst(v___x_1313_, v___x_1312_);
    return v___x_1314_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy()
-> *mut leanh::LeanObject {
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once
        ),
        _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2,
    );
    return v___x_1315_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(
    mut v_keys_1316_: *mut leanh::LeanObject,
    mut v_i_1317_: *mut leanh::LeanObject,
    mut v_k_1318_: *mut leanh::LeanObject,
    mut v_k_u2080_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v_k_x27_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1320_ = lean_array_get_size(v_keys_1316_);
                v___x_1321_ = lean_nat_dec_lt(v_i_1317_, v___x_1320_);
                if v___x_1321_ == 0 {
                    leanh::lean_dec_ref(v_k_1318_);
                    leanh::lean_dec(v_i_1317_);
                    leanh::lean_inc_ref(v_k_u2080_1319_);
                    return v_k_u2080_1319_;
                } else {
                    v_k_x27_1322_ = lean_array_fget_borrowed(v_keys_1316_, v_i_1317_);
                    leanh::lean_inc(v_k_x27_1322_);
                    leanh::lean_inc_ref(v_k_1318_);
                    v___x_1323_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_1318_,
                            v_k_x27_1322_,
                        );
                    if v___x_1323_ == 0 {
                        v___x_1324_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1325_ = lean_nat_add(v_i_1317_, v___x_1324_);
                        leanh::lean_dec(v_i_1317_);
                        v_i_1317_ = v___x_1325_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_1318_);
                        leanh::lean_dec(v_i_1317_);
                        leanh::lean_inc(v_k_x27_1322_);
                        return v_k_x27_1322_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(
    mut v_keys_1327_: *mut leanh::LeanObject,
    mut v_i_1328_: *mut leanh::LeanObject,
    mut v_k_1329_: *mut leanh::LeanObject,
    mut v_k_u2080_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_1327_, v_i_1328_, v_k_1329_, v_k_u2080_1330_);
    leanh::lean_dec_ref(v_k_u2080_1330_);
    leanh::lean_dec_ref(v_keys_1327_);
    return v_res_1331_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1332_: usize = 0;
    let mut v___x_1333_: usize = 0;
    let mut v___x_1334_: usize = 0;
    v___x_1332_ = 5usize;
    v___x_1333_ = 1usize;
    v___x_1334_ = lean_usize_shift_left(v___x_1333_, v___x_1332_);
    return v___x_1334_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1335_: usize = 0;
    let mut v___x_1336_: usize = 0;
    let mut v___x_1337_: usize = 0;
    v___x_1335_ = 1usize;
    v___x_1336_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0);
    v___x_1337_ = lean_usize_sub(v___x_1336_, v___x_1335_);
    return v___x_1337_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(
    mut v_x_1338_: *mut leanh::LeanObject,
    mut v_x_1339_: usize,
    mut v_x_1340_: *mut leanh::LeanObject,
    mut v_x_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: usize = 0;
    let mut v___x_1345_: usize = 0;
    let mut v___x_1346_: usize = 0;
    let mut v_j_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    let mut v_node_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: usize = 0;
    let mut v_ks_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1338_) == 0 {
                    v_es_1342_ = leanh::lean_ctor_get(v_x_1338_, 0);
                    leanh::lean_inc_ref(v_es_1342_);
                    leanh::lean_dec_ref_known(v_x_1338_, 1);
                    v___x_1343_ = leanh::lean_box(2);
                    v___x_1344_ = 5usize;
                    v___x_1345_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
                    v___x_1346_ = lean_usize_land(v_x_1339_, v___x_1345_);
                    v_j_1347_ = lean_usize_to_nat(v___x_1346_);
                    v___x_1348_ = lean_array_get(v___x_1343_, v_es_1342_, v_j_1347_);
                    leanh::lean_dec(v_j_1347_);
                    leanh::lean_dec_ref(v_es_1342_);
                    match leanh::lean_obj_tag(v___x_1348_) {
                        0 => {
                            v_key_1349_ = leanh::lean_ctor_get(v___x_1348_, 0);
                            leanh::lean_inc_n(v_key_1349_, 2);
                            leanh::lean_dec_ref_known(v___x_1348_, 2);
                            v___x_1350_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_1340_,
                                    v_key_1349_,
                                );
                            if v___x_1350_ == 0 {
                                leanh::lean_dec(v_key_1349_);
                                leanh::lean_inc_ref(v_x_1341_);
                                return v_x_1341_;
                            } else {
                                return v_key_1349_;
                            }
                        }
                        1 => {
                            v_node_1351_ = leanh::lean_ctor_get(v___x_1348_, 0);
                            leanh::lean_inc(v_node_1351_);
                            leanh::lean_dec_ref_known(v___x_1348_, 1);
                            v___x_1352_ = lean_usize_shift_right(v_x_1339_, v___x_1344_);
                            v_x_1338_ = v_node_1351_;
                            v_x_1339_ = v___x_1352_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_x_1340_);
                            leanh::lean_inc_ref(v_x_1341_);
                            return v_x_1341_;
                        }
                    }
                } else {
                    v_ks_1354_ = leanh::lean_ctor_get(v_x_1338_, 0);
                    leanh::lean_inc_ref(v_ks_1354_);
                    leanh::lean_dec_ref_known(v_x_1338_, 2);
                    v___x_1355_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1356_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_1354_, v___x_1355_, v_x_1340_, v_x_1341_);
                    leanh::lean_dec_ref(v_ks_1354_);
                    return v___x_1356_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(
    mut v_x_1357_: *mut leanh::LeanObject,
    mut v_x_1358_: *mut leanh::LeanObject,
    mut v_x_1359_: *mut leanh::LeanObject,
    mut v_x_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1916__boxed_1361_: usize = 0;
    let mut v_res_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1916__boxed_1361_ = leanh::lean_unbox_usize(v_x_1358_);
    leanh::lean_dec(v_x_1358_);
    v_res_1362_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_1357_, v_x_1916__boxed_1361_, v_x_1359_, v_x_1360_);
    leanh::lean_dec_ref(v_x_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(
    mut v_x_1363_: *mut leanh::LeanObject,
    mut v_x_1364_: *mut leanh::LeanObject,
    mut v_x_1365_: *mut leanh::LeanObject,
    mut v_x_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1371_: u8 = 0;
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1367_ = leanh::lean_ctor_get(v_x_1363_, 0);
                v_vs_1368_ = leanh::lean_ctor_get(v_x_1363_, 1);
                v_isSharedCheck_1392_ = (!leanh::lean_is_exclusive(v_x_1363_)) as u8;
                if v_isSharedCheck_1392_ == 0 {
                    v___x_1370_ = v_x_1363_;
                    v_isShared_1371_ = v_isSharedCheck_1392_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1368_);
                    leanh::lean_inc(v_ks_1367_);
                    leanh::lean_dec(v_x_1363_);
                    v___x_1370_ = leanh::lean_box(0);
                    v_isShared_1371_ = v_isSharedCheck_1392_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1372_ = lean_array_get_size(v_ks_1367_);
                v___x_1373_ = lean_nat_dec_lt(v_x_1364_, v___x_1372_);
                if v___x_1373_ == 0 {
                    leanh::lean_dec(v_x_1364_);
                    v___x_1374_ = lean_array_push(v_ks_1367_, v_x_1365_);
                    v___x_1375_ = lean_array_push(v_vs_1368_, v_x_1366_);
                    if v_isShared_1371_ == 0 {
                        leanh::lean_ctor_set(v___x_1370_, 1, v___x_1375_);
                        leanh::lean_ctor_set(v___x_1370_, 0, v___x_1374_);
                        v___x_1377_ = v___x_1370_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1378_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1374_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
                        v___x_1377_ = v_reuseFailAlloc_1378_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1379_ = lean_array_fget_borrowed(v_ks_1367_, v_x_1364_);
                    leanh::lean_inc(v_k_x27_1379_);
                    leanh::lean_inc_ref(v_x_1365_);
                    v___x_1380_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_x_1365_,
                            v_k_x27_1379_,
                        );
                    if v___x_1380_ == 0 {
                        if v_isShared_1371_ == 0 {
                            v___x_1382_ = v___x_1370_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1386_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_ks_1367_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_vs_1368_);
                            v___x_1382_ = v_reuseFailAlloc_1386_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1387_ = lean_array_fset(v_ks_1367_, v_x_1364_, v_x_1365_);
                        v___x_1388_ = lean_array_fset(v_vs_1368_, v_x_1364_, v_x_1366_);
                        leanh::lean_dec(v_x_1364_);
                        if v_isShared_1371_ == 0 {
                            leanh::lean_ctor_set(v___x_1370_, 1, v___x_1388_);
                            leanh::lean_ctor_set(v___x_1370_, 0, v___x_1387_);
                            v___x_1390_ = v___x_1370_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1391_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1387_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1388_);
                            v___x_1390_ = v_reuseFailAlloc_1391_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1377_;
            }
            3 => {
                v___x_1383_ = leanh::lean_unsigned_to_nat(1);
                v___x_1384_ = lean_nat_add(v_x_1364_, v___x_1383_);
                leanh::lean_dec(v_x_1364_);
                v_x_1363_ = v___x_1382_;
                v_x_1364_ = v___x_1384_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(
    mut v_n_1393_: *mut leanh::LeanObject,
    mut v_k_1394_: *mut leanh::LeanObject,
    mut v_v_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = leanh::lean_unsigned_to_nat(0);
    v___x_1397_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_1393_, v___x_1396_, v_k_1394_, v_v_1395_);
    return v___x_1397_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1398_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1398_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(
    mut v_x_1399_: *mut leanh::LeanObject,
    mut v_x_1400_: usize,
    mut v_x_1401_: usize,
    mut v_x_1402_: *mut leanh::LeanObject,
    mut v_x_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: usize = 0;
    let mut v___x_1406_: usize = 0;
    let mut v___x_1407_: usize = 0;
    let mut v___x_1408_: usize = 0;
    let mut v_j_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v_v_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut v_node_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1441_: usize = 0;
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1448_: u8 = 0;
    let mut v_unused_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: u8 = 0;
    let mut v_ks_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: usize = 0;
    let mut v___x_1466_: u8 = 0;
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v_reuseFailAlloc_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1399_) == 0 {
                    v_es_1404_ = leanh::lean_ctor_get(v_x_1399_, 0);
                    v___x_1405_ = 5usize;
                    v___x_1406_ = 1usize;
                    v___x_1407_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
                    v___x_1408_ = lean_usize_land(v_x_1400_, v___x_1407_);
                    v_j_1409_ = lean_usize_to_nat(v___x_1408_);
                    v___x_1410_ = lean_array_get_size(v_es_1404_);
                    v___x_1411_ = lean_nat_dec_lt(v_j_1409_, v___x_1410_);
                    if v___x_1411_ == 0 {
                        leanh::lean_dec(v_j_1409_);
                        leanh::lean_dec(v_x_1403_);
                        leanh::lean_dec_ref(v_x_1402_);
                        return v_x_1399_;
                    } else {
                        leanh::lean_inc_ref(v_es_1404_);
                        v_isSharedCheck_1448_ = (!leanh::lean_is_exclusive(v_x_1399_)) as u8;
                        if v_isSharedCheck_1448_ == 0 {
                            v_unused_1449_ = leanh::lean_ctor_get(v_x_1399_, 0);
                            leanh::lean_dec(v_unused_1449_);
                            v___x_1413_ = v_x_1399_;
                            v_isShared_1414_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1399_);
                            v___x_1413_ = leanh::lean_box(0);
                            v_isShared_1414_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1450_ = leanh::lean_ctor_get(v_x_1399_, 0);
                    v_vs_1451_ = leanh::lean_ctor_get(v_x_1399_, 1);
                    v_isSharedCheck_1471_ = (!leanh::lean_is_exclusive(v_x_1399_)) as u8;
                    if v_isSharedCheck_1471_ == 0 {
                        v___x_1453_ = v_x_1399_;
                        v_isShared_1454_ = v_isSharedCheck_1471_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1451_);
                        leanh::lean_inc(v_ks_1450_);
                        leanh::lean_dec(v_x_1399_);
                        v___x_1453_ = leanh::lean_box(0);
                        v_isShared_1454_ = v_isSharedCheck_1471_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1415_ = lean_array_fget(v_es_1404_, v_j_1409_);
                v___x_1416_ = leanh::lean_box(0);
                v_xs_x27_1417_ = lean_array_fset(v_es_1404_, v_j_1409_, v___x_1416_);
                match leanh::lean_obj_tag(v_v_1415_) {
                    0 => {
                        v_key_1424_ = leanh::lean_ctor_get(v_v_1415_, 0);
                        v_val_1425_ = leanh::lean_ctor_get(v_v_1415_, 1);
                        v_isSharedCheck_1435_ = (!leanh::lean_is_exclusive(v_v_1415_)) as u8;
                        if v_isSharedCheck_1435_ == 0 {
                            v___x_1427_ = v_v_1415_;
                            v_isShared_1428_ = v_isSharedCheck_1435_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1425_);
                            leanh::lean_inc(v_key_1424_);
                            leanh::lean_dec(v_v_1415_);
                            v___x_1427_ = leanh::lean_box(0);
                            v_isShared_1428_ = v_isSharedCheck_1435_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1436_ = leanh::lean_ctor_get(v_v_1415_, 0);
                        v_isSharedCheck_1446_ = (!leanh::lean_is_exclusive(v_v_1415_)) as u8;
                        if v_isSharedCheck_1446_ == 0 {
                            v___x_1438_ = v_v_1415_;
                            v_isShared_1439_ = v_isSharedCheck_1446_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1436_);
                            leanh::lean_dec(v_v_1415_);
                            v___x_1438_ = leanh::lean_box(0);
                            v_isShared_1439_ = v_isSharedCheck_1446_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1447_, 0, v_x_1402_);
                        leanh::lean_ctor_set(v___x_1447_, 1, v_x_1403_);
                        v___y_1419_ = v___x_1447_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1420_ = lean_array_fset(v_xs_x27_1417_, v_j_1409_, v___y_1419_);
                leanh::lean_dec(v_j_1409_);
                if v_isShared_1414_ == 0 {
                    leanh::lean_ctor_set(v___x_1413_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
                    v___x_1422_ = v_reuseFailAlloc_1423_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1422_;
            }
            4 => {
                leanh::lean_inc(v_key_1424_);
                leanh::lean_inc_ref(v_x_1402_);
                v___x_1429_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                    v_x_1402_,
                    v_key_1424_,
                );
                if v___x_1429_ == 0 {
                    leanh::lean_del_object(v___x_1427_);
                    v___x_1430_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1424_,
                        v_val_1425_,
                        v_x_1402_,
                        v_x_1403_,
                    );
                    v___x_1431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1431_, 0, v___x_1430_);
                    v___y_1419_ = v___x_1431_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1425_);
                    leanh::lean_dec(v_key_1424_);
                    if v_isShared_1428_ == 0 {
                        leanh::lean_ctor_set(v___x_1427_, 1, v_x_1403_);
                        leanh::lean_ctor_set(v___x_1427_, 0, v_x_1402_);
                        v___x_1433_ = v___x_1427_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1434_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_x_1402_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_x_1403_);
                        v___x_1433_ = v_reuseFailAlloc_1434_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1419_ = v___x_1433_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1440_ = lean_usize_shift_right(v_x_1400_, v___x_1405_);
                v___x_1441_ = lean_usize_add(v_x_1401_, v___x_1406_);
                v___x_1442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_1436_, v___x_1440_, v___x_1441_, v_x_1402_, v_x_1403_);
                if v_isShared_1439_ == 0 {
                    leanh::lean_ctor_set(v___x_1438_, 0, v___x_1442_);
                    v___x_1444_ = v___x_1438_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                    v___x_1444_ = v_reuseFailAlloc_1445_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1419_ = v___x_1444_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1454_ == 0 {
                    v___x_1456_ = v___x_1453_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_ks_1450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_vs_1451_);
                    v___x_1456_ = v_reuseFailAlloc_1470_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1457_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_1456_, v_x_1402_, v_x_1403_);
                v___x_1465_ = 7usize;
                v___x_1466_ = lean_usize_dec_le(v___x_1465_, v_x_1401_);
                if v___x_1466_ == 0 {
                    v___x_1467_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1457_);
                    v___x_1468_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1469_ = lean_nat_dec_lt(v___x_1467_, v___x_1468_);
                    leanh::lean_dec(v___x_1467_);
                    v___y_1459_ = v___x_1469_;
                    state = 10;
                    continue;
                } else {
                    v___y_1459_ = v___x_1466_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1459_ == 0 {
                    v_ks_1460_ = leanh::lean_ctor_get(v_newNode_1457_, 0);
                    leanh::lean_inc_ref(v_ks_1460_);
                    v_vs_1461_ = leanh::lean_ctor_get(v_newNode_1457_, 1);
                    leanh::lean_inc_ref(v_vs_1461_);
                    leanh::lean_dec_ref(v_newNode_1457_);
                    v___x_1462_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1463_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
                    v___x_1464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_1401_, v_ks_1460_, v_vs_1461_, v___x_1462_, v___x_1463_);
                    leanh::lean_dec_ref(v_vs_1461_);
                    leanh::lean_dec_ref(v_ks_1460_);
                    return v___x_1464_;
                } else {
                    return v_newNode_1457_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(
    mut v_depth_1472_: usize,
    mut v_keys_1473_: *mut leanh::LeanObject,
    mut v_vals_1474_: *mut leanh::LeanObject,
    mut v_i_1475_: *mut leanh::LeanObject,
    mut v_entries_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v_k_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u64 = 0;
    let mut v_h_1482_: usize = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: usize = 0;
    let mut v___x_1486_: usize = 0;
    let mut v___x_1487_: usize = 0;
    let mut v_h_1488_: usize = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_array_get_size(v_keys_1473_);
                v___x_1478_ = lean_nat_dec_lt(v_i_1475_, v___x_1477_);
                if v___x_1478_ == 0 {
                    leanh::lean_dec(v_i_1475_);
                    return v_entries_1476_;
                } else {
                    v_k_1479_ = lean_array_fget_borrowed(v_keys_1473_, v_i_1475_);
                    v_v_1480_ = lean_array_fget_borrowed(v_vals_1474_, v_i_1475_);
                    v___x_1481_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                            v_k_1479_,
                        );
                    v_h_1482_ = lean_uint64_to_usize(v___x_1481_);
                    v___x_1483_ = 5usize;
                    v___x_1484_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1485_ = 1usize;
                    v___x_1486_ = lean_usize_sub(v_depth_1472_, v___x_1485_);
                    v___x_1487_ = lean_usize_mul(v___x_1483_, v___x_1486_);
                    v_h_1488_ = lean_usize_shift_right(v_h_1482_, v___x_1487_);
                    v___x_1489_ = lean_nat_add(v_i_1475_, v___x_1484_);
                    leanh::lean_dec(v_i_1475_);
                    leanh::lean_inc(v_v_1480_);
                    leanh::lean_inc(v_k_1479_);
                    v___x_1490_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_1476_, v_h_1488_, v_depth_1472_, v_k_1479_, v_v_1480_);
                    v_i_1475_ = v___x_1489_;
                    v_entries_1476_ = v___x_1490_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(
    mut v_depth_1492_: *mut leanh::LeanObject,
    mut v_keys_1493_: *mut leanh::LeanObject,
    mut v_vals_1494_: *mut leanh::LeanObject,
    mut v_i_1495_: *mut leanh::LeanObject,
    mut v_entries_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1497_: usize = 0;
    let mut v_res_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1497_ = leanh::lean_unbox_usize(v_depth_1492_);
    leanh::lean_dec(v_depth_1492_);
    v_res_1498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_1497_, v_keys_1493_, v_vals_1494_, v_i_1495_, v_entries_1496_);
    leanh::lean_dec_ref(v_vals_1494_);
    leanh::lean_dec_ref(v_keys_1493_);
    return v_res_1498_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(
    mut v_x_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
    mut v_x_1501_: *mut leanh::LeanObject,
    mut v_x_1502_: *mut leanh::LeanObject,
    mut v_x_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2046__boxed_1504_: usize = 0;
    let mut v_x_2047__boxed_1505_: usize = 0;
    let mut v_res_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2046__boxed_1504_ = leanh::lean_unbox_usize(v_x_1500_);
    leanh::lean_dec(v_x_1500_);
    v_x_2047__boxed_1505_ = leanh::lean_unbox_usize(v_x_1501_);
    leanh::lean_dec(v_x_1501_);
    v_res_1506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_1499_, v_x_2046__boxed_1504_, v_x_2047__boxed_1505_, v_x_1502_, v_x_1503_);
    return v_res_1506_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(
    mut v_x_1507_: *mut leanh::LeanObject,
    mut v_x_1508_: *mut leanh::LeanObject,
    mut v_x_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1510_: u64 = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1508_);
    v___x_1511_ = lean_uint64_to_usize(v___x_1510_);
    v___x_1512_ = 1usize;
    v___x_1513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_1507_, v___x_1511_, v___x_1512_, v_x_1508_, v_x_1509_);
    return v___x_1513_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(
    mut v_a_1514_: *mut leanh::LeanObject,
    mut v_b_1515_: *mut leanh::LeanObject,
    mut v_x_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1516_) == 0 {
                    leanh::lean_dec(v_b_1515_);
                    leanh::lean_dec_ref(v_a_1514_);
                    return v_x_1516_;
                } else {
                    v_key_1517_ = leanh::lean_ctor_get(v_x_1516_, 0);
                    v_value_1518_ = leanh::lean_ctor_get(v_x_1516_, 1);
                    v_tail_1519_ = leanh::lean_ctor_get(v_x_1516_, 2);
                    v_isSharedCheck_1531_ = (!leanh::lean_is_exclusive(v_x_1516_)) as u8;
                    if v_isSharedCheck_1531_ == 0 {
                        v___x_1521_ = v_x_1516_;
                        v_isShared_1522_ = v_isSharedCheck_1531_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1519_);
                        leanh::lean_inc(v_value_1518_);
                        leanh::lean_inc(v_key_1517_);
                        leanh::lean_dec(v_x_1516_);
                        v___x_1521_ = leanh::lean_box(0);
                        v_isShared_1522_ = v_isSharedCheck_1531_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1523_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_key_1517_,
                        v_a_1514_,
                    );
                if v___x_1523_ == 0 {
                    v___x_1524_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_1514_, v_b_1515_, v_tail_1519_);
                    if v_isShared_1522_ == 0 {
                        leanh::lean_ctor_set(v___x_1521_, 2, v___x_1524_);
                        v___x_1526_ = v___x_1521_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1527_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_key_1517_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_value_1518_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 2, v___x_1524_);
                        v___x_1526_ = v_reuseFailAlloc_1527_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1518_);
                    leanh::lean_dec(v_key_1517_);
                    if v_isShared_1522_ == 0 {
                        leanh::lean_ctor_set(v___x_1521_, 1, v_b_1515_);
                        leanh::lean_ctor_set(v___x_1521_, 0, v_a_1514_);
                        v___x_1529_ = v___x_1521_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1530_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1514_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_b_1515_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_tail_1519_);
                        v___x_1529_ = v_reuseFailAlloc_1530_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1526_;
            }
            3 => {
                return v___x_1529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(
    mut v_x_1532_: *mut leanh::LeanObject,
    mut v_x_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1539_: u8 = 0;
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u64 = 0;
    let mut v___x_1542_: u64 = 0;
    let mut v___x_1543_: u64 = 0;
    let mut v_fold_1544_: u64 = 0;
    let mut v___x_1545_: u64 = 0;
    let mut v___x_1546_: u64 = 0;
    let mut v___x_1547_: u64 = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: usize = 0;
    let mut v___x_1550_: usize = 0;
    let mut v___x_1551_: usize = 0;
    let mut v___x_1552_: usize = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1533_) == 0 {
                    return v_x_1532_;
                } else {
                    v_key_1534_ = leanh::lean_ctor_get(v_x_1533_, 0);
                    v_value_1535_ = leanh::lean_ctor_get(v_x_1533_, 1);
                    v_tail_1536_ = leanh::lean_ctor_get(v_x_1533_, 2);
                    v_isSharedCheck_1559_ = (!leanh::lean_is_exclusive(v_x_1533_)) as u8;
                    if v_isSharedCheck_1559_ == 0 {
                        v___x_1538_ = v_x_1533_;
                        v_isShared_1539_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1536_);
                        leanh::lean_inc(v_value_1535_);
                        leanh::lean_inc(v_key_1534_);
                        leanh::lean_dec(v_x_1533_);
                        v___x_1538_ = leanh::lean_box(0);
                        v_isShared_1539_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1540_ = lean_array_get_size(v_x_1532_);
                v___x_1541_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_1534_);
                v___x_1542_ = 32u64;
                v___x_1543_ = lean_uint64_shift_right(v___x_1541_, v___x_1542_);
                v_fold_1544_ = lean_uint64_xor(v___x_1541_, v___x_1543_);
                v___x_1545_ = 16u64;
                v___x_1546_ = lean_uint64_shift_right(v_fold_1544_, v___x_1545_);
                v___x_1547_ = lean_uint64_xor(v_fold_1544_, v___x_1546_);
                v___x_1548_ = lean_uint64_to_usize(v___x_1547_);
                v___x_1549_ = lean_usize_of_nat(v___x_1540_);
                v___x_1550_ = 1usize;
                v___x_1551_ = lean_usize_sub(v___x_1549_, v___x_1550_);
                v___x_1552_ = lean_usize_land(v___x_1548_, v___x_1551_);
                v___x_1553_ = lean_array_uget_borrowed(v_x_1532_, v___x_1552_);
                leanh::lean_inc(v___x_1553_);
                if v_isShared_1539_ == 0 {
                    leanh::lean_ctor_set(v___x_1538_, 2, v___x_1553_);
                    v___x_1555_ = v___x_1538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_key_1534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_value_1535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 2, v___x_1553_);
                    v___x_1555_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1556_ = lean_array_uset(v_x_1532_, v___x_1552_, v___x_1555_);
                v_x_1532_ = v___x_1556_;
                v_x_1533_ = v_tail_1536_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(
    mut v_i_1560_: *mut leanh::LeanObject,
    mut v_source_1561_: *mut leanh::LeanObject,
    mut v_target_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v_es_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1563_ = lean_array_get_size(v_source_1561_);
                v___x_1564_ = lean_nat_dec_lt(v_i_1560_, v___x_1563_);
                if v___x_1564_ == 0 {
                    leanh::lean_dec_ref(v_source_1561_);
                    leanh::lean_dec(v_i_1560_);
                    return v_target_1562_;
                } else {
                    v_es_1565_ = lean_array_fget(v_source_1561_, v_i_1560_);
                    v___x_1566_ = leanh::lean_box(0);
                    v_source_1567_ = lean_array_fset(v_source_1561_, v_i_1560_, v___x_1566_);
                    v_target_1568_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_1562_, v_es_1565_);
                    v___x_1569_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1570_ = lean_nat_add(v_i_1560_, v___x_1569_);
                    leanh::lean_dec(v_i_1560_);
                    v_i_1560_ = v___x_1570_;
                    v_source_1561_ = v_source_1567_;
                    v_target_1562_ = v_target_1568_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(
    mut v_data_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = lean_array_get_size(v_data_1572_);
    v___x_1574_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1575_ = lean_nat_mul(v___x_1573_, v___x_1574_);
    v___x_1576_ = leanh::lean_unsigned_to_nat(0);
    v___x_1577_ = leanh::lean_box(0);
    v___x_1578_ = lean_mk_array(v_nbuckets_1575_, v___x_1577_);
    v___x_1579_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_1576_, v_data_1572_, v___x_1578_);
    return v___x_1579_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(
    mut v_a_1580_: *mut leanh::LeanObject,
    mut v_x_1581_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1582_: u8 = 0;
    let mut v_key_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1581_) == 0 {
                    v___x_1582_ = 0;
                    return v___x_1582_;
                } else {
                    v_key_1583_ = leanh::lean_ctor_get(v_x_1581_, 0);
                    v_tail_1584_ = leanh::lean_ctor_get(v_x_1581_, 2);
                    v___x_1585_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_1583_,
                            v_a_1580_,
                        );
                    if v___x_1585_ == 0 {
                        v_x_1581_ = v_tail_1584_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1585_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(
    mut v_a_1587_: *mut leanh::LeanObject,
    mut v_x_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1589_: u8 = 0;
    let mut v_r_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1589_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_1587_, v_x_1588_);
    leanh::lean_dec(v_x_1588_);
    leanh::lean_dec_ref(v_a_1587_);
    v_r_1590_ = leanh::lean_box((v_res_1589_) as usize);
    return v_r_1590_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(
    mut v_m_1591_: *mut leanh::LeanObject,
    mut v_a_1592_: *mut leanh::LeanObject,
    mut v_b_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1598_: u8 = 0;
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u64 = 0;
    let mut v___x_1601_: u64 = 0;
    let mut v___x_1602_: u64 = 0;
    let mut v_fold_1603_: u64 = 0;
    let mut v___x_1604_: u64 = 0;
    let mut v___x_1605_: u64 = 0;
    let mut v___x_1606_: u64 = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: usize = 0;
    let mut v___x_1610_: usize = 0;
    let mut v___x_1611_: usize = 0;
    let mut v_bkt_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v_val_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1594_ = leanh::lean_ctor_get(v_m_1591_, 0);
                v_buckets_1595_ = leanh::lean_ctor_get(v_m_1591_, 1);
                v_isSharedCheck_1638_ = (!leanh::lean_is_exclusive(v_m_1591_)) as u8;
                if v_isSharedCheck_1638_ == 0 {
                    v___x_1597_ = v_m_1591_;
                    v_isShared_1598_ = v_isSharedCheck_1638_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1595_);
                    leanh::lean_inc(v_size_1594_);
                    leanh::lean_dec(v_m_1591_);
                    v___x_1597_ = leanh::lean_box(0);
                    v_isShared_1598_ = v_isSharedCheck_1638_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1599_ = lean_array_get_size(v_buckets_1595_);
                v___x_1600_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1592_);
                v___x_1601_ = 32u64;
                v___x_1602_ = lean_uint64_shift_right(v___x_1600_, v___x_1601_);
                v_fold_1603_ = lean_uint64_xor(v___x_1600_, v___x_1602_);
                v___x_1604_ = 16u64;
                v___x_1605_ = lean_uint64_shift_right(v_fold_1603_, v___x_1604_);
                v___x_1606_ = lean_uint64_xor(v_fold_1603_, v___x_1605_);
                v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
                v___x_1608_ = lean_usize_of_nat(v___x_1599_);
                v___x_1609_ = 1usize;
                v___x_1610_ = lean_usize_sub(v___x_1608_, v___x_1609_);
                v___x_1611_ = lean_usize_land(v___x_1607_, v___x_1610_);
                v_bkt_1612_ = lean_array_uget_borrowed(v_buckets_1595_, v___x_1611_);
                v___x_1613_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_1592_, v_bkt_1612_);
                if v___x_1613_ == 0 {
                    v___x_1614_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1615_ = lean_nat_add(v_size_1594_, v___x_1614_);
                    leanh::lean_dec(v_size_1594_);
                    leanh::lean_inc(v_bkt_1612_);
                    v___x_1616_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1616_, 0, v_a_1592_);
                    leanh::lean_ctor_set(v___x_1616_, 1, v_b_1593_);
                    leanh::lean_ctor_set(v___x_1616_, 2, v_bkt_1612_);
                    v_buckets_x27_1617_ =
                        lean_array_uset(v_buckets_1595_, v___x_1611_, v___x_1616_);
                    v___x_1618_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1619_ = lean_nat_mul(v_size_x27_1615_, v___x_1618_);
                    v___x_1620_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1621_ = lean_nat_div(v___x_1619_, v___x_1620_);
                    leanh::lean_dec(v___x_1619_);
                    v___x_1622_ = lean_array_get_size(v_buckets_x27_1617_);
                    v___x_1623_ = lean_nat_dec_le(v___x_1621_, v___x_1622_);
                    leanh::lean_dec(v___x_1621_);
                    if v___x_1623_ == 0 {
                        v_val_1624_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_1617_);
                        if v_isShared_1598_ == 0 {
                            leanh::lean_ctor_set(v___x_1597_, 1, v_val_1624_);
                            leanh::lean_ctor_set(v___x_1597_, 0, v_size_x27_1615_);
                            v___x_1626_ = v___x_1597_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1627_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1627_,
                                0,
                                v_size_x27_1615_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_val_1624_);
                            v___x_1626_ = v_reuseFailAlloc_1627_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1598_ == 0 {
                            leanh::lean_ctor_set(v___x_1597_, 1, v_buckets_x27_1617_);
                            leanh::lean_ctor_set(v___x_1597_, 0, v_size_x27_1615_);
                            v___x_1629_ = v___x_1597_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1630_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1630_,
                                0,
                                v_size_x27_1615_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1630_,
                                1,
                                v_buckets_x27_1617_,
                            );
                            v___x_1629_ = v_reuseFailAlloc_1630_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1612_);
                    v___x_1631_ = leanh::lean_box(0);
                    v_buckets_x27_1632_ =
                        lean_array_uset(v_buckets_1595_, v___x_1611_, v___x_1631_);
                    v___x_1633_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_1592_, v_b_1593_, v_bkt_1612_);
                    v___x_1634_ = lean_array_uset(v_buckets_x27_1632_, v___x_1611_, v___x_1633_);
                    if v_isShared_1598_ == 0 {
                        leanh::lean_ctor_set(v___x_1597_, 1, v___x_1634_);
                        v___x_1636_ = v___x_1597_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1637_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_size_1594_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1634_);
                        v___x_1636_ = v_reuseFailAlloc_1637_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1626_;
            }
            3 => {
                return v___x_1629_;
            }
            4 => {
                return v___x_1636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
    mut v_e_1639_: *mut leanh::LeanObject,
    mut v_r_1640_: *mut leanh::LeanObject,
    mut v_a_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u64 = 0;
    let mut v___x_1649_: usize = 0;
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1642_ = leanh::lean_ctor_get(v_a_1641_, 0);
                v_set_1643_ = leanh::lean_ctor_get(v_a_1641_, 1);
                v_isSharedCheck_1665_ = (!leanh::lean_is_exclusive(v_a_1641_)) as u8;
                if v_isSharedCheck_1665_ == 0 {
                    v___x_1645_ = v_a_1641_;
                    v_isShared_1646_ = v_isSharedCheck_1665_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_set_1643_);
                    leanh::lean_inc(v_map_1642_);
                    leanh::lean_dec(v_a_1641_);
                    v___x_1645_ = leanh::lean_box(0);
                    v_isShared_1646_ = v_isSharedCheck_1665_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1647_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                v___x_1648_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                    v_r_1640_,
                );
                v___x_1649_ = lean_uint64_to_usize(v___x_1648_);
                leanh::lean_inc_ref(v_r_1640_);
                leanh::lean_inc_ref(v_set_1643_);
                v___x_1650_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1643_, v___x_1649_, v_r_1640_, v___x_1647_);
                v___x_1651_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_1650_,
                        v___x_1647_,
                    );
                if v___x_1651_ == 0 {
                    leanh::lean_dec_ref(v_r_1640_);
                    leanh::lean_inc_ref(v___x_1650_);
                    v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_1642_, v_e_1639_, v___x_1650_);
                    if v_isShared_1646_ == 0 {
                        leanh::lean_ctor_set(v___x_1645_, 0, v___x_1652_);
                        v___x_1654_ = v___x_1645_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1652_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_set_1643_);
                        v___x_1654_ = v_reuseFailAlloc_1656_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1650_);
                    leanh::lean_inc_ref_n(v_r_1640_, 4);
                    v___x_1657_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_1642_, v_e_1639_, v_r_1640_);
                    v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_1657_, v_r_1640_, v_r_1640_);
                    v___x_1659_ = leanh::lean_box(0);
                    v___x_1660_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1643_, v_r_1640_, v___x_1659_);
                    if v_isShared_1646_ == 0 {
                        leanh::lean_ctor_set(v___x_1645_, 1, v___x_1660_);
                        leanh::lean_ctor_set(v___x_1645_, 0, v___x_1658_);
                        v___x_1662_ = v___x_1645_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1664_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1658_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1660_);
                        v___x_1662_ = v_reuseFailAlloc_1664_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1655_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1655_, 0, v___x_1650_);
                leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
                return v___x_1655_;
            }
            3 => {
                v___x_1663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1663_, 0, v_r_1640_);
                leanh::lean_ctor_set(v___x_1663_, 1, v___x_1662_);
                return v___x_1663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(
    mut v_00_u03b2_1666_: *mut leanh::LeanObject,
    mut v_x_1667_: *mut leanh::LeanObject,
    mut v_x_1668_: usize,
    mut v_x_1669_: *mut leanh::LeanObject,
    mut v_x_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_1667_, v_x_1668_, v_x_1669_, v_x_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(
    mut v_00_u03b2_1672_: *mut leanh::LeanObject,
    mut v_x_1673_: *mut leanh::LeanObject,
    mut v_x_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
    mut v_x_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2466__boxed_1677_: usize = 0;
    let mut v_res_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2466__boxed_1677_ = leanh::lean_unbox_usize(v_x_1674_);
    leanh::lean_dec(v_x_1674_);
    v_res_1678_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_1672_, v_x_1673_, v_x_2466__boxed_1677_, v_x_1675_, v_x_1676_);
    leanh::lean_dec_ref(v_x_1676_);
    return v_res_1678_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(
    mut v_00_u03b2_1679_: *mut leanh::LeanObject,
    mut v_m_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
    mut v_b_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_1680_, v_a_1681_, v_b_1682_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(
    mut v_00_u03b2_1684_: *mut leanh::LeanObject,
    mut v_x_1685_: *mut leanh::LeanObject,
    mut v_x_1686_: *mut leanh::LeanObject,
    mut v_x_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_1685_, v_x_1686_, v_x_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(
    mut v_00_u03b2_1689_: *mut leanh::LeanObject,
    mut v_keys_1690_: *mut leanh::LeanObject,
    mut v_vals_1691_: *mut leanh::LeanObject,
    mut v_heq_1692_: *mut leanh::LeanObject,
    mut v_i_1693_: *mut leanh::LeanObject,
    mut v_k_1694_: *mut leanh::LeanObject,
    mut v_k_u2080_1695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_1690_, v_i_1693_, v_k_1694_, v_k_u2080_1695_);
    return v___x_1696_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(
    mut v_00_u03b2_1697_: *mut leanh::LeanObject,
    mut v_keys_1698_: *mut leanh::LeanObject,
    mut v_vals_1699_: *mut leanh::LeanObject,
    mut v_heq_1700_: *mut leanh::LeanObject,
    mut v_i_1701_: *mut leanh::LeanObject,
    mut v_k_1702_: *mut leanh::LeanObject,
    mut v_k_u2080_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1697_, v_keys_1698_, v_vals_1699_, v_heq_1700_, v_i_1701_, v_k_1702_, v_k_u2080_1703_);
    leanh::lean_dec_ref(v_k_u2080_1703_);
    leanh::lean_dec_ref(v_vals_1699_);
    leanh::lean_dec_ref(v_keys_1698_);
    return v_res_1704_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(
    mut v_00_u03b2_1705_: *mut leanh::LeanObject,
    mut v_a_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1708_: u8 = 0;
    v___x_1708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_1706_, v_x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(
    mut v_00_u03b2_1709_: *mut leanh::LeanObject,
    mut v_a_1710_: *mut leanh::LeanObject,
    mut v_x_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1712_: u8 = 0;
    let mut v_r_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_1709_, v_a_1710_, v_x_1711_);
    leanh::lean_dec(v_x_1711_);
    leanh::lean_dec_ref(v_a_1710_);
    v_r_1713_ = leanh::lean_box((v_res_1712_) as usize);
    return v_r_1713_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(
    mut v_00_u03b2_1714_: *mut leanh::LeanObject,
    mut v_data_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(
    mut v_00_u03b2_1717_: *mut leanh::LeanObject,
    mut v_a_1718_: *mut leanh::LeanObject,
    mut v_b_1719_: *mut leanh::LeanObject,
    mut v_x_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_1718_, v_b_1719_, v_x_1720_);
    return v___x_1721_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(
    mut v_00_u03b2_1722_: *mut leanh::LeanObject,
    mut v_x_1723_: *mut leanh::LeanObject,
    mut v_x_1724_: usize,
    mut v_x_1725_: usize,
    mut v_x_1726_: *mut leanh::LeanObject,
    mut v_x_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_1723_, v_x_1724_, v_x_1725_, v_x_1726_, v_x_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(
    mut v_00_u03b2_1729_: *mut leanh::LeanObject,
    mut v_x_1730_: *mut leanh::LeanObject,
    mut v_x_1731_: *mut leanh::LeanObject,
    mut v_x_1732_: *mut leanh::LeanObject,
    mut v_x_1733_: *mut leanh::LeanObject,
    mut v_x_1734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2503__boxed_1735_: usize = 0;
    let mut v_x_2504__boxed_1736_: usize = 0;
    let mut v_res_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2503__boxed_1735_ = leanh::lean_unbox_usize(v_x_1731_);
    leanh::lean_dec(v_x_1731_);
    v_x_2504__boxed_1736_ = leanh::lean_unbox_usize(v_x_1732_);
    leanh::lean_dec(v_x_1732_);
    v_res_1737_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_1729_, v_x_1730_, v_x_2503__boxed_1735_, v_x_2504__boxed_1736_, v_x_1733_, v_x_1734_);
    return v_res_1737_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1738_: *mut leanh::LeanObject,
    mut v_i_1739_: *mut leanh::LeanObject,
    mut v_source_1740_: *mut leanh::LeanObject,
    mut v_target_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_1739_, v_source_1740_, v_target_1741_);
    return v___x_1742_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(
    mut v_00_u03b2_1743_: *mut leanh::LeanObject,
    mut v_n_1744_: *mut leanh::LeanObject,
    mut v_k_1745_: *mut leanh::LeanObject,
    mut v_v_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_1744_, v_k_1745_, v_v_1746_);
    return v___x_1747_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(
    mut v_00_u03b2_1748_: *mut leanh::LeanObject,
    mut v_depth_1749_: usize,
    mut v_keys_1750_: *mut leanh::LeanObject,
    mut v_vals_1751_: *mut leanh::LeanObject,
    mut v_heq_1752_: *mut leanh::LeanObject,
    mut v_i_1753_: *mut leanh::LeanObject,
    mut v_entries_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_1749_, v_keys_1750_, v_vals_1751_, v_i_1753_, v_entries_1754_);
    return v___x_1755_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(
    mut v_00_u03b2_1756_: *mut leanh::LeanObject,
    mut v_depth_1757_: *mut leanh::LeanObject,
    mut v_keys_1758_: *mut leanh::LeanObject,
    mut v_vals_1759_: *mut leanh::LeanObject,
    mut v_heq_1760_: *mut leanh::LeanObject,
    mut v_i_1761_: *mut leanh::LeanObject,
    mut v_entries_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1763_: usize = 0;
    let mut v_res_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1763_ = leanh::lean_unbox_usize(v_depth_1757_);
    leanh::lean_dec(v_depth_1757_);
    v_res_1764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_1756_, v_depth_boxed_1763_, v_keys_1758_, v_vals_1759_, v_heq_1760_, v_i_1761_, v_entries_1762_);
    leanh::lean_dec_ref(v_vals_1759_);
    leanh::lean_dec_ref(v_keys_1758_);
    return v_res_1764_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1765_: *mut leanh::LeanObject,
    mut v_x_1766_: *mut leanh::LeanObject,
    mut v_x_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_1766_, v_x_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(
    mut v_00_u03b2_1769_: *mut leanh::LeanObject,
    mut v_x_1770_: *mut leanh::LeanObject,
    mut v_x_1771_: *mut leanh::LeanObject,
    mut v_x_1772_: *mut leanh::LeanObject,
    mut v_x_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_1770_, v_x_1771_, v_x_1772_, v_x_1773_);
    return v___x_1774_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(
    mut v_e_1777_: *mut leanh::LeanObject,
    mut v_k_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1780_ = leanh::lean_ctor_get(v_a_1779_, 0);
    v_set_1781_ = leanh::lean_ctor_get(v_a_1779_, 1);
    v___f_1782_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0;
    v___f_1783_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1;
    leanh::lean_inc_ref(v_e_1777_);
    v___x_1784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_1782_,
        v___f_1783_,
        v_map_1780_,
        v_e_1777_,
    );
    if leanh::lean_obj_tag(v___x_1784_) == 1 {
        let mut v_val_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_1778_);
        leanh::lean_dec_ref(v_e_1777_);
        v_val_1785_ = leanh::lean_ctor_get(v___x_1784_, 0);
        leanh::lean_inc(v_val_1785_);
        leanh::lean_dec_ref_known(v___x_1784_, 1);
        v___x_1786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1786_, 0, v_val_1785_);
        leanh::lean_ctor_set(v___x_1786_, 1, v_a_1779_);
        return v___x_1786_;
    } else {
        let mut v___f_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: u64 = 0;
        let mut v___x_1790_: usize = 0;
        let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: u8 = 0;
        leanh::lean_dec(v___x_1784_);
        v___f_1787_ = l_Lean_Meta_Sym_instBEqAlphaKey___closed__0;
        v___x_1788_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
        v___x_1789_ =
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1777_);
        v___x_1790_ = lean_uint64_to_usize(v___x_1789_);
        leanh::lean_inc_ref(v_e_1777_);
        leanh::lean_inc_ref(v_set_1781_);
        v___x_1791_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
            v___f_1787_,
            v_set_1781_,
            v___x_1790_,
            v_e_1777_,
            v___x_1788_,
        );
        v___x_1792_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v___x_1791_,
            v___x_1788_,
        );
        if v___x_1792_ == 0 {
            let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_k_1778_);
            leanh::lean_dec_ref(v_e_1777_);
            v___x_1793_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1793_, 0, v___x_1791_);
            leanh::lean_ctor_set(v___x_1793_, 1, v_a_1779_);
            return v___x_1793_;
        } else {
            let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1791_);
            v___x_1794_ = leanh::lean_apply_1(v_k_1778_, v_a_1779_);
            v_fst_1795_ = leanh::lean_ctor_get(v___x_1794_, 0);
            leanh::lean_inc(v_fst_1795_);
            v_snd_1796_ = leanh::lean_ctor_get(v___x_1794_, 1);
            leanh::lean_inc(v_snd_1796_);
            leanh::lean_dec_ref(v___x_1794_);
            v___x_1797_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                v_e_1777_,
                v_fst_1795_,
                v_snd_1796_,
            );
            return v___x_1797_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(
    mut v_keys_1798_: *mut leanh::LeanObject,
    mut v_vals_1799_: *mut leanh::LeanObject,
    mut v_i_1800_: *mut leanh::LeanObject,
    mut v_k_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1802_ = lean_array_get_size(v_keys_1798_);
                v___x_1803_ = lean_nat_dec_lt(v_i_1800_, v___x_1802_);
                if v___x_1803_ == 0 {
                    leanh::lean_dec_ref(v_k_1801_);
                    leanh::lean_dec(v_i_1800_);
                    v___x_1804_ = leanh::lean_box(0);
                    return v___x_1804_;
                } else {
                    v_k_x27_1805_ = lean_array_fget_borrowed(v_keys_1798_, v_i_1800_);
                    leanh::lean_inc(v_k_x27_1805_);
                    leanh::lean_inc_ref(v_k_1801_);
                    v___x_1806_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_1801_,
                            v_k_x27_1805_,
                        );
                    if v___x_1806_ == 0 {
                        v___x_1807_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1808_ = lean_nat_add(v_i_1800_, v___x_1807_);
                        leanh::lean_dec(v_i_1800_);
                        v_i_1800_ = v___x_1808_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_1801_);
                        v___x_1810_ = lean_array_fget_borrowed(v_vals_1799_, v_i_1800_);
                        leanh::lean_dec(v_i_1800_);
                        leanh::lean_inc(v___x_1810_);
                        leanh::lean_inc(v_k_x27_1805_);
                        v___x_1811_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1811_, 0, v_k_x27_1805_);
                        leanh::lean_ctor_set(v___x_1811_, 1, v___x_1810_);
                        v___x_1812_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
                        return v___x_1812_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_1813_: *mut leanh::LeanObject,
    mut v_vals_1814_: *mut leanh::LeanObject,
    mut v_i_1815_: *mut leanh::LeanObject,
    mut v_k_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_1813_, v_vals_1814_, v_i_1815_, v_k_1816_);
    leanh::lean_dec_ref(v_vals_1814_);
    leanh::lean_dec_ref(v_keys_1813_);
    return v_res_1817_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(
    mut v_x_1818_: *mut leanh::LeanObject,
    mut v_x_1819_: usize,
    mut v_x_1820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: usize = 0;
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: usize = 0;
    let mut v_j_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: usize = 0;
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1818_) == 0 {
                    v_es_1821_ = leanh::lean_ctor_get(v_x_1818_, 0);
                    leanh::lean_inc_ref(v_es_1821_);
                    leanh::lean_dec_ref_known(v_x_1818_, 1);
                    v___x_1822_ = leanh::lean_box(2);
                    v___x_1823_ = 5usize;
                    v___x_1824_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
                    v___x_1825_ = lean_usize_land(v_x_1819_, v___x_1824_);
                    v_j_1826_ = lean_usize_to_nat(v___x_1825_);
                    v___x_1827_ = lean_array_get(v___x_1822_, v_es_1821_, v_j_1826_);
                    leanh::lean_dec(v_j_1826_);
                    leanh::lean_dec_ref(v_es_1821_);
                    match leanh::lean_obj_tag(v___x_1827_) {
                        0 => {
                            v_key_1828_ = leanh::lean_ctor_get(v___x_1827_, 0);
                            leanh::lean_inc_n(v_key_1828_, 2);
                            v_val_1829_ = leanh::lean_ctor_get(v___x_1827_, 1);
                            leanh::lean_inc(v_val_1829_);
                            leanh::lean_dec_ref_known(v___x_1827_, 2);
                            v___x_1830_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_1820_,
                                    v_key_1828_,
                                );
                            if v___x_1830_ == 0 {
                                leanh::lean_dec(v_val_1829_);
                                leanh::lean_dec(v_key_1828_);
                                v___x_1831_ = leanh::lean_box(0);
                                return v___x_1831_;
                            } else {
                                v___x_1832_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1832_, 0, v_key_1828_);
                                leanh::lean_ctor_set(v___x_1832_, 1, v_val_1829_);
                                v___x_1833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1833_, 0, v___x_1832_);
                                return v___x_1833_;
                            }
                        }
                        1 => {
                            v_node_1834_ = leanh::lean_ctor_get(v___x_1827_, 0);
                            leanh::lean_inc(v_node_1834_);
                            leanh::lean_dec_ref_known(v___x_1827_, 1);
                            v___x_1835_ = lean_usize_shift_right(v_x_1819_, v___x_1823_);
                            v_x_1818_ = v_node_1834_;
                            v_x_1819_ = v___x_1835_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_x_1820_);
                            v___x_1837_ = leanh::lean_box(0);
                            return v___x_1837_;
                        }
                    }
                } else {
                    v_ks_1838_ = leanh::lean_ctor_get(v_x_1818_, 0);
                    leanh::lean_inc_ref(v_ks_1838_);
                    v_vs_1839_ = leanh::lean_ctor_get(v_x_1818_, 1);
                    leanh::lean_inc_ref(v_vs_1839_);
                    leanh::lean_dec_ref_known(v_x_1818_, 2);
                    v___x_1840_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1841_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_ks_1838_, v_vs_1839_, v___x_1840_, v_x_1820_);
                    leanh::lean_dec_ref(v_vs_1839_);
                    leanh::lean_dec_ref(v_ks_1838_);
                    return v___x_1841_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(
    mut v_x_1842_: *mut leanh::LeanObject,
    mut v_x_1843_: *mut leanh::LeanObject,
    mut v_x_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_8780__boxed_1845_: usize = 0;
    let mut v_res_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_8780__boxed_1845_ = leanh::lean_unbox_usize(v_x_1843_);
    leanh::lean_dec(v_x_1843_);
    v_res_1846_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_1842_, v_x_8780__boxed_1845_, v_x_1844_);
    return v_res_1846_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(
    mut v_x_1847_: *mut leanh::LeanObject,
    mut v_x_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1849_: u64 = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1848_);
    v___x_1850_ = lean_uint64_to_usize(v___x_1849_);
    leanh::lean_inc_ref(v_x_1847_);
    v___x_1851_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_1847_, v___x_1850_, v_x_1848_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(
    mut v_x_1852_: *mut leanh::LeanObject,
    mut v_x_1853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1854_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_x_1852_, v_x_1853_);
    leanh::lean_dec_ref(v_x_1852_);
    return v_res_1854_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(
    mut v_a_1855_: *mut leanh::LeanObject,
    mut v_x_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1856_) == 0 {
                    v___x_1857_ = leanh::lean_box(0);
                    return v___x_1857_;
                } else {
                    v_key_1858_ = leanh::lean_ctor_get(v_x_1856_, 0);
                    v_value_1859_ = leanh::lean_ctor_get(v_x_1856_, 1);
                    v_tail_1860_ = leanh::lean_ctor_get(v_x_1856_, 2);
                    v___x_1861_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_1858_,
                            v_a_1855_,
                        );
                    if v___x_1861_ == 0 {
                        v_x_1856_ = v_tail_1860_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1859_);
                        v___x_1863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1863_, 0, v_value_1859_);
                        return v___x_1863_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(
    mut v_a_1864_: *mut leanh::LeanObject,
    mut v_x_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_1864_, v_x_1865_);
    leanh::lean_dec(v_x_1865_);
    leanh::lean_dec_ref(v_a_1864_);
    return v_res_1866_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(
    mut v_m_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: u64 = 0;
    let mut v___x_1873_: u64 = 0;
    let mut v_fold_1874_: u64 = 0;
    let mut v___x_1875_: u64 = 0;
    let mut v___x_1876_: u64 = 0;
    let mut v___x_1877_: u64 = 0;
    let mut v___x_1878_: usize = 0;
    let mut v___x_1879_: usize = 0;
    let mut v___x_1880_: usize = 0;
    let mut v___x_1881_: usize = 0;
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1869_ = leanh::lean_ctor_get(v_m_1867_, 1);
    v___x_1870_ = lean_array_get_size(v_buckets_1869_);
    v___x_1871_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1868_);
    v___x_1872_ = 32u64;
    v___x_1873_ = lean_uint64_shift_right(v___x_1871_, v___x_1872_);
    v_fold_1874_ = lean_uint64_xor(v___x_1871_, v___x_1873_);
    v___x_1875_ = 16u64;
    v___x_1876_ = lean_uint64_shift_right(v_fold_1874_, v___x_1875_);
    v___x_1877_ = lean_uint64_xor(v_fold_1874_, v___x_1876_);
    v___x_1878_ = lean_uint64_to_usize(v___x_1877_);
    v___x_1879_ = lean_usize_of_nat(v___x_1870_);
    v___x_1880_ = 1usize;
    v___x_1881_ = lean_usize_sub(v___x_1879_, v___x_1880_);
    v___x_1882_ = lean_usize_land(v___x_1878_, v___x_1881_);
    v___x_1883_ = lean_array_uget_borrowed(v_buckets_1869_, v___x_1882_);
    v___x_1884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_1868_, v___x_1883_);
    return v___x_1884_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(
    mut v_m_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_1885_, v_a_1886_);
    leanh::lean_dec_ref(v_a_1886_);
    leanh::lean_dec_ref(v_m_1885_);
    return v_res_1887_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
    mut v_e_1888_: *mut leanh::LeanObject,
    mut v_a_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u64 = 0;
    let mut v___x_1899_: usize = 0;
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: u8 = 0;
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: usize = 0;
    let mut v___x_1915_: usize = 0;
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: usize = 0;
    let mut v___x_1918_: usize = 0;
    let mut v___x_1919_: u8 = 0;
    let mut v_binderName_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1923_: u8 = 0;
    let mut v_map_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u64 = 0;
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: u8 = 0;
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: u8 = 0;
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: usize = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: usize = 0;
    let mut v___x_1953_: usize = 0;
    let mut v___x_1954_: u8 = 0;
    let mut v_binderName_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1958_: u8 = 0;
    let mut v_map_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u64 = 0;
    let mut v___x_1966_: usize = 0;
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: u8 = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: usize = 0;
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: usize = 0;
    let mut v___x_1988_: usize = 0;
    let mut v___x_1989_: u8 = 0;
    let mut v_declName_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1994_: u8 = 0;
    let mut v_map_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u64 = 0;
    let mut v___x_2002_: usize = 0;
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2016_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: usize = 0;
    let mut v___x_2020_: usize = 0;
    let mut v___x_2021_: u8 = 0;
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: usize = 0;
    let mut v___x_2026_: usize = 0;
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: usize = 0;
    let mut v___x_2029_: usize = 0;
    let mut v___x_2030_: u8 = 0;
    let mut v_data_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u64 = 0;
    let mut v___x_2040_: usize = 0;
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u64 = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: usize = 0;
    let mut v___x_2071_: usize = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_unused_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut v_unused_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_e_1888_) {
                    5 => {
                        v_fn_1890_ = leanh::lean_ctor_get(v_e_1888_, 0);
                        v_arg_1891_ = leanh::lean_ctor_get(v_e_1888_, 1);
                        v_map_1892_ = leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1893_ = leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1892_, v_e_1888_);
                        if leanh::lean_obj_tag(v___x_1894_) == 1 {
                            leanh::lean_dec_ref_known(v_e_1888_, 2);
                            v_val_1895_ = leanh::lean_ctor_get(v___x_1894_, 0);
                            leanh::lean_inc(v_val_1895_);
                            leanh::lean_dec_ref_known(v___x_1894_, 1);
                            v___x_1896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1896_, 0, v_val_1895_);
                            leanh::lean_ctor_set(v___x_1896_, 1, v_a_1889_);
                            return v___x_1896_;
                        } else {
                            leanh::lean_dec(v___x_1894_);
                            v___x_1897_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_1898_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_1899_ = lean_uint64_to_usize(v___x_1898_);
                            leanh::lean_inc_ref(v_e_1888_);
                            leanh::lean_inc_ref(v_set_1893_);
                            v___x_1900_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1893_, v___x_1899_, v_e_1888_, v___x_1897_);
                            v___x_1901_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1900_, v___x_1897_);
                            if v___x_1901_ == 0 {
                                leanh::lean_dec_ref_known(v_e_1888_, 2);
                                v___x_1902_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1902_, 0, v___x_1900_);
                                leanh::lean_ctor_set(v___x_1902_, 1, v_a_1889_);
                                return v___x_1902_;
                            } else {
                                leanh::lean_dec_ref(v___x_1900_);
                                leanh::lean_inc_ref(v_fn_1890_);
                                v___x_1903_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_fn_1890_, v_a_1889_,
                                    );
                                v_fst_1904_ = leanh::lean_ctor_get(v___x_1903_, 0);
                                leanh::lean_inc(v_fst_1904_);
                                v_snd_1905_ = leanh::lean_ctor_get(v___x_1903_, 1);
                                leanh::lean_inc(v_snd_1905_);
                                leanh::lean_dec_ref(v___x_1903_);
                                leanh::lean_inc_ref(v_arg_1891_);
                                v___x_1906_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_arg_1891_,
                                        v_snd_1905_,
                                    );
                                v_fst_1907_ = leanh::lean_ctor_get(v___x_1906_, 0);
                                leanh::lean_inc(v_fst_1907_);
                                v_snd_1908_ = leanh::lean_ctor_get(v___x_1906_, 1);
                                leanh::lean_inc(v_snd_1908_);
                                leanh::lean_dec_ref(v___x_1906_);
                                v___x_1914_ = lean_ptr_addr(v_fn_1890_);
                                v___x_1915_ = lean_ptr_addr(v_fst_1904_);
                                v___x_1916_ = lean_usize_dec_eq(v___x_1914_, v___x_1915_);
                                if v___x_1916_ == 0 {
                                    v___y_1910_ = v___x_1916_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1917_ = lean_ptr_addr(v_arg_1891_);
                                    v___x_1918_ = lean_ptr_addr(v_fst_1907_);
                                    v___x_1919_ = lean_usize_dec_eq(v___x_1917_, v___x_1918_);
                                    v___y_1910_ = v___x_1919_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                    6 => {
                        v_binderName_1920_ = leanh::lean_ctor_get(v_e_1888_, 0);
                        v_binderType_1921_ = leanh::lean_ctor_get(v_e_1888_, 1);
                        v_body_1922_ = leanh::lean_ctor_get(v_e_1888_, 2);
                        v_binderInfo_1923_ = leanh::lean_ctor_get_uint8(
                            v_e_1888_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v_map_1924_ = leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1925_ = leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1924_, v_e_1888_);
                        if leanh::lean_obj_tag(v___x_1926_) == 1 {
                            leanh::lean_dec_ref_known(v_e_1888_, 3);
                            v_val_1927_ = leanh::lean_ctor_get(v___x_1926_, 0);
                            leanh::lean_inc(v_val_1927_);
                            leanh::lean_dec_ref_known(v___x_1926_, 1);
                            v___x_1928_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1928_, 0, v_val_1927_);
                            leanh::lean_ctor_set(v___x_1928_, 1, v_a_1889_);
                            return v___x_1928_;
                        } else {
                            leanh::lean_dec(v___x_1926_);
                            v___x_1929_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_1930_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_1931_ = lean_uint64_to_usize(v___x_1930_);
                            leanh::lean_inc_ref(v_e_1888_);
                            leanh::lean_inc_ref(v_set_1925_);
                            v___x_1932_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1925_, v___x_1931_, v_e_1888_, v___x_1929_);
                            v___x_1933_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1932_, v___x_1929_);
                            if v___x_1933_ == 0 {
                                leanh::lean_dec_ref_known(v_e_1888_, 3);
                                v___x_1934_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1934_, 0, v___x_1932_);
                                leanh::lean_ctor_set(v___x_1934_, 1, v_a_1889_);
                                return v___x_1934_;
                            } else {
                                leanh::lean_dec_ref(v___x_1932_);
                                leanh::lean_inc_ref(v_binderType_1921_);
                                v___x_1935_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_binderType_1921_,
                                        v_a_1889_,
                                    );
                                v_fst_1936_ = leanh::lean_ctor_get(v___x_1935_, 0);
                                leanh::lean_inc(v_fst_1936_);
                                v_snd_1937_ = leanh::lean_ctor_get(v___x_1935_, 1);
                                leanh::lean_inc(v_snd_1937_);
                                leanh::lean_dec_ref(v___x_1935_);
                                leanh::lean_inc_ref(v_body_1922_);
                                v___x_1938_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_body_1922_,
                                        v_snd_1937_,
                                    );
                                v_fst_1939_ = leanh::lean_ctor_get(v___x_1938_, 0);
                                leanh::lean_inc(v_fst_1939_);
                                v_snd_1940_ = leanh::lean_ctor_get(v___x_1938_, 1);
                                leanh::lean_inc(v_snd_1940_);
                                leanh::lean_dec_ref(v___x_1938_);
                                v___x_1949_ = lean_ptr_addr(v_binderType_1921_);
                                v___x_1950_ = lean_ptr_addr(v_fst_1936_);
                                v___x_1951_ = lean_usize_dec_eq(v___x_1949_, v___x_1950_);
                                if v___x_1951_ == 0 {
                                    v___y_1942_ = v___x_1951_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1952_ = lean_ptr_addr(v_body_1922_);
                                    v___x_1953_ = lean_ptr_addr(v_fst_1939_);
                                    v___x_1954_ = lean_usize_dec_eq(v___x_1952_, v___x_1953_);
                                    v___y_1942_ = v___x_1954_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                    7 => {
                        v_binderName_1955_ = leanh::lean_ctor_get(v_e_1888_, 0);
                        v_binderType_1956_ = leanh::lean_ctor_get(v_e_1888_, 1);
                        v_body_1957_ = leanh::lean_ctor_get(v_e_1888_, 2);
                        v_binderInfo_1958_ = leanh::lean_ctor_get_uint8(
                            v_e_1888_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v_map_1959_ = leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1960_ = leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1959_, v_e_1888_);
                        if leanh::lean_obj_tag(v___x_1961_) == 1 {
                            leanh::lean_dec_ref_known(v_e_1888_, 3);
                            v_val_1962_ = leanh::lean_ctor_get(v___x_1961_, 0);
                            leanh::lean_inc(v_val_1962_);
                            leanh::lean_dec_ref_known(v___x_1961_, 1);
                            v___x_1963_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1963_, 0, v_val_1962_);
                            leanh::lean_ctor_set(v___x_1963_, 1, v_a_1889_);
                            return v___x_1963_;
                        } else {
                            leanh::lean_dec(v___x_1961_);
                            v___x_1964_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_1965_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_1966_ = lean_uint64_to_usize(v___x_1965_);
                            leanh::lean_inc_ref(v_e_1888_);
                            leanh::lean_inc_ref(v_set_1960_);
                            v___x_1967_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1960_, v___x_1966_, v_e_1888_, v___x_1964_);
                            v___x_1968_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1967_, v___x_1964_);
                            if v___x_1968_ == 0 {
                                leanh::lean_dec_ref_known(v_e_1888_, 3);
                                v___x_1969_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1969_, 0, v___x_1967_);
                                leanh::lean_ctor_set(v___x_1969_, 1, v_a_1889_);
                                return v___x_1969_;
                            } else {
                                leanh::lean_dec_ref(v___x_1967_);
                                leanh::lean_inc_ref(v_binderType_1956_);
                                v___x_1970_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_binderType_1956_,
                                        v_a_1889_,
                                    );
                                v_fst_1971_ = leanh::lean_ctor_get(v___x_1970_, 0);
                                leanh::lean_inc(v_fst_1971_);
                                v_snd_1972_ = leanh::lean_ctor_get(v___x_1970_, 1);
                                leanh::lean_inc(v_snd_1972_);
                                leanh::lean_dec_ref(v___x_1970_);
                                leanh::lean_inc_ref(v_body_1957_);
                                v___x_1973_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_body_1957_,
                                        v_snd_1972_,
                                    );
                                v_fst_1974_ = leanh::lean_ctor_get(v___x_1973_, 0);
                                leanh::lean_inc(v_fst_1974_);
                                v_snd_1975_ = leanh::lean_ctor_get(v___x_1973_, 1);
                                leanh::lean_inc(v_snd_1975_);
                                leanh::lean_dec_ref(v___x_1973_);
                                v___x_1984_ = lean_ptr_addr(v_binderType_1956_);
                                v___x_1985_ = lean_ptr_addr(v_fst_1971_);
                                v___x_1986_ = lean_usize_dec_eq(v___x_1984_, v___x_1985_);
                                if v___x_1986_ == 0 {
                                    v___y_1977_ = v___x_1986_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_1987_ = lean_ptr_addr(v_body_1957_);
                                    v___x_1988_ = lean_ptr_addr(v_fst_1974_);
                                    v___x_1989_ = lean_usize_dec_eq(v___x_1987_, v___x_1988_);
                                    v___y_1977_ = v___x_1989_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                    8 => {
                        v_declName_1990_ = leanh::lean_ctor_get(v_e_1888_, 0);
                        v_type_1991_ = leanh::lean_ctor_get(v_e_1888_, 1);
                        v_value_1992_ = leanh::lean_ctor_get(v_e_1888_, 2);
                        v_body_1993_ = leanh::lean_ctor_get(v_e_1888_, 3);
                        v_nondep_1994_ = leanh::lean_ctor_get_uint8(
                            v_e_1888_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        v_map_1995_ = leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1996_ = leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1997_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1995_, v_e_1888_);
                        if leanh::lean_obj_tag(v___x_1997_) == 1 {
                            leanh::lean_dec_ref_known(v_e_1888_, 4);
                            v_val_1998_ = leanh::lean_ctor_get(v___x_1997_, 0);
                            leanh::lean_inc(v_val_1998_);
                            leanh::lean_dec_ref_known(v___x_1997_, 1);
                            v___x_1999_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1999_, 0, v_val_1998_);
                            leanh::lean_ctor_set(v___x_1999_, 1, v_a_1889_);
                            return v___x_1999_;
                        } else {
                            leanh::lean_dec(v___x_1997_);
                            v___x_2000_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_2001_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_2002_ = lean_uint64_to_usize(v___x_2001_);
                            leanh::lean_inc_ref(v_e_1888_);
                            leanh::lean_inc_ref(v_set_1996_);
                            v___x_2003_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1996_, v___x_2002_, v_e_1888_, v___x_2000_);
                            v___x_2004_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2003_, v___x_2000_);
                            if v___x_2004_ == 0 {
                                leanh::lean_dec_ref_known(v_e_1888_, 4);
                                v___x_2005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2005_, 0, v___x_2003_);
                                leanh::lean_ctor_set(v___x_2005_, 1, v_a_1889_);
                                return v___x_2005_;
                            } else {
                                leanh::lean_dec_ref(v___x_2003_);
                                leanh::lean_inc_ref(v_type_1991_);
                                v___x_2006_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_type_1991_,
                                        v_a_1889_,
                                    );
                                v_fst_2007_ = leanh::lean_ctor_get(v___x_2006_, 0);
                                leanh::lean_inc(v_fst_2007_);
                                v_snd_2008_ = leanh::lean_ctor_get(v___x_2006_, 1);
                                leanh::lean_inc(v_snd_2008_);
                                leanh::lean_dec_ref(v___x_2006_);
                                leanh::lean_inc_ref(v_value_1992_);
                                v___x_2009_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_value_1992_,
                                        v_snd_2008_,
                                    );
                                v_fst_2010_ = leanh::lean_ctor_get(v___x_2009_, 0);
                                leanh::lean_inc(v_fst_2010_);
                                v_snd_2011_ = leanh::lean_ctor_get(v___x_2009_, 1);
                                leanh::lean_inc(v_snd_2011_);
                                leanh::lean_dec_ref(v___x_2009_);
                                leanh::lean_inc_ref(v_body_1993_);
                                v___x_2012_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_body_1993_,
                                        v_snd_2011_,
                                    );
                                v_fst_2013_ = leanh::lean_ctor_get(v___x_2012_, 0);
                                leanh::lean_inc(v_fst_2013_);
                                v_snd_2014_ = leanh::lean_ctor_get(v___x_2012_, 1);
                                leanh::lean_inc(v_snd_2014_);
                                leanh::lean_dec_ref(v___x_2012_);
                                v___x_2025_ = lean_ptr_addr(v_type_1991_);
                                v___x_2026_ = lean_ptr_addr(v_fst_2007_);
                                v___x_2027_ = lean_usize_dec_eq(v___x_2025_, v___x_2026_);
                                if v___x_2027_ == 0 {
                                    v___y_2016_ = v___x_2027_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_2028_ = lean_ptr_addr(v_value_1992_);
                                    v___x_2029_ = lean_ptr_addr(v_fst_2010_);
                                    v___x_2030_ = lean_usize_dec_eq(v___x_2028_, v___x_2029_);
                                    v___y_2016_ = v___x_2030_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                    10 => {
                        v_data_2031_ = leanh::lean_ctor_get(v_e_1888_, 0);
                        v_expr_2032_ = leanh::lean_ctor_get(v_e_1888_, 1);
                        v_map_2033_ = leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_2034_ = leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_2035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_2033_, v_e_1888_);
                        if leanh::lean_obj_tag(v___x_2035_) == 1 {
                            leanh::lean_dec_ref_known(v_e_1888_, 2);
                            v_val_2036_ = leanh::lean_ctor_get(v___x_2035_, 0);
                            leanh::lean_inc(v_val_2036_);
                            leanh::lean_dec_ref_known(v___x_2035_, 1);
                            v___x_2037_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2037_, 0, v_val_2036_);
                            leanh::lean_ctor_set(v___x_2037_, 1, v_a_1889_);
                            return v___x_2037_;
                        } else {
                            leanh::lean_dec(v___x_2035_);
                            v___x_2038_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_2039_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_2040_ = lean_uint64_to_usize(v___x_2039_);
                            leanh::lean_inc_ref(v_e_1888_);
                            leanh::lean_inc_ref(v_set_2034_);
                            v___x_2041_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_2034_, v___x_2040_, v_e_1888_, v___x_2038_);
                            v___x_2042_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2041_, v___x_2038_);
                            if v___x_2042_ == 0 {
                                leanh::lean_dec_ref_known(v_e_1888_, 2);
                                v___x_2043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2043_, 0, v___x_2041_);
                                leanh::lean_ctor_set(v___x_2043_, 1, v_a_1889_);
                                return v___x_2043_;
                            } else {
                                leanh::lean_dec_ref(v___x_2041_);
                                leanh::lean_inc_ref(v_expr_2032_);
                                v___x_2044_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_expr_2032_,
                                        v_a_1889_,
                                    );
                                v_fst_2045_ = leanh::lean_ctor_get(v___x_2044_, 0);
                                leanh::lean_inc(v_fst_2045_);
                                v_snd_2046_ = leanh::lean_ctor_get(v___x_2044_, 1);
                                leanh::lean_inc(v_snd_2046_);
                                leanh::lean_dec_ref(v___x_2044_);
                                v___x_2047_ = lean_ptr_addr(v_expr_2032_);
                                v___x_2048_ = lean_ptr_addr(v_fst_2045_);
                                v___x_2049_ = lean_usize_dec_eq(v___x_2047_, v___x_2048_);
                                if v___x_2049_ == 0 {
                                    leanh::lean_inc(v_data_2031_);
                                    v___x_2050_ =
                                        l_Lean_Expr_mdata___override(v_data_2031_, v_fst_2045_);
                                    v___x_2051_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v___x_2050_, v_snd_2046_);
                                    return v___x_2051_;
                                } else {
                                    leanh::lean_dec(v_fst_2045_);
                                    leanh::lean_inc_ref(v_e_1888_);
                                    v___x_2052_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v_e_1888_, v_snd_2046_);
                                    return v___x_2052_;
                                }
                            }
                        }
                    }
                    11 => {
                        v_typeName_2053_ = leanh::lean_ctor_get(v_e_1888_, 0);
                        v_idx_2054_ = leanh::lean_ctor_get(v_e_1888_, 1);
                        v_struct_2055_ = leanh::lean_ctor_get(v_e_1888_, 2);
                        v_map_2056_ = leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_2057_ = leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_2058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_2056_, v_e_1888_);
                        if leanh::lean_obj_tag(v___x_2058_) == 1 {
                            leanh::lean_dec_ref_known(v_e_1888_, 3);
                            v_val_2059_ = leanh::lean_ctor_get(v___x_2058_, 0);
                            leanh::lean_inc(v_val_2059_);
                            leanh::lean_dec_ref_known(v___x_2058_, 1);
                            v___x_2060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2060_, 0, v_val_2059_);
                            leanh::lean_ctor_set(v___x_2060_, 1, v_a_1889_);
                            return v___x_2060_;
                        } else {
                            leanh::lean_dec(v___x_2058_);
                            v___x_2061_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_2062_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_2063_ = lean_uint64_to_usize(v___x_2062_);
                            leanh::lean_inc_ref(v_e_1888_);
                            leanh::lean_inc_ref(v_set_2057_);
                            v___x_2064_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_2057_, v___x_2063_, v_e_1888_, v___x_2061_);
                            v___x_2065_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2064_, v___x_2061_);
                            if v___x_2065_ == 0 {
                                leanh::lean_dec_ref_known(v_e_1888_, 3);
                                v___x_2066_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2066_, 0, v___x_2064_);
                                leanh::lean_ctor_set(v___x_2066_, 1, v_a_1889_);
                                return v___x_2066_;
                            } else {
                                leanh::lean_dec_ref(v___x_2064_);
                                leanh::lean_inc_ref(v_struct_2055_);
                                v___x_2067_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_struct_2055_,
                                        v_a_1889_,
                                    );
                                v_fst_2068_ = leanh::lean_ctor_get(v___x_2067_, 0);
                                leanh::lean_inc(v_fst_2068_);
                                v_snd_2069_ = leanh::lean_ctor_get(v___x_2067_, 1);
                                leanh::lean_inc(v_snd_2069_);
                                leanh::lean_dec_ref(v___x_2067_);
                                v___x_2070_ = lean_ptr_addr(v_struct_2055_);
                                v___x_2071_ = lean_ptr_addr(v_fst_2068_);
                                v___x_2072_ = lean_usize_dec_eq(v___x_2070_, v___x_2071_);
                                if v___x_2072_ == 0 {
                                    leanh::lean_inc(v_idx_2054_);
                                    leanh::lean_inc(v_typeName_2053_);
                                    v___x_2073_ = l_Lean_Expr_proj___override(
                                        v_typeName_2053_,
                                        v_idx_2054_,
                                        v_fst_2068_,
                                    );
                                    v___x_2074_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v___x_2073_, v_snd_2069_);
                                    return v___x_2074_;
                                } else {
                                    leanh::lean_dec(v_fst_2068_);
                                    leanh::lean_inc_ref(v_e_1888_);
                                    v___x_2075_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v_e_1888_, v_snd_2069_);
                                    return v___x_2075_;
                                }
                            }
                        }
                    }
                    _ => {
                        v_map_2076_ = leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_2077_ = leanh::lean_ctor_get(v_a_1889_, 1);
                        leanh::lean_inc_ref(v_e_1888_);
                        v___x_2078_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_set_2077_, v_e_1888_);
                        if leanh::lean_obj_tag(v___x_2078_) == 0 {
                            leanh::lean_inc_ref(v_set_2077_);
                            leanh::lean_inc_ref(v_map_2076_);
                            v_isSharedCheck_2088_ =
                                (!leanh::lean_is_exclusive(v_a_1889_)) as u8;
                            if v_isSharedCheck_2088_ == 0 {
                                v_unused_2089_ = leanh::lean_ctor_get(v_a_1889_, 1);
                                leanh::lean_dec(v_unused_2089_);
                                v_unused_2090_ = leanh::lean_ctor_get(v_a_1889_, 0);
                                leanh::lean_dec(v_unused_2090_);
                                v___x_2080_ = v_a_1889_;
                                v_isShared_2081_ = v_isSharedCheck_2088_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_1889_);
                                v___x_2080_ = leanh::lean_box(0);
                                v_isShared_2081_ = v_isSharedCheck_2088_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_1888_);
                            v_val_2091_ = leanh::lean_ctor_get(v___x_2078_, 0);
                            leanh::lean_inc(v_val_2091_);
                            leanh::lean_dec_ref_known(v___x_2078_, 1);
                            v_fst_2092_ = leanh::lean_ctor_get(v_val_2091_, 0);
                            v_isSharedCheck_2099_ =
                                (!leanh::lean_is_exclusive(v_val_2091_)) as u8;
                            if v_isSharedCheck_2099_ == 0 {
                                v_unused_2100_ = leanh::lean_ctor_get(v_val_2091_, 1);
                                leanh::lean_dec(v_unused_2100_);
                                v___x_2094_ = v_val_2091_;
                                v_isShared_2095_ = v_isSharedCheck_2099_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_fst_2092_);
                                leanh::lean_dec(v_val_2091_);
                                v___x_2094_ = leanh::lean_box(0);
                                v_isShared_2095_ = v_isSharedCheck_2099_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_1910_ == 0 {
                    v___x_1911_ = l_Lean_Expr_app___override(v_fst_1904_, v_fst_1907_);
                    v___x_1912_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_1911_,
                        v_snd_1908_,
                    );
                    return v___x_1912_;
                } else {
                    leanh::lean_dec(v_fst_1907_);
                    leanh::lean_dec(v_fst_1904_);
                    leanh::lean_inc_ref(v_e_1888_);
                    v___x_1913_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v_e_1888_,
                        v_snd_1908_,
                    );
                    return v___x_1913_;
                }
            }
            2 => {
                if v___y_1942_ == 0 {
                    leanh::lean_inc(v_binderName_1920_);
                    v___x_1943_ = l_Lean_Expr_lam___override(
                        v_binderName_1920_,
                        v_fst_1936_,
                        v_fst_1939_,
                        v_binderInfo_1923_,
                    );
                    v___x_1944_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_1943_,
                        v_snd_1940_,
                    );
                    return v___x_1944_;
                } else {
                    v___x_1945_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1923_, v_binderInfo_1923_);
                    if v___x_1945_ == 0 {
                        leanh::lean_inc(v_binderName_1920_);
                        v___x_1946_ = l_Lean_Expr_lam___override(
                            v_binderName_1920_,
                            v_fst_1936_,
                            v_fst_1939_,
                            v_binderInfo_1923_,
                        );
                        v___x_1947_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v___x_1946_,
                                v_snd_1940_,
                            );
                        return v___x_1947_;
                    } else {
                        leanh::lean_dec(v_fst_1939_);
                        leanh::lean_dec(v_fst_1936_);
                        leanh::lean_inc_ref(v_e_1888_);
                        v___x_1948_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v_e_1888_,
                                v_snd_1940_,
                            );
                        return v___x_1948_;
                    }
                }
            }
            3 => {
                if v___y_1977_ == 0 {
                    leanh::lean_inc(v_binderName_1955_);
                    v___x_1978_ = l_Lean_Expr_forallE___override(
                        v_binderName_1955_,
                        v_fst_1971_,
                        v_fst_1974_,
                        v_binderInfo_1958_,
                    );
                    v___x_1979_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_1978_,
                        v_snd_1975_,
                    );
                    return v___x_1979_;
                } else {
                    v___x_1980_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1958_, v_binderInfo_1958_);
                    if v___x_1980_ == 0 {
                        leanh::lean_inc(v_binderName_1955_);
                        v___x_1981_ = l_Lean_Expr_forallE___override(
                            v_binderName_1955_,
                            v_fst_1971_,
                            v_fst_1974_,
                            v_binderInfo_1958_,
                        );
                        v___x_1982_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v___x_1981_,
                                v_snd_1975_,
                            );
                        return v___x_1982_;
                    } else {
                        leanh::lean_dec(v_fst_1974_);
                        leanh::lean_dec(v_fst_1971_);
                        leanh::lean_inc_ref(v_e_1888_);
                        v___x_1983_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v_e_1888_,
                                v_snd_1975_,
                            );
                        return v___x_1983_;
                    }
                }
            }
            4 => {
                if v___y_2016_ == 0 {
                    leanh::lean_inc(v_declName_1990_);
                    v___x_2017_ = l_Lean_Expr_letE___override(
                        v_declName_1990_,
                        v_fst_2007_,
                        v_fst_2010_,
                        v_fst_2013_,
                        v_nondep_1994_,
                    );
                    v___x_2018_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_2017_,
                        v_snd_2014_,
                    );
                    return v___x_2018_;
                } else {
                    v___x_2019_ = lean_ptr_addr(v_body_1993_);
                    v___x_2020_ = lean_ptr_addr(v_fst_2013_);
                    v___x_2021_ = lean_usize_dec_eq(v___x_2019_, v___x_2020_);
                    if v___x_2021_ == 0 {
                        leanh::lean_inc(v_declName_1990_);
                        v___x_2022_ = l_Lean_Expr_letE___override(
                            v_declName_1990_,
                            v_fst_2007_,
                            v_fst_2010_,
                            v_fst_2013_,
                            v_nondep_1994_,
                        );
                        v___x_2023_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v___x_2022_,
                                v_snd_2014_,
                            );
                        return v___x_2023_;
                    } else {
                        leanh::lean_dec(v_fst_2013_);
                        leanh::lean_dec(v_fst_2010_);
                        leanh::lean_dec(v_fst_2007_);
                        leanh::lean_inc_ref(v_e_1888_);
                        v___x_2024_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v_e_1888_,
                                v_snd_2014_,
                            );
                        return v___x_2024_;
                    }
                }
            }
            5 => {
                v___x_2082_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_e_1888_);
                v___x_2083_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_2077_, v_e_1888_, v___x_2082_);
                if v_isShared_2081_ == 0 {
                    leanh::lean_ctor_set(v___x_2080_, 1, v___x_2083_);
                    v___x_2085_ = v___x_2080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_map_2076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2083_);
                    v___x_2085_ = v_reuseFailAlloc_2087_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2086_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2086_, 0, v_e_1888_);
                leanh::lean_ctor_set(v___x_2086_, 1, v___x_2085_);
                return v___x_2086_;
            }
            7 => {
                if v_isShared_2095_ == 0 {
                    leanh::lean_ctor_set(v___x_2094_, 1, v_a_1889_);
                    v___x_2097_ = v___x_2094_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2098_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_fst_2092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_a_1889_);
                    v___x_2097_ = v_reuseFailAlloc_2098_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(
    mut v_00_u03b2_2101_: *mut leanh::LeanObject,
    mut v_m_2102_: *mut leanh::LeanObject,
    mut v_a_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_2102_, v_a_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(
    mut v_00_u03b2_2105_: *mut leanh::LeanObject,
    mut v_m_2106_: *mut leanh::LeanObject,
    mut v_a_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_2105_, v_m_2106_, v_a_2107_);
    leanh::lean_dec_ref(v_a_2107_);
    leanh::lean_dec_ref(v_m_2106_);
    return v_res_2108_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(
    mut v_00_u03b2_2109_: *mut leanh::LeanObject,
    mut v_x_2110_: *mut leanh::LeanObject,
    mut v_x_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_x_2110_, v_x_2111_);
    return v___x_2112_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(
    mut v_00_u03b2_2113_: *mut leanh::LeanObject,
    mut v_x_2114_: *mut leanh::LeanObject,
    mut v_x_2115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_2113_, v_x_2114_, v_x_2115_);
    leanh::lean_dec_ref(v_x_2114_);
    return v_res_2116_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(
    mut v_00_u03b2_2117_: *mut leanh::LeanObject,
    mut v_a_2118_: *mut leanh::LeanObject,
    mut v_x_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_2118_, v_x_2119_);
    return v___x_2120_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_2121_: *mut leanh::LeanObject,
    mut v_a_2122_: *mut leanh::LeanObject,
    mut v_x_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_2121_, v_a_2122_, v_x_2123_);
    leanh::lean_dec(v_x_2123_);
    leanh::lean_dec_ref(v_a_2122_);
    return v_res_2124_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(
    mut v_00_u03b2_2125_: *mut leanh::LeanObject,
    mut v_x_2126_: *mut leanh::LeanObject,
    mut v_x_2127_: usize,
    mut v_x_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_x_2126_);
    v___x_2129_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_2126_, v_x_2127_, v_x_2128_);
    return v___x_2129_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(
    mut v_00_u03b2_2130_: *mut leanh::LeanObject,
    mut v_x_2131_: *mut leanh::LeanObject,
    mut v_x_2132_: *mut leanh::LeanObject,
    mut v_x_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_9303__boxed_2134_: usize = 0;
    let mut v_res_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_9303__boxed_2134_ = leanh::lean_unbox_usize(v_x_2132_);
    leanh::lean_dec(v_x_2132_);
    v_res_2135_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_2130_, v_x_2131_, v_x_9303__boxed_2134_, v_x_2133_);
    leanh::lean_dec_ref(v_x_2131_);
    return v_res_2135_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2136_: *mut leanh::LeanObject,
    mut v_keys_2137_: *mut leanh::LeanObject,
    mut v_vals_2138_: *mut leanh::LeanObject,
    mut v_heq_2139_: *mut leanh::LeanObject,
    mut v_i_2140_: *mut leanh::LeanObject,
    mut v_k_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2142_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_2137_, v_vals_2138_, v_i_2140_, v_k_2141_);
    return v___x_2142_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_2143_: *mut leanh::LeanObject,
    mut v_keys_2144_: *mut leanh::LeanObject,
    mut v_vals_2145_: *mut leanh::LeanObject,
    mut v_heq_2146_: *mut leanh::LeanObject,
    mut v_i_2147_: *mut leanh::LeanObject,
    mut v_k_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2149_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(v_00_u03b2_2143_, v_keys_2144_, v_vals_2145_, v_heq_2146_, v_i_2147_, v_k_2148_);
    leanh::lean_dec_ref(v_vals_2145_);
    leanh::lean_dec_ref(v_keys_2144_);
    return v_res_2149_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = leanh::lean_box(0);
    v___x_2151_ = leanh::lean_unsigned_to_nat(16);
    v___x_2152_ = lean_mk_array(v___x_2151_, v___x_2150_);
    return v___x_2152_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__0_once),
        _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0,
    );
    v___x_2154_ = leanh::lean_unsigned_to_nat(0);
    v___x_2155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2155_, 1, v___x_2153_);
    return v___x_2155_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonAlpha(
    mut v_e_2156_: *mut leanh::LeanObject,
    mut v_s_2157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v_set_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_val_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2178_: u8 = 0;
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_unused_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2158_ = l_Lean_Meta_Sym_instBEqAlphaKey___closed__0;
                v___f_2159_ = l_Lean_Meta_Sym_instHashableAlphaKey___closed__0;
                leanh::lean_inc_ref(v_e_2156_);
                v___x_2160_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(
                    v___f_2158_,
                    v___f_2159_,
                    v_s_2157_,
                    v_e_2156_,
                );
                if leanh::lean_obj_tag(v___x_2160_) == 0 {
                    v___x_2161_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__1_once),
                        _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1,
                    );
                    v___x_2162_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2162_, 0, v___x_2161_);
                    leanh::lean_ctor_set(v___x_2162_, 1, v_s_2157_);
                    v___x_2163_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                        v_e_2156_,
                        v___x_2162_,
                    );
                    v_snd_2164_ = leanh::lean_ctor_get(v___x_2163_, 1);
                    v_fst_2165_ = leanh::lean_ctor_get(v___x_2163_, 0);
                    v_isSharedCheck_2173_ = (!leanh::lean_is_exclusive(v___x_2163_)) as u8;
                    if v_isSharedCheck_2173_ == 0 {
                        v___x_2167_ = v___x_2163_;
                        v_isShared_2168_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2164_);
                        leanh::lean_inc(v_fst_2165_);
                        leanh::lean_dec(v___x_2163_);
                        v___x_2167_ = leanh::lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2156_);
                    v_val_2174_ = leanh::lean_ctor_get(v___x_2160_, 0);
                    leanh::lean_inc(v_val_2174_);
                    leanh::lean_dec_ref_known(v___x_2160_, 1);
                    v_fst_2175_ = leanh::lean_ctor_get(v_val_2174_, 0);
                    v_isSharedCheck_2182_ = (!leanh::lean_is_exclusive(v_val_2174_)) as u8;
                    if v_isSharedCheck_2182_ == 0 {
                        v_unused_2183_ = leanh::lean_ctor_get(v_val_2174_, 1);
                        leanh::lean_dec(v_unused_2183_);
                        v___x_2177_ = v_val_2174_;
                        v_isShared_2178_ = v_isSharedCheck_2182_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2175_);
                        leanh::lean_dec(v_val_2174_);
                        v___x_2177_ = leanh::lean_box(0);
                        v_isShared_2178_ = v_isSharedCheck_2182_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_set_2169_ = leanh::lean_ctor_get(v_snd_2164_, 1);
                leanh::lean_inc_ref(v_set_2169_);
                leanh::lean_dec(v_snd_2164_);
                if v_isShared_2168_ == 0 {
                    leanh::lean_ctor_set(v___x_2167_, 1, v_set_2169_);
                    v___x_2171_ = v___x_2167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_fst_2165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_set_2169_);
                    v___x_2171_ = v_reuseFailAlloc_2172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2171_;
            }
            3 => {
                if v_isShared_2178_ == 0 {
                    leanh::lean_ctor_set(v___x_2177_, 1, v_s_2157_);
                    v___x_2180_ = v___x_2177_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_fst_2175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_s_2157_);
                    v___x_2180_ = v_reuseFailAlloc_2181_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
    mut v_e_2184_: *mut leanh::LeanObject,
    mut v_a_2185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u64 = 0;
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    v___x_2186_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
    v___x_2187_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_2184_);
    v___x_2188_ = lean_uint64_to_usize(v___x_2187_);
    leanh::lean_inc_ref(v_e_2184_);
    leanh::lean_inc_ref(v_a_2185_);
    v___x_2189_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2185_, v___x_2188_, v_e_2184_, v___x_2186_);
    v___x_2190_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2189_,
        v___x_2186_,
    );
    if v___x_2190_ == 0 {
        let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_2184_);
        v___x_2191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2191_, 0, v___x_2189_);
        leanh::lean_ctor_set(v___x_2191_, 1, v_a_2185_);
        return v___x_2191_;
    } else {
        let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2189_);
        v___x_2192_ = leanh::lean_box(0);
        leanh::lean_inc_ref(v_e_2184_);
        v___x_2193_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_2185_, v_e_2184_, v___x_2192_);
        v___x_2194_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2194_, 0, v_e_2184_);
        leanh::lean_ctor_set(v___x_2194_, 1, v___x_2193_);
        return v___x_2194_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(
    mut v_e_2195_: *mut leanh::LeanObject,
    mut v_k_2196_: *mut leanh::LeanObject,
    mut v_a_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u64 = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    v___f_2198_ = l_Lean_Meta_Sym_instBEqAlphaKey___closed__0;
    v___x_2199_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
    v___x_2200_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_2195_);
    v___x_2201_ = lean_uint64_to_usize(v___x_2200_);
    leanh::lean_inc_ref(v_a_2197_);
    v___x_2202_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v___f_2198_,
        v_a_2197_,
        v___x_2201_,
        v_e_2195_,
        v___x_2199_,
    );
    v___x_2203_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2202_,
        v___x_2199_,
    );
    if v___x_2203_ == 0 {
        let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_2196_);
        v___x_2204_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2204_, 0, v___x_2202_);
        leanh::lean_ctor_set(v___x_2204_, 1, v_a_2197_);
        return v___x_2204_;
    } else {
        let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_2202_);
        v___x_2205_ = leanh::lean_apply_1(v_k_2196_, v_a_2197_);
        v_fst_2206_ = leanh::lean_ctor_get(v___x_2205_, 0);
        leanh::lean_inc(v_fst_2206_);
        v_snd_2207_ = leanh::lean_ctor_get(v___x_2205_, 1);
        leanh::lean_inc(v_snd_2207_);
        leanh::lean_dec_ref(v___x_2205_);
        v___x_2208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
            v_fst_2206_,
            v_snd_2207_,
        );
        return v___x_2208_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(
    mut v_e_2209_: *mut leanh::LeanObject,
    mut v_a_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: u64 = 0;
    let mut v___x_2215_: usize = 0;
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: usize = 0;
    let mut v___x_2231_: usize = 0;
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: usize = 0;
    let mut v___x_2234_: usize = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v_binderName_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2239_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u64 = 0;
    let mut v___x_2242_: usize = 0;
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: u8 = 0;
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: u8 = 0;
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: usize = 0;
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: usize = 0;
    let mut v___x_2264_: usize = 0;
    let mut v___x_2265_: u8 = 0;
    let mut v_binderName_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2269_: u8 = 0;
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u64 = 0;
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: u8 = 0;
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: usize = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: u8 = 0;
    let mut v_declName_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2300_: u8 = 0;
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u64 = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2317_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: usize = 0;
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: usize = 0;
    let mut v___x_2327_: usize = 0;
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v_data_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u64 = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: usize = 0;
    let mut v___x_2344_: usize = 0;
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u64 = 0;
    let mut v___x_2354_: usize = 0;
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_e_2209_) {
                    5 => {
                        v_fn_2211_ = leanh::lean_ctor_get(v_e_2209_, 0);
                        v_arg_2212_ = leanh::lean_ctor_get(v_e_2209_, 1);
                        v___x_2213_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2214_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2215_ = lean_uint64_to_usize(v___x_2214_);
                        leanh::lean_inc_ref(v_e_2209_);
                        leanh::lean_inc_ref(v_a_2210_);
                        v___x_2216_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2215_, v_e_2209_, v___x_2213_);
                        v___x_2217_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2216_,
                                v___x_2213_,
                            );
                        if v___x_2217_ == 0 {
                            leanh::lean_dec_ref_known(v_e_2209_, 2);
                            v___x_2218_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2218_, 0, v___x_2216_);
                            leanh::lean_ctor_set(v___x_2218_, 1, v_a_2210_);
                            return v___x_2218_;
                        } else {
                            leanh::lean_dec_ref(v___x_2216_);
                            leanh::lean_inc_ref(v_fn_2211_);
                            v___x_2219_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_2211_, v_a_2210_);
                            v_fst_2220_ = leanh::lean_ctor_get(v___x_2219_, 0);
                            leanh::lean_inc(v_fst_2220_);
                            v_snd_2221_ = leanh::lean_ctor_get(v___x_2219_, 1);
                            leanh::lean_inc(v_snd_2221_);
                            leanh::lean_dec_ref(v___x_2219_);
                            leanh::lean_inc_ref(v_arg_2212_);
                            v___x_2222_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_2212_, v_snd_2221_);
                            v_fst_2223_ = leanh::lean_ctor_get(v___x_2222_, 0);
                            leanh::lean_inc(v_fst_2223_);
                            v_snd_2224_ = leanh::lean_ctor_get(v___x_2222_, 1);
                            leanh::lean_inc(v_snd_2224_);
                            leanh::lean_dec_ref(v___x_2222_);
                            v___x_2230_ = lean_ptr_addr(v_fn_2211_);
                            v___x_2231_ = lean_ptr_addr(v_fst_2220_);
                            v___x_2232_ = lean_usize_dec_eq(v___x_2230_, v___x_2231_);
                            if v___x_2232_ == 0 {
                                v___y_2226_ = v___x_2232_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2233_ = lean_ptr_addr(v_arg_2212_);
                                v___x_2234_ = lean_ptr_addr(v_fst_2223_);
                                v___x_2235_ = lean_usize_dec_eq(v___x_2233_, v___x_2234_);
                                v___y_2226_ = v___x_2235_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    6 => {
                        v_binderName_2236_ = leanh::lean_ctor_get(v_e_2209_, 0);
                        v_binderType_2237_ = leanh::lean_ctor_get(v_e_2209_, 1);
                        v_body_2238_ = leanh::lean_ctor_get(v_e_2209_, 2);
                        v_binderInfo_2239_ = leanh::lean_ctor_get_uint8(
                            v_e_2209_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v___x_2240_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2241_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2242_ = lean_uint64_to_usize(v___x_2241_);
                        leanh::lean_inc_ref(v_e_2209_);
                        leanh::lean_inc_ref(v_a_2210_);
                        v___x_2243_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2242_, v_e_2209_, v___x_2240_);
                        v___x_2244_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2243_,
                                v___x_2240_,
                            );
                        if v___x_2244_ == 0 {
                            leanh::lean_dec_ref_known(v_e_2209_, 3);
                            v___x_2245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2245_, 0, v___x_2243_);
                            leanh::lean_ctor_set(v___x_2245_, 1, v_a_2210_);
                            return v___x_2245_;
                        } else {
                            leanh::lean_dec_ref(v___x_2243_);
                            leanh::lean_inc_ref(v_binderType_2237_);
                            v___x_2246_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_2237_, v_a_2210_);
                            v_fst_2247_ = leanh::lean_ctor_get(v___x_2246_, 0);
                            leanh::lean_inc(v_fst_2247_);
                            v_snd_2248_ = leanh::lean_ctor_get(v___x_2246_, 1);
                            leanh::lean_inc(v_snd_2248_);
                            leanh::lean_dec_ref(v___x_2246_);
                            leanh::lean_inc_ref(v_body_2238_);
                            v___x_2249_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_2238_, v_snd_2248_);
                            v_fst_2250_ = leanh::lean_ctor_get(v___x_2249_, 0);
                            leanh::lean_inc(v_fst_2250_);
                            v_snd_2251_ = leanh::lean_ctor_get(v___x_2249_, 1);
                            leanh::lean_inc(v_snd_2251_);
                            leanh::lean_dec_ref(v___x_2249_);
                            v___x_2260_ = lean_ptr_addr(v_binderType_2237_);
                            v___x_2261_ = lean_ptr_addr(v_fst_2247_);
                            v___x_2262_ = lean_usize_dec_eq(v___x_2260_, v___x_2261_);
                            if v___x_2262_ == 0 {
                                v___y_2253_ = v___x_2262_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2263_ = lean_ptr_addr(v_body_2238_);
                                v___x_2264_ = lean_ptr_addr(v_fst_2250_);
                                v___x_2265_ = lean_usize_dec_eq(v___x_2263_, v___x_2264_);
                                v___y_2253_ = v___x_2265_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    7 => {
                        v_binderName_2266_ = leanh::lean_ctor_get(v_e_2209_, 0);
                        v_binderType_2267_ = leanh::lean_ctor_get(v_e_2209_, 1);
                        v_body_2268_ = leanh::lean_ctor_get(v_e_2209_, 2);
                        v_binderInfo_2269_ = leanh::lean_ctor_get_uint8(
                            v_e_2209_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v___x_2270_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2271_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2272_ = lean_uint64_to_usize(v___x_2271_);
                        leanh::lean_inc_ref(v_e_2209_);
                        leanh::lean_inc_ref(v_a_2210_);
                        v___x_2273_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2272_, v_e_2209_, v___x_2270_);
                        v___x_2274_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2273_,
                                v___x_2270_,
                            );
                        if v___x_2274_ == 0 {
                            leanh::lean_dec_ref_known(v_e_2209_, 3);
                            v___x_2275_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2275_, 0, v___x_2273_);
                            leanh::lean_ctor_set(v___x_2275_, 1, v_a_2210_);
                            return v___x_2275_;
                        } else {
                            leanh::lean_dec_ref(v___x_2273_);
                            leanh::lean_inc_ref(v_binderType_2267_);
                            v___x_2276_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_2267_, v_a_2210_);
                            v_fst_2277_ = leanh::lean_ctor_get(v___x_2276_, 0);
                            leanh::lean_inc(v_fst_2277_);
                            v_snd_2278_ = leanh::lean_ctor_get(v___x_2276_, 1);
                            leanh::lean_inc(v_snd_2278_);
                            leanh::lean_dec_ref(v___x_2276_);
                            leanh::lean_inc_ref(v_body_2268_);
                            v___x_2279_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_2268_, v_snd_2278_);
                            v_fst_2280_ = leanh::lean_ctor_get(v___x_2279_, 0);
                            leanh::lean_inc(v_fst_2280_);
                            v_snd_2281_ = leanh::lean_ctor_get(v___x_2279_, 1);
                            leanh::lean_inc(v_snd_2281_);
                            leanh::lean_dec_ref(v___x_2279_);
                            v___x_2290_ = lean_ptr_addr(v_binderType_2267_);
                            v___x_2291_ = lean_ptr_addr(v_fst_2277_);
                            v___x_2292_ = lean_usize_dec_eq(v___x_2290_, v___x_2291_);
                            if v___x_2292_ == 0 {
                                v___y_2283_ = v___x_2292_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2293_ = lean_ptr_addr(v_body_2268_);
                                v___x_2294_ = lean_ptr_addr(v_fst_2280_);
                                v___x_2295_ = lean_usize_dec_eq(v___x_2293_, v___x_2294_);
                                v___y_2283_ = v___x_2295_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    8 => {
                        v_declName_2296_ = leanh::lean_ctor_get(v_e_2209_, 0);
                        v_type_2297_ = leanh::lean_ctor_get(v_e_2209_, 1);
                        v_value_2298_ = leanh::lean_ctor_get(v_e_2209_, 2);
                        v_body_2299_ = leanh::lean_ctor_get(v_e_2209_, 3);
                        v_nondep_2300_ = leanh::lean_ctor_get_uint8(
                            v_e_2209_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        v___x_2301_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2302_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2303_ = lean_uint64_to_usize(v___x_2302_);
                        leanh::lean_inc_ref(v_e_2209_);
                        leanh::lean_inc_ref(v_a_2210_);
                        v___x_2304_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2303_, v_e_2209_, v___x_2301_);
                        v___x_2305_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2304_,
                                v___x_2301_,
                            );
                        if v___x_2305_ == 0 {
                            leanh::lean_dec_ref_known(v_e_2209_, 4);
                            v___x_2306_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2306_, 0, v___x_2304_);
                            leanh::lean_ctor_set(v___x_2306_, 1, v_a_2210_);
                            return v___x_2306_;
                        } else {
                            leanh::lean_dec_ref(v___x_2304_);
                            leanh::lean_inc_ref(v_type_2297_);
                            v___x_2307_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_2297_, v_a_2210_);
                            v_fst_2308_ = leanh::lean_ctor_get(v___x_2307_, 0);
                            leanh::lean_inc(v_fst_2308_);
                            v_snd_2309_ = leanh::lean_ctor_get(v___x_2307_, 1);
                            leanh::lean_inc(v_snd_2309_);
                            leanh::lean_dec_ref(v___x_2307_);
                            leanh::lean_inc_ref(v_value_2298_);
                            v___x_2310_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_2298_, v_snd_2309_);
                            v_fst_2311_ = leanh::lean_ctor_get(v___x_2310_, 0);
                            leanh::lean_inc(v_fst_2311_);
                            v_snd_2312_ = leanh::lean_ctor_get(v___x_2310_, 1);
                            leanh::lean_inc(v_snd_2312_);
                            leanh::lean_dec_ref(v___x_2310_);
                            leanh::lean_inc_ref(v_body_2299_);
                            v___x_2313_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_2299_, v_snd_2312_);
                            v_fst_2314_ = leanh::lean_ctor_get(v___x_2313_, 0);
                            leanh::lean_inc(v_fst_2314_);
                            v_snd_2315_ = leanh::lean_ctor_get(v___x_2313_, 1);
                            leanh::lean_inc(v_snd_2315_);
                            leanh::lean_dec_ref(v___x_2313_);
                            v___x_2326_ = lean_ptr_addr(v_type_2297_);
                            v___x_2327_ = lean_ptr_addr(v_fst_2308_);
                            v___x_2328_ = lean_usize_dec_eq(v___x_2326_, v___x_2327_);
                            if v___x_2328_ == 0 {
                                v___y_2317_ = v___x_2328_;
                                state = 4;
                                continue;
                            } else {
                                v___x_2329_ = lean_ptr_addr(v_value_2298_);
                                v___x_2330_ = lean_ptr_addr(v_fst_2311_);
                                v___x_2331_ = lean_usize_dec_eq(v___x_2329_, v___x_2330_);
                                v___y_2317_ = v___x_2331_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                    10 => {
                        v_data_2332_ = leanh::lean_ctor_get(v_e_2209_, 0);
                        v_expr_2333_ = leanh::lean_ctor_get(v_e_2209_, 1);
                        v___x_2334_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2335_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2336_ = lean_uint64_to_usize(v___x_2335_);
                        leanh::lean_inc_ref(v_e_2209_);
                        leanh::lean_inc_ref(v_a_2210_);
                        v___x_2337_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2336_, v_e_2209_, v___x_2334_);
                        v___x_2338_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2337_,
                                v___x_2334_,
                            );
                        if v___x_2338_ == 0 {
                            leanh::lean_dec_ref_known(v_e_2209_, 2);
                            v___x_2339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2339_, 0, v___x_2337_);
                            leanh::lean_ctor_set(v___x_2339_, 1, v_a_2210_);
                            return v___x_2339_;
                        } else {
                            leanh::lean_dec_ref(v___x_2337_);
                            leanh::lean_inc_ref(v_expr_2333_);
                            v___x_2340_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_2333_, v_a_2210_);
                            v_fst_2341_ = leanh::lean_ctor_get(v___x_2340_, 0);
                            leanh::lean_inc(v_fst_2341_);
                            v_snd_2342_ = leanh::lean_ctor_get(v___x_2340_, 1);
                            leanh::lean_inc(v_snd_2342_);
                            leanh::lean_dec_ref(v___x_2340_);
                            v___x_2343_ = lean_ptr_addr(v_expr_2333_);
                            v___x_2344_ = lean_ptr_addr(v_fst_2341_);
                            v___x_2345_ = lean_usize_dec_eq(v___x_2343_, v___x_2344_);
                            if v___x_2345_ == 0 {
                                leanh::lean_inc(v_data_2332_);
                                leanh::lean_dec_ref_known(v_e_2209_, 2);
                                v___x_2346_ =
                                    l_Lean_Expr_mdata___override(v_data_2332_, v_fst_2341_);
                                v___x_2347_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_2346_, v_snd_2342_);
                                return v___x_2347_;
                            } else {
                                leanh::lean_dec(v_fst_2341_);
                                v___x_2348_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_2209_, v_snd_2342_);
                                return v___x_2348_;
                            }
                        }
                    }
                    11 => {
                        v_typeName_2349_ = leanh::lean_ctor_get(v_e_2209_, 0);
                        v_idx_2350_ = leanh::lean_ctor_get(v_e_2209_, 1);
                        v_struct_2351_ = leanh::lean_ctor_get(v_e_2209_, 2);
                        v___x_2352_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2353_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2354_ = lean_uint64_to_usize(v___x_2353_);
                        leanh::lean_inc_ref(v_e_2209_);
                        leanh::lean_inc_ref(v_a_2210_);
                        v___x_2355_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2354_, v_e_2209_, v___x_2352_);
                        v___x_2356_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2355_,
                                v___x_2352_,
                            );
                        if v___x_2356_ == 0 {
                            leanh::lean_dec_ref_known(v_e_2209_, 3);
                            v___x_2357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2357_, 0, v___x_2355_);
                            leanh::lean_ctor_set(v___x_2357_, 1, v_a_2210_);
                            return v___x_2357_;
                        } else {
                            leanh::lean_dec_ref(v___x_2355_);
                            leanh::lean_inc_ref(v_struct_2351_);
                            v___x_2358_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_2351_, v_a_2210_);
                            v_fst_2359_ = leanh::lean_ctor_get(v___x_2358_, 0);
                            leanh::lean_inc(v_fst_2359_);
                            v_snd_2360_ = leanh::lean_ctor_get(v___x_2358_, 1);
                            leanh::lean_inc(v_snd_2360_);
                            leanh::lean_dec_ref(v___x_2358_);
                            v___x_2361_ = lean_ptr_addr(v_struct_2351_);
                            v___x_2362_ = lean_ptr_addr(v_fst_2359_);
                            v___x_2363_ = lean_usize_dec_eq(v___x_2361_, v___x_2362_);
                            if v___x_2363_ == 0 {
                                leanh::lean_inc(v_idx_2350_);
                                leanh::lean_inc(v_typeName_2349_);
                                leanh::lean_dec_ref_known(v_e_2209_, 3);
                                v___x_2364_ = l_Lean_Expr_proj___override(
                                    v_typeName_2349_,
                                    v_idx_2350_,
                                    v_fst_2359_,
                                );
                                v___x_2365_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_2364_, v_snd_2360_);
                                return v___x_2365_;
                            } else {
                                leanh::lean_dec(v_fst_2359_);
                                v___x_2366_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_2209_, v_snd_2360_);
                                return v___x_2366_;
                            }
                        }
                    }
                    _ => {
                        v___x_2367_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_, v_a_2210_,
                            );
                        return v___x_2367_;
                    }
                }
            }
            1 => {
                if v___y_2226_ == 0 {
                    leanh::lean_dec_ref_known(v_e_2209_, 2);
                    v___x_2227_ = l_Lean_Expr_app___override(v_fst_2220_, v_fst_2223_);
                    v___x_2228_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2227_,
                            v_snd_2224_,
                        );
                    return v___x_2228_;
                } else {
                    leanh::lean_dec(v_fst_2223_);
                    leanh::lean_dec(v_fst_2220_);
                    v___x_2229_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v_e_2209_,
                            v_snd_2224_,
                        );
                    return v___x_2229_;
                }
            }
            2 => {
                if v___y_2253_ == 0 {
                    leanh::lean_inc(v_binderName_2236_);
                    leanh::lean_dec_ref_known(v_e_2209_, 3);
                    v___x_2254_ = l_Lean_Expr_lam___override(
                        v_binderName_2236_,
                        v_fst_2247_,
                        v_fst_2250_,
                        v_binderInfo_2239_,
                    );
                    v___x_2255_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2254_,
                            v_snd_2251_,
                        );
                    return v___x_2255_;
                } else {
                    v___x_2256_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_2239_, v_binderInfo_2239_);
                    if v___x_2256_ == 0 {
                        leanh::lean_inc(v_binderName_2236_);
                        leanh::lean_dec_ref_known(v_e_2209_, 3);
                        v___x_2257_ = l_Lean_Expr_lam___override(
                            v_binderName_2236_,
                            v_fst_2247_,
                            v_fst_2250_,
                            v_binderInfo_2239_,
                        );
                        v___x_2258_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v___x_2257_,
                                v_snd_2251_,
                            );
                        return v___x_2258_;
                    } else {
                        leanh::lean_dec(v_fst_2250_);
                        leanh::lean_dec(v_fst_2247_);
                        v___x_2259_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_,
                                v_snd_2251_,
                            );
                        return v___x_2259_;
                    }
                }
            }
            3 => {
                if v___y_2283_ == 0 {
                    leanh::lean_inc(v_binderName_2266_);
                    leanh::lean_dec_ref_known(v_e_2209_, 3);
                    v___x_2284_ = l_Lean_Expr_forallE___override(
                        v_binderName_2266_,
                        v_fst_2277_,
                        v_fst_2280_,
                        v_binderInfo_2269_,
                    );
                    v___x_2285_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2284_,
                            v_snd_2281_,
                        );
                    return v___x_2285_;
                } else {
                    v___x_2286_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_2269_, v_binderInfo_2269_);
                    if v___x_2286_ == 0 {
                        leanh::lean_inc(v_binderName_2266_);
                        leanh::lean_dec_ref_known(v_e_2209_, 3);
                        v___x_2287_ = l_Lean_Expr_forallE___override(
                            v_binderName_2266_,
                            v_fst_2277_,
                            v_fst_2280_,
                            v_binderInfo_2269_,
                        );
                        v___x_2288_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v___x_2287_,
                                v_snd_2281_,
                            );
                        return v___x_2288_;
                    } else {
                        leanh::lean_dec(v_fst_2280_);
                        leanh::lean_dec(v_fst_2277_);
                        v___x_2289_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_,
                                v_snd_2281_,
                            );
                        return v___x_2289_;
                    }
                }
            }
            4 => {
                if v___y_2317_ == 0 {
                    leanh::lean_inc(v_declName_2296_);
                    leanh::lean_dec_ref_known(v_e_2209_, 4);
                    v___x_2318_ = l_Lean_Expr_letE___override(
                        v_declName_2296_,
                        v_fst_2308_,
                        v_fst_2311_,
                        v_fst_2314_,
                        v_nondep_2300_,
                    );
                    v___x_2319_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2318_,
                            v_snd_2315_,
                        );
                    return v___x_2319_;
                } else {
                    v___x_2320_ = lean_ptr_addr(v_body_2299_);
                    v___x_2321_ = lean_ptr_addr(v_fst_2314_);
                    v___x_2322_ = lean_usize_dec_eq(v___x_2320_, v___x_2321_);
                    if v___x_2322_ == 0 {
                        leanh::lean_inc(v_declName_2296_);
                        leanh::lean_dec_ref_known(v_e_2209_, 4);
                        v___x_2323_ = l_Lean_Expr_letE___override(
                            v_declName_2296_,
                            v_fst_2308_,
                            v_fst_2311_,
                            v_fst_2314_,
                            v_nondep_2300_,
                        );
                        v___x_2324_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v___x_2323_,
                                v_snd_2315_,
                            );
                        return v___x_2324_;
                    } else {
                        leanh::lean_dec(v_fst_2314_);
                        leanh::lean_dec(v_fst_2311_);
                        leanh::lean_dec(v_fst_2308_);
                        v___x_2325_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_,
                                v_snd_2315_,
                            );
                        return v___x_2325_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonAlphaInc(
    mut v_e_2368_: *mut leanh::LeanObject,
    mut v_a_2369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ =
        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(
            v_e_2368_, v_a_2369_,
        );
    return v___x_2370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy =
        _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_AlphaShareCommon(
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
pub unsafe fn initialize_Lean_Meta_Sym_AlphaShareCommon(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
}
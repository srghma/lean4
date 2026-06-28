// Lean compiler output
// Module: Lake.Toml.Data.Dict
// Imports: Lean.Data.NameMap.Basic Init.Data.Nat.Fold
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_isEqvAux___redArg,
};
use crate::r#gen::Init::Data::Nat::Fold::{
    initialize_Init_Data_Nat_Fold, runtime_initialize_Init_Data_Nat_Fold,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic, runtime_initialize_Lean_Data_NameMap_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lake_Toml_instInhabitedRBDict_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lake_Toml_instInhabitedRBDict_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_instInhabitedRBDict_default___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__0_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_Toml_instInhabitedRBDict_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_Toml_RBDict_empty___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_Toml_RBDict_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_empty___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__0_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_RBDict_empty___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_RBDict_map___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_RBDict_map___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_RBDict_map___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__9_value) as *mut LeanObject;
pub unsafe fn l_Lake_Toml_instInhabitedRBDict_default(
    mut v_00_u03b1_1218_: *mut LeanObject,
    mut v_00_u03b2_1219_: *mut LeanObject,
    mut v_cmp_1220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lake_Toml_instInhabitedRBDict_default___closed__1;
    return v___x_1221_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict_default___boxed(
    mut v_00_u03b1_1222_: *mut LeanObject,
    mut v_00_u03b2_1223_: *mut LeanObject,
    mut v_cmp_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1225_: *mut LeanObject = core::ptr::null_mut();
    v_res_1225_ =
        l_Lake_Toml_instInhabitedRBDict_default(v_00_u03b1_1222_, v_00_u03b2_1223_, v_cmp_1224_);
    lean_dec_ref(v_cmp_1224_);
    return v_res_1225_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___redArg(
    mut v_a_1226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    v___x_1227_ = l_Lake_Toml_instInhabitedRBDict_default(lean_box(0), lean_box(0), v_a_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___redArg___boxed(
    mut v_a_1228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1229_: *mut LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lake_Toml_instInhabitedRBDict___redArg(v_a_1228_);
    lean_dec_ref(v_a_1228_);
    return v_res_1229_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict(
    mut v_a_1230_: *mut LeanObject,
    mut v_a_1231_: *mut LeanObject,
    mut v_a_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_Lake_Toml_instInhabitedRBDict_default(lean_box(0), lean_box(0), v_a_1232_);
    return v___x_1233_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___boxed(
    mut v_a_1234_: *mut LeanObject,
    mut v_a_1235_: *mut LeanObject,
    mut v_a_1236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1237_: *mut LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lake_Toml_instInhabitedRBDict(v_a_1234_, v_a_1235_, v_a_1236_);
    lean_dec_ref(v_a_1236_);
    return v_res_1237_;
}
pub unsafe fn l_Lake_Toml_RBDict_empty(
    mut v_00_u03b1_1243_: *mut LeanObject,
    mut v_00_u03b2_1244_: *mut LeanObject,
    mut v_cmp_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lake_Toml_RBDict_empty___closed__1;
    return v___x_1246_;
}
pub unsafe fn l_Lake_Toml_RBDict_empty___boxed(
    mut v_00_u03b1_1247_: *mut LeanObject,
    mut v_00_u03b2_1248_: *mut LeanObject,
    mut v_cmp_1249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1250_: *mut LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Lake_Toml_RBDict_empty(v_00_u03b1_1247_, v_00_u03b2_1248_, v_cmp_1249_);
    lean_dec_ref(v_cmp_1249_);
    return v_res_1250_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___redArg(
    mut v_cmp_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_1251_);
    return v___x_1252_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___redArg___boxed(
    mut v_cmp_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1254_: *mut LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lake_Toml_RBDict_instEmptyCollection___redArg(v_cmp_1253_);
    lean_dec_ref(v_cmp_1253_);
    return v_res_1254_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection(
    mut v_00_u03b1_1255_: *mut LeanObject,
    mut v_00_u03b2_1256_: *mut LeanObject,
    mut v_cmp_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    v___x_1258_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_1257_);
    return v___x_1258_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___boxed(
    mut v_00_u03b1_1259_: *mut LeanObject,
    mut v_00_u03b2_1260_: *mut LeanObject,
    mut v_cmp_1261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1262_: *mut LeanObject = core::ptr::null_mut();
    v_res_1262_ =
        l_Lake_Toml_RBDict_instEmptyCollection(v_00_u03b1_1259_, v_00_u03b2_1260_, v_cmp_1261_);
    lean_dec_ref(v_cmp_1261_);
    return v_res_1262_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___redArg(
    mut v_capacity_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    v___x_1264_ = lean_mk_empty_array_with_capacity(v_capacity_1263_);
    v___x_1265_ = lean_box(1);
    v___x_1266_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1266_, 0, v___x_1264_);
    lean_ctor_set(v___x_1266_, 1, v___x_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___redArg___boxed(
    mut v_capacity_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1268_: *mut LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_1267_);
    lean_dec(v_capacity_1267_);
    return v_res_1268_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty(
    mut v_00_u03b1_1269_: *mut LeanObject,
    mut v_00_u03b2_1270_: *mut LeanObject,
    mut v_cmp_1271_: *mut LeanObject,
    mut v_capacity_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___boxed(
    mut v_00_u03b1_1274_: *mut LeanObject,
    mut v_00_u03b2_1275_: *mut LeanObject,
    mut v_cmp_1276_: *mut LeanObject,
    mut v_capacity_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1278_: *mut LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Lake_Toml_RBDict_mkEmpty(
        v_00_u03b1_1274_,
        v_00_u03b2_1275_,
        v_cmp_1276_,
        v_capacity_1277_,
    );
    lean_dec(v_capacity_1277_);
    lean_dec_ref(v_cmp_1276_);
    return v_res_1278_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(
    mut v_cmp_1279_: *mut LeanObject,
    mut v_k_1280_: *mut LeanObject,
    mut v_v_1281_: *mut LeanObject,
    mut v_t_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v_impl_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v_size_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v_unused_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1367_: u8 = 0;
    let mut v_unused_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_unused_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_unused_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v_k_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_unused_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v_unused_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v_size_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_unused_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1501_: u8 = 0;
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1505_: u8 = 0;
    let mut v_unused_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v_k_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v_unused_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_unused_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1552_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_unused_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1282_) == 0 {
                    v_size_1283_ = lean_ctor_get(v_t_1282_, 0);
                    v_k_1284_ = lean_ctor_get(v_t_1282_, 1);
                    v_v_1285_ = lean_ctor_get(v_t_1282_, 2);
                    v_l_1286_ = lean_ctor_get(v_t_1282_, 3);
                    v_r_1287_ = lean_ctor_get(v_t_1282_, 4);
                    v_isSharedCheck_1568_ = (!lean_is_exclusive(v_t_1282_)) as u8;
                    if v_isSharedCheck_1568_ == 0 {
                        v___x_1289_ = v_t_1282_;
                        v_isShared_1290_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1287_);
                        lean_inc(v_l_1286_);
                        lean_inc(v_v_1285_);
                        lean_inc(v_k_1284_);
                        lean_inc(v_size_1283_);
                        lean_dec(v_t_1282_);
                        v___x_1289_ = lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_cmp_1279_);
                    v___x_1569_ = lean_unsigned_to_nat(1);
                    v___x_1570_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1570_, 0, v___x_1569_);
                    lean_ctor_set(v___x_1570_, 1, v_k_1280_);
                    lean_ctor_set(v___x_1570_, 2, v_v_1281_);
                    lean_ctor_set(v___x_1570_, 3, v_t_1282_);
                    lean_ctor_set(v___x_1570_, 4, v_t_1282_);
                    return v___x_1570_;
                }
            }
            1 => {
                lean_inc_ref(v_cmp_1279_);
                lean_inc(v_k_1284_);
                lean_inc(v_k_1280_);
                v___x_1291_ = lean_apply_2(v_cmp_1279_, v_k_1280_, v_k_1284_);
                v___x_1292_ = (lean_unbox(v___x_1291_) as u8);
                match v___x_1292_ {
                    0 => {
                        lean_dec(v_size_1283_);
                        v_impl_1293_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1279_, v_k_1280_, v_v_1281_, v_l_1286_);
                        v___x_1294_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_1287_) == 0 {
                            v_size_1295_ = lean_ctor_get(v_r_1287_, 0);
                            v_size_1296_ = lean_ctor_get(v_impl_1293_, 0);
                            lean_inc(v_size_1296_);
                            v_k_1297_ = lean_ctor_get(v_impl_1293_, 1);
                            lean_inc(v_k_1297_);
                            v_v_1298_ = lean_ctor_get(v_impl_1293_, 2);
                            lean_inc(v_v_1298_);
                            v_l_1299_ = lean_ctor_get(v_impl_1293_, 3);
                            lean_inc(v_l_1299_);
                            v_r_1300_ = lean_ctor_get(v_impl_1293_, 4);
                            lean_inc(v_r_1300_);
                            v___x_1301_ = lean_unsigned_to_nat(3);
                            v___x_1302_ = lean_nat_mul(v___x_1301_, v_size_1295_);
                            v___x_1303_ = lean_nat_dec_lt(v___x_1302_, v_size_1296_);
                            lean_dec(v___x_1302_);
                            if v___x_1303_ == 0 {
                                lean_dec(v_r_1300_);
                                lean_dec(v_l_1299_);
                                lean_dec(v_v_1298_);
                                lean_dec(v_k_1297_);
                                v___x_1304_ = lean_nat_add(v___x_1294_, v_size_1296_);
                                lean_dec(v_size_1296_);
                                v___x_1305_ = lean_nat_add(v___x_1304_, v_size_1295_);
                                lean_dec(v___x_1304_);
                                if v_isShared_1290_ == 0 {
                                    lean_ctor_set(v___x_1289_, 3, v_impl_1293_);
                                    lean_ctor_set(v___x_1289_, 0, v___x_1305_);
                                    v___x_1307_ = v___x_1289_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
                                    lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_k_1284_);
                                    lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_v_1285_);
                                    lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_impl_1293_);
                                    lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_r_1287_);
                                    v___x_1307_ = v_reuseFailAlloc_1308_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1374_ = (!lean_is_exclusive(v_impl_1293_)) as u8;
                                if v_isSharedCheck_1374_ == 0 {
                                    v_unused_1375_ = lean_ctor_get(v_impl_1293_, 4);
                                    lean_dec(v_unused_1375_);
                                    v_unused_1376_ = lean_ctor_get(v_impl_1293_, 3);
                                    lean_dec(v_unused_1376_);
                                    v_unused_1377_ = lean_ctor_get(v_impl_1293_, 2);
                                    lean_dec(v_unused_1377_);
                                    v_unused_1378_ = lean_ctor_get(v_impl_1293_, 1);
                                    lean_dec(v_unused_1378_);
                                    v_unused_1379_ = lean_ctor_get(v_impl_1293_, 0);
                                    lean_dec(v_unused_1379_);
                                    v___x_1310_ = v_impl_1293_;
                                    v_isShared_1311_ = v_isSharedCheck_1374_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1293_);
                                    v___x_1310_ = lean_box(0);
                                    v_isShared_1311_ = v_isSharedCheck_1374_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1380_ = lean_ctor_get(v_impl_1293_, 3);
                            lean_inc(v_l_1380_);
                            if lean_obj_tag(v_l_1380_) == 0 {
                                v_r_1381_ = lean_ctor_get(v_impl_1293_, 4);
                                v_k_1382_ = lean_ctor_get(v_impl_1293_, 1);
                                v_v_1383_ = lean_ctor_get(v_impl_1293_, 2);
                                v_isSharedCheck_1394_ = (!lean_is_exclusive(v_impl_1293_)) as u8;
                                if v_isSharedCheck_1394_ == 0 {
                                    v_unused_1395_ = lean_ctor_get(v_impl_1293_, 3);
                                    lean_dec(v_unused_1395_);
                                    v_unused_1396_ = lean_ctor_get(v_impl_1293_, 0);
                                    lean_dec(v_unused_1396_);
                                    v___x_1385_ = v_impl_1293_;
                                    v_isShared_1386_ = v_isSharedCheck_1394_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_1381_);
                                    lean_inc(v_v_1383_);
                                    lean_inc(v_k_1382_);
                                    lean_dec(v_impl_1293_);
                                    v___x_1385_ = lean_box(0);
                                    v_isShared_1386_ = v_isSharedCheck_1394_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1397_ = lean_ctor_get(v_impl_1293_, 4);
                                lean_inc(v_r_1397_);
                                if lean_obj_tag(v_r_1397_) == 0 {
                                    v_k_1398_ = lean_ctor_get(v_impl_1293_, 1);
                                    v_v_1399_ = lean_ctor_get(v_impl_1293_, 2);
                                    v_isSharedCheck_1422_ =
                                        (!lean_is_exclusive(v_impl_1293_)) as u8;
                                    if v_isSharedCheck_1422_ == 0 {
                                        v_unused_1423_ = lean_ctor_get(v_impl_1293_, 4);
                                        lean_dec(v_unused_1423_);
                                        v_unused_1424_ = lean_ctor_get(v_impl_1293_, 3);
                                        lean_dec(v_unused_1424_);
                                        v_unused_1425_ = lean_ctor_get(v_impl_1293_, 0);
                                        lean_dec(v_unused_1425_);
                                        v___x_1401_ = v_impl_1293_;
                                        v_isShared_1402_ = v_isSharedCheck_1422_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1399_);
                                        lean_inc(v_k_1398_);
                                        lean_dec(v_impl_1293_);
                                        v___x_1401_ = lean_box(0);
                                        v_isShared_1402_ = v_isSharedCheck_1422_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1426_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1290_ == 0 {
                                        lean_ctor_set(v___x_1289_, 4, v_r_1397_);
                                        lean_ctor_set(v___x_1289_, 3, v_impl_1293_);
                                        lean_ctor_set(v___x_1289_, 0, v___x_1426_);
                                        v___x_1428_ = v___x_1289_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
                                        lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_k_1284_);
                                        lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_v_1285_);
                                        lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_impl_1293_);
                                        lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_r_1397_);
                                        v___x_1428_ = v_reuseFailAlloc_1429_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_1285_);
                        lean_dec(v_k_1284_);
                        lean_dec_ref(v_cmp_1279_);
                        if v_isShared_1290_ == 0 {
                            lean_ctor_set(v___x_1289_, 2, v_v_1281_);
                            lean_ctor_set(v___x_1289_, 1, v_k_1280_);
                            v___x_1431_ = v___x_1289_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_size_1283_);
                            lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1280_);
                            lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1281_);
                            lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_l_1286_);
                            lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_r_1287_);
                            v___x_1431_ = v_reuseFailAlloc_1432_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_1283_);
                        v_impl_1433_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1279_, v_k_1280_, v_v_1281_, v_r_1287_);
                        v___x_1434_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_1286_) == 0 {
                            v_size_1435_ = lean_ctor_get(v_l_1286_, 0);
                            v_size_1436_ = lean_ctor_get(v_impl_1433_, 0);
                            lean_inc(v_size_1436_);
                            v_k_1437_ = lean_ctor_get(v_impl_1433_, 1);
                            lean_inc(v_k_1437_);
                            v_v_1438_ = lean_ctor_get(v_impl_1433_, 2);
                            lean_inc(v_v_1438_);
                            v_l_1439_ = lean_ctor_get(v_impl_1433_, 3);
                            lean_inc(v_l_1439_);
                            v_r_1440_ = lean_ctor_get(v_impl_1433_, 4);
                            lean_inc(v_r_1440_);
                            v___x_1441_ = lean_unsigned_to_nat(3);
                            v___x_1442_ = lean_nat_mul(v___x_1441_, v_size_1435_);
                            v___x_1443_ = lean_nat_dec_lt(v___x_1442_, v_size_1436_);
                            lean_dec(v___x_1442_);
                            if v___x_1443_ == 0 {
                                lean_dec(v_r_1440_);
                                lean_dec(v_l_1439_);
                                lean_dec(v_v_1438_);
                                lean_dec(v_k_1437_);
                                v___x_1444_ = lean_nat_add(v___x_1434_, v_size_1435_);
                                v___x_1445_ = lean_nat_add(v___x_1444_, v_size_1436_);
                                lean_dec(v_size_1436_);
                                lean_dec(v___x_1444_);
                                if v_isShared_1290_ == 0 {
                                    lean_ctor_set(v___x_1289_, 4, v_impl_1433_);
                                    lean_ctor_set(v___x_1289_, 0, v___x_1445_);
                                    v___x_1447_ = v___x_1289_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
                                    lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1284_);
                                    lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1285_);
                                    lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_l_1286_);
                                    lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_impl_1433_);
                                    v___x_1447_ = v_reuseFailAlloc_1448_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1512_ = (!lean_is_exclusive(v_impl_1433_)) as u8;
                                if v_isSharedCheck_1512_ == 0 {
                                    v_unused_1513_ = lean_ctor_get(v_impl_1433_, 4);
                                    lean_dec(v_unused_1513_);
                                    v_unused_1514_ = lean_ctor_get(v_impl_1433_, 3);
                                    lean_dec(v_unused_1514_);
                                    v_unused_1515_ = lean_ctor_get(v_impl_1433_, 2);
                                    lean_dec(v_unused_1515_);
                                    v_unused_1516_ = lean_ctor_get(v_impl_1433_, 1);
                                    lean_dec(v_unused_1516_);
                                    v_unused_1517_ = lean_ctor_get(v_impl_1433_, 0);
                                    lean_dec(v_unused_1517_);
                                    v___x_1450_ = v_impl_1433_;
                                    v_isShared_1451_ = v_isSharedCheck_1512_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1433_);
                                    v___x_1450_ = lean_box(0);
                                    v_isShared_1451_ = v_isSharedCheck_1512_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1518_ = lean_ctor_get(v_impl_1433_, 3);
                            lean_inc(v_l_1518_);
                            if lean_obj_tag(v_l_1518_) == 0 {
                                v_r_1519_ = lean_ctor_get(v_impl_1433_, 4);
                                v_k_1520_ = lean_ctor_get(v_impl_1433_, 1);
                                v_v_1521_ = lean_ctor_get(v_impl_1433_, 2);
                                v_isSharedCheck_1544_ = (!lean_is_exclusive(v_impl_1433_)) as u8;
                                if v_isSharedCheck_1544_ == 0 {
                                    v_unused_1545_ = lean_ctor_get(v_impl_1433_, 3);
                                    lean_dec(v_unused_1545_);
                                    v_unused_1546_ = lean_ctor_get(v_impl_1433_, 0);
                                    lean_dec(v_unused_1546_);
                                    v___x_1523_ = v_impl_1433_;
                                    v_isShared_1524_ = v_isSharedCheck_1544_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_1519_);
                                    lean_inc(v_v_1521_);
                                    lean_inc(v_k_1520_);
                                    lean_dec(v_impl_1433_);
                                    v___x_1523_ = lean_box(0);
                                    v_isShared_1524_ = v_isSharedCheck_1544_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1547_ = lean_ctor_get(v_impl_1433_, 4);
                                lean_inc(v_r_1547_);
                                if lean_obj_tag(v_r_1547_) == 0 {
                                    v_k_1548_ = lean_ctor_get(v_impl_1433_, 1);
                                    v_v_1549_ = lean_ctor_get(v_impl_1433_, 2);
                                    v_isSharedCheck_1560_ =
                                        (!lean_is_exclusive(v_impl_1433_)) as u8;
                                    if v_isSharedCheck_1560_ == 0 {
                                        v_unused_1561_ = lean_ctor_get(v_impl_1433_, 4);
                                        lean_dec(v_unused_1561_);
                                        v_unused_1562_ = lean_ctor_get(v_impl_1433_, 3);
                                        lean_dec(v_unused_1562_);
                                        v_unused_1563_ = lean_ctor_get(v_impl_1433_, 0);
                                        lean_dec(v_unused_1563_);
                                        v___x_1551_ = v_impl_1433_;
                                        v_isShared_1552_ = v_isSharedCheck_1560_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1549_);
                                        lean_inc(v_k_1548_);
                                        lean_dec(v_impl_1433_);
                                        v___x_1551_ = lean_box(0);
                                        v_isShared_1552_ = v_isSharedCheck_1560_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1564_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1290_ == 0 {
                                        lean_ctor_set(v___x_1289_, 4, v_impl_1433_);
                                        lean_ctor_set(v___x_1289_, 3, v_r_1547_);
                                        lean_ctor_set(v___x_1289_, 0, v___x_1564_);
                                        v___x_1566_ = v___x_1289_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
                                        lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1284_);
                                        lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1285_);
                                        lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_r_1547_);
                                        lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_impl_1433_);
                                        v___x_1566_ = v_reuseFailAlloc_1567_;
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
                return v___x_1307_;
            }
            3 => {
                v_size_1312_ = lean_ctor_get(v_l_1299_, 0);
                v_size_1313_ = lean_ctor_get(v_r_1300_, 0);
                v_k_1314_ = lean_ctor_get(v_r_1300_, 1);
                v_v_1315_ = lean_ctor_get(v_r_1300_, 2);
                v_l_1316_ = lean_ctor_get(v_r_1300_, 3);
                v_r_1317_ = lean_ctor_get(v_r_1300_, 4);
                v___x_1318_ = lean_unsigned_to_nat(2);
                v___x_1319_ = lean_nat_mul(v___x_1318_, v_size_1312_);
                v___x_1320_ = lean_nat_dec_lt(v_size_1313_, v___x_1319_);
                lean_dec(v___x_1319_);
                if v___x_1320_ == 0 {
                    lean_inc(v_r_1317_);
                    lean_inc(v_l_1316_);
                    lean_inc(v_v_1315_);
                    lean_inc(v_k_1314_);
                    v_isSharedCheck_1349_ = (!lean_is_exclusive(v_r_1300_)) as u8;
                    if v_isSharedCheck_1349_ == 0 {
                        v_unused_1350_ = lean_ctor_get(v_r_1300_, 4);
                        lean_dec(v_unused_1350_);
                        v_unused_1351_ = lean_ctor_get(v_r_1300_, 3);
                        lean_dec(v_unused_1351_);
                        v_unused_1352_ = lean_ctor_get(v_r_1300_, 2);
                        lean_dec(v_unused_1352_);
                        v_unused_1353_ = lean_ctor_get(v_r_1300_, 1);
                        lean_dec(v_unused_1353_);
                        v_unused_1354_ = lean_ctor_get(v_r_1300_, 0);
                        lean_dec(v_unused_1354_);
                        v___x_1322_ = v_r_1300_;
                        v_isShared_1323_ = v_isSharedCheck_1349_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_1300_);
                        v___x_1322_ = lean_box(0);
                        v_isShared_1323_ = v_isSharedCheck_1349_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1289_);
                    v___x_1355_ = lean_nat_add(v___x_1294_, v_size_1296_);
                    lean_dec(v_size_1296_);
                    v___x_1356_ = lean_nat_add(v___x_1355_, v_size_1295_);
                    lean_dec(v___x_1355_);
                    v___x_1357_ = lean_nat_add(v___x_1294_, v_size_1295_);
                    v___x_1358_ = lean_nat_add(v___x_1357_, v_size_1313_);
                    lean_dec(v___x_1357_);
                    lean_inc_ref(v_r_1287_);
                    if v_isShared_1311_ == 0 {
                        lean_ctor_set(v___x_1310_, 4, v_r_1287_);
                        lean_ctor_set(v___x_1310_, 3, v_r_1300_);
                        lean_ctor_set(v___x_1310_, 2, v_v_1285_);
                        lean_ctor_set(v___x_1310_, 1, v_k_1284_);
                        lean_ctor_set(v___x_1310_, 0, v___x_1358_);
                        v___x_1360_ = v___x_1310_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1358_);
                        lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1284_);
                        lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1285_);
                        lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_r_1300_);
                        lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1287_);
                        v___x_1360_ = v_reuseFailAlloc_1373_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1324_ = lean_nat_add(v___x_1294_, v_size_1296_);
                lean_dec(v_size_1296_);
                v___x_1325_ = lean_nat_add(v___x_1324_, v_size_1295_);
                lean_dec(v___x_1324_);
                v___x_1337_ = lean_nat_add(v___x_1294_, v_size_1312_);
                if lean_obj_tag(v_l_1316_) == 0 {
                    v_size_1347_ = lean_ctor_get(v_l_1316_, 0);
                    lean_inc(v_size_1347_);
                    v___y_1339_ = v_size_1347_;
                    state = 8;
                    continue;
                } else {
                    v___x_1348_ = lean_unsigned_to_nat(0);
                    v___y_1339_ = v___x_1348_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1330_ = lean_nat_add(v___y_1328_, v___y_1329_);
                lean_dec(v___y_1329_);
                lean_dec(v___y_1328_);
                if v_isShared_1323_ == 0 {
                    lean_ctor_set(v___x_1322_, 4, v_r_1287_);
                    lean_ctor_set(v___x_1322_, 3, v_r_1317_);
                    lean_ctor_set(v___x_1322_, 2, v_v_1285_);
                    lean_ctor_set(v___x_1322_, 1, v_k_1284_);
                    lean_ctor_set(v___x_1322_, 0, v___x_1330_);
                    v___x_1332_ = v___x_1322_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1330_);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1284_);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_r_1317_);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 4, v_r_1287_);
                    v___x_1332_ = v_reuseFailAlloc_1336_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1311_ == 0 {
                    lean_ctor_set(v___x_1310_, 4, v___x_1332_);
                    lean_ctor_set(v___x_1310_, 3, v___y_1327_);
                    lean_ctor_set(v___x_1310_, 2, v_v_1315_);
                    lean_ctor_set(v___x_1310_, 1, v_k_1314_);
                    lean_ctor_set(v___x_1310_, 0, v___x_1325_);
                    v___x_1334_ = v___x_1310_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1325_);
                    lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1314_);
                    lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1315_);
                    lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___y_1327_);
                    lean_ctor_set(v_reuseFailAlloc_1335_, 4, v___x_1332_);
                    v___x_1334_ = v_reuseFailAlloc_1335_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1334_;
            }
            8 => {
                v___x_1340_ = lean_nat_add(v___x_1337_, v___y_1339_);
                lean_dec(v___y_1339_);
                lean_dec(v___x_1337_);
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 4, v_l_1316_);
                    lean_ctor_set(v___x_1289_, 3, v_l_1299_);
                    lean_ctor_set(v___x_1289_, 2, v_v_1298_);
                    lean_ctor_set(v___x_1289_, 1, v_k_1297_);
                    lean_ctor_set(v___x_1289_, 0, v___x_1340_);
                    v___x_1342_ = v___x_1289_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1297_);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1298_);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_l_1299_);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_l_1316_);
                    v___x_1342_ = v_reuseFailAlloc_1346_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1343_ = lean_nat_add(v___x_1294_, v_size_1295_);
                if lean_obj_tag(v_r_1317_) == 0 {
                    v_size_1344_ = lean_ctor_get(v_r_1317_, 0);
                    lean_inc(v_size_1344_);
                    v___y_1327_ = v___x_1342_;
                    v___y_1328_ = v___x_1343_;
                    v___y_1329_ = v_size_1344_;
                    state = 5;
                    continue;
                } else {
                    v___x_1345_ = lean_unsigned_to_nat(0);
                    v___y_1327_ = v___x_1342_;
                    v___y_1328_ = v___x_1343_;
                    v___y_1329_ = v___x_1345_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1367_ = (!lean_is_exclusive(v_r_1287_)) as u8;
                if v_isSharedCheck_1367_ == 0 {
                    v_unused_1368_ = lean_ctor_get(v_r_1287_, 4);
                    lean_dec(v_unused_1368_);
                    v_unused_1369_ = lean_ctor_get(v_r_1287_, 3);
                    lean_dec(v_unused_1369_);
                    v_unused_1370_ = lean_ctor_get(v_r_1287_, 2);
                    lean_dec(v_unused_1370_);
                    v_unused_1371_ = lean_ctor_get(v_r_1287_, 1);
                    lean_dec(v_unused_1371_);
                    v_unused_1372_ = lean_ctor_get(v_r_1287_, 0);
                    lean_dec(v_unused_1372_);
                    v___x_1362_ = v_r_1287_;
                    v_isShared_1363_ = v_isSharedCheck_1367_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_1287_);
                    v___x_1362_ = lean_box(0);
                    v_isShared_1363_ = v_isSharedCheck_1367_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1363_ == 0 {
                    lean_ctor_set(v___x_1362_, 4, v___x_1360_);
                    lean_ctor_set(v___x_1362_, 3, v_l_1299_);
                    lean_ctor_set(v___x_1362_, 2, v_v_1298_);
                    lean_ctor_set(v___x_1362_, 1, v_k_1297_);
                    lean_ctor_set(v___x_1362_, 0, v___x_1356_);
                    v___x_1365_ = v___x_1362_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1356_);
                    lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1297_);
                    lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1298_);
                    lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_l_1299_);
                    lean_ctor_set(v_reuseFailAlloc_1366_, 4, v___x_1360_);
                    v___x_1365_ = v_reuseFailAlloc_1366_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1365_;
            }
            13 => {
                v___x_1387_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_1381_);
                if v_isShared_1386_ == 0 {
                    lean_ctor_set(v___x_1385_, 3, v_r_1381_);
                    lean_ctor_set(v___x_1385_, 2, v_v_1285_);
                    lean_ctor_set(v___x_1385_, 1, v_k_1284_);
                    lean_ctor_set(v___x_1385_, 0, v___x_1294_);
                    v___x_1389_ = v___x_1385_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1294_);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1284_);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_r_1381_);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_r_1381_);
                    v___x_1389_ = v_reuseFailAlloc_1393_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 4, v___x_1389_);
                    lean_ctor_set(v___x_1289_, 3, v_l_1380_);
                    lean_ctor_set(v___x_1289_, 2, v_v_1383_);
                    lean_ctor_set(v___x_1289_, 1, v_k_1382_);
                    lean_ctor_set(v___x_1289_, 0, v___x_1387_);
                    v___x_1391_ = v___x_1289_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1387_);
                    lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1382_);
                    lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1383_);
                    lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_l_1380_);
                    lean_ctor_set(v_reuseFailAlloc_1392_, 4, v___x_1389_);
                    v___x_1391_ = v_reuseFailAlloc_1392_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1391_;
            }
            16 => {
                v_k_1403_ = lean_ctor_get(v_r_1397_, 1);
                v_v_1404_ = lean_ctor_get(v_r_1397_, 2);
                v_isSharedCheck_1418_ = (!lean_is_exclusive(v_r_1397_)) as u8;
                if v_isSharedCheck_1418_ == 0 {
                    v_unused_1419_ = lean_ctor_get(v_r_1397_, 4);
                    lean_dec(v_unused_1419_);
                    v_unused_1420_ = lean_ctor_get(v_r_1397_, 3);
                    lean_dec(v_unused_1420_);
                    v_unused_1421_ = lean_ctor_get(v_r_1397_, 0);
                    lean_dec(v_unused_1421_);
                    v___x_1406_ = v_r_1397_;
                    v_isShared_1407_ = v_isSharedCheck_1418_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_1404_);
                    lean_inc(v_k_1403_);
                    lean_dec(v_r_1397_);
                    v___x_1406_ = lean_box(0);
                    v_isShared_1407_ = v_isSharedCheck_1418_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1408_ = lean_unsigned_to_nat(3);
                if v_isShared_1407_ == 0 {
                    lean_ctor_set(v___x_1406_, 4, v_l_1380_);
                    lean_ctor_set(v___x_1406_, 3, v_l_1380_);
                    lean_ctor_set(v___x_1406_, 2, v_v_1399_);
                    lean_ctor_set(v___x_1406_, 1, v_k_1398_);
                    lean_ctor_set(v___x_1406_, 0, v___x_1294_);
                    v___x_1410_ = v___x_1406_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1294_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1398_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1399_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1380_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1380_);
                    v___x_1410_ = v_reuseFailAlloc_1417_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1402_ == 0 {
                    lean_ctor_set(v___x_1401_, 4, v_l_1380_);
                    lean_ctor_set(v___x_1401_, 2, v_v_1285_);
                    lean_ctor_set(v___x_1401_, 1, v_k_1284_);
                    lean_ctor_set(v___x_1401_, 0, v___x_1294_);
                    v___x_1412_ = v___x_1401_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1294_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1284_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_l_1380_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_l_1380_);
                    v___x_1412_ = v_reuseFailAlloc_1416_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 4, v___x_1412_);
                    lean_ctor_set(v___x_1289_, 3, v___x_1410_);
                    lean_ctor_set(v___x_1289_, 2, v_v_1404_);
                    lean_ctor_set(v___x_1289_, 1, v_k_1403_);
                    lean_ctor_set(v___x_1289_, 0, v___x_1408_);
                    v___x_1414_ = v___x_1289_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1408_);
                    lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1403_);
                    lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1404_);
                    lean_ctor_set(v_reuseFailAlloc_1415_, 3, v___x_1410_);
                    lean_ctor_set(v_reuseFailAlloc_1415_, 4, v___x_1412_);
                    v___x_1414_ = v_reuseFailAlloc_1415_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1414_;
            }
            21 => {
                return v___x_1428_;
            }
            22 => {
                return v___x_1431_;
            }
            23 => {
                return v___x_1447_;
            }
            24 => {
                v_size_1452_ = lean_ctor_get(v_l_1439_, 0);
                v_k_1453_ = lean_ctor_get(v_l_1439_, 1);
                v_v_1454_ = lean_ctor_get(v_l_1439_, 2);
                v_l_1455_ = lean_ctor_get(v_l_1439_, 3);
                v_r_1456_ = lean_ctor_get(v_l_1439_, 4);
                v_size_1457_ = lean_ctor_get(v_r_1440_, 0);
                v___x_1458_ = lean_unsigned_to_nat(2);
                v___x_1459_ = lean_nat_mul(v___x_1458_, v_size_1457_);
                v___x_1460_ = lean_nat_dec_lt(v_size_1452_, v___x_1459_);
                lean_dec(v___x_1459_);
                if v___x_1460_ == 0 {
                    lean_inc(v_r_1456_);
                    lean_inc(v_l_1455_);
                    lean_inc(v_v_1454_);
                    lean_inc(v_k_1453_);
                    v_isSharedCheck_1488_ = (!lean_is_exclusive(v_l_1439_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v_unused_1489_ = lean_ctor_get(v_l_1439_, 4);
                        lean_dec(v_unused_1489_);
                        v_unused_1490_ = lean_ctor_get(v_l_1439_, 3);
                        lean_dec(v_unused_1490_);
                        v_unused_1491_ = lean_ctor_get(v_l_1439_, 2);
                        lean_dec(v_unused_1491_);
                        v_unused_1492_ = lean_ctor_get(v_l_1439_, 1);
                        lean_dec(v_unused_1492_);
                        v_unused_1493_ = lean_ctor_get(v_l_1439_, 0);
                        lean_dec(v_unused_1493_);
                        v___x_1462_ = v_l_1439_;
                        v_isShared_1463_ = v_isSharedCheck_1488_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_1439_);
                        v___x_1462_ = lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1488_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1289_);
                    v___x_1494_ = lean_nat_add(v___x_1434_, v_size_1435_);
                    v___x_1495_ = lean_nat_add(v___x_1494_, v_size_1436_);
                    lean_dec(v_size_1436_);
                    v___x_1496_ = lean_nat_add(v___x_1494_, v_size_1452_);
                    lean_dec(v___x_1494_);
                    lean_inc_ref(v_l_1286_);
                    if v_isShared_1451_ == 0 {
                        lean_ctor_set(v___x_1450_, 4, v_l_1439_);
                        lean_ctor_set(v___x_1450_, 3, v_l_1286_);
                        lean_ctor_set(v___x_1450_, 2, v_v_1285_);
                        lean_ctor_set(v___x_1450_, 1, v_k_1284_);
                        lean_ctor_set(v___x_1450_, 0, v___x_1496_);
                        v___x_1498_ = v___x_1450_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1496_);
                        lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1284_);
                        lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1285_);
                        lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_l_1286_);
                        lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_l_1439_);
                        v___x_1498_ = v_reuseFailAlloc_1511_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1464_ = lean_nat_add(v___x_1434_, v_size_1435_);
                v___x_1465_ = lean_nat_add(v___x_1464_, v_size_1436_);
                lean_dec(v_size_1436_);
                if lean_obj_tag(v_l_1455_) == 0 {
                    v_size_1486_ = lean_ctor_get(v_l_1455_, 0);
                    lean_inc(v_size_1486_);
                    v___y_1478_ = v_size_1486_;
                    state = 29;
                    continue;
                } else {
                    v___x_1487_ = lean_unsigned_to_nat(0);
                    v___y_1478_ = v___x_1487_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1470_ = lean_nat_add(v___y_1467_, v___y_1469_);
                lean_dec(v___y_1469_);
                lean_dec(v___y_1467_);
                if v_isShared_1463_ == 0 {
                    lean_ctor_set(v___x_1462_, 4, v_r_1440_);
                    lean_ctor_set(v___x_1462_, 3, v_r_1456_);
                    lean_ctor_set(v___x_1462_, 2, v_v_1438_);
                    lean_ctor_set(v___x_1462_, 1, v_k_1437_);
                    lean_ctor_set(v___x_1462_, 0, v___x_1470_);
                    v___x_1472_ = v___x_1462_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1470_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1437_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1438_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_r_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_r_1440_);
                    v___x_1472_ = v_reuseFailAlloc_1476_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1451_ == 0 {
                    lean_ctor_set(v___x_1450_, 4, v___x_1472_);
                    lean_ctor_set(v___x_1450_, 3, v___y_1468_);
                    lean_ctor_set(v___x_1450_, 2, v_v_1454_);
                    lean_ctor_set(v___x_1450_, 1, v_k_1453_);
                    lean_ctor_set(v___x_1450_, 0, v___x_1465_);
                    v___x_1474_ = v___x_1450_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1465_);
                    lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1453_);
                    lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1475_, 3, v___y_1468_);
                    lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1472_);
                    v___x_1474_ = v_reuseFailAlloc_1475_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1474_;
            }
            29 => {
                v___x_1479_ = lean_nat_add(v___x_1464_, v___y_1478_);
                lean_dec(v___y_1478_);
                lean_dec(v___x_1464_);
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 4, v_l_1455_);
                    lean_ctor_set(v___x_1289_, 0, v___x_1479_);
                    v___x_1481_ = v___x_1289_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1284_);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_l_1286_);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_l_1455_);
                    v___x_1481_ = v_reuseFailAlloc_1485_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1482_ = lean_nat_add(v___x_1434_, v_size_1457_);
                if lean_obj_tag(v_r_1456_) == 0 {
                    v_size_1483_ = lean_ctor_get(v_r_1456_, 0);
                    lean_inc(v_size_1483_);
                    v___y_1467_ = v___x_1482_;
                    v___y_1468_ = v___x_1481_;
                    v___y_1469_ = v_size_1483_;
                    state = 26;
                    continue;
                } else {
                    v___x_1484_ = lean_unsigned_to_nat(0);
                    v___y_1467_ = v___x_1482_;
                    v___y_1468_ = v___x_1481_;
                    v___y_1469_ = v___x_1484_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1505_ = (!lean_is_exclusive(v_l_1286_)) as u8;
                if v_isSharedCheck_1505_ == 0 {
                    v_unused_1506_ = lean_ctor_get(v_l_1286_, 4);
                    lean_dec(v_unused_1506_);
                    v_unused_1507_ = lean_ctor_get(v_l_1286_, 3);
                    lean_dec(v_unused_1507_);
                    v_unused_1508_ = lean_ctor_get(v_l_1286_, 2);
                    lean_dec(v_unused_1508_);
                    v_unused_1509_ = lean_ctor_get(v_l_1286_, 1);
                    lean_dec(v_unused_1509_);
                    v_unused_1510_ = lean_ctor_get(v_l_1286_, 0);
                    lean_dec(v_unused_1510_);
                    v___x_1500_ = v_l_1286_;
                    v_isShared_1501_ = v_isSharedCheck_1505_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_1286_);
                    v___x_1500_ = lean_box(0);
                    v_isShared_1501_ = v_isSharedCheck_1505_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1501_ == 0 {
                    lean_ctor_set(v___x_1500_, 4, v_r_1440_);
                    lean_ctor_set(v___x_1500_, 3, v___x_1498_);
                    lean_ctor_set(v___x_1500_, 2, v_v_1438_);
                    lean_ctor_set(v___x_1500_, 1, v_k_1437_);
                    lean_ctor_set(v___x_1500_, 0, v___x_1495_);
                    v___x_1503_ = v___x_1500_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1495_);
                    lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1437_);
                    lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1438_);
                    lean_ctor_set(v_reuseFailAlloc_1504_, 3, v___x_1498_);
                    lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_r_1440_);
                    v___x_1503_ = v_reuseFailAlloc_1504_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1503_;
            }
            34 => {
                v_k_1525_ = lean_ctor_get(v_l_1518_, 1);
                v_v_1526_ = lean_ctor_get(v_l_1518_, 2);
                v_isSharedCheck_1540_ = (!lean_is_exclusive(v_l_1518_)) as u8;
                if v_isSharedCheck_1540_ == 0 {
                    v_unused_1541_ = lean_ctor_get(v_l_1518_, 4);
                    lean_dec(v_unused_1541_);
                    v_unused_1542_ = lean_ctor_get(v_l_1518_, 3);
                    lean_dec(v_unused_1542_);
                    v_unused_1543_ = lean_ctor_get(v_l_1518_, 0);
                    lean_dec(v_unused_1543_);
                    v___x_1528_ = v_l_1518_;
                    v_isShared_1529_ = v_isSharedCheck_1540_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_1526_);
                    lean_inc(v_k_1525_);
                    lean_dec(v_l_1518_);
                    v___x_1528_ = lean_box(0);
                    v_isShared_1529_ = v_isSharedCheck_1540_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1530_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_1519_, 2);
                if v_isShared_1529_ == 0 {
                    lean_ctor_set(v___x_1528_, 4, v_r_1519_);
                    lean_ctor_set(v___x_1528_, 3, v_r_1519_);
                    lean_ctor_set(v___x_1528_, 2, v_v_1285_);
                    lean_ctor_set(v___x_1528_, 1, v_k_1284_);
                    lean_ctor_set(v___x_1528_, 0, v___x_1434_);
                    v___x_1532_ = v___x_1528_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1434_);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1284_);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_r_1519_);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1519_);
                    v___x_1532_ = v_reuseFailAlloc_1539_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_1519_);
                if v_isShared_1524_ == 0 {
                    lean_ctor_set(v___x_1523_, 3, v_r_1519_);
                    lean_ctor_set(v___x_1523_, 0, v___x_1434_);
                    v___x_1534_ = v___x_1523_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1434_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1520_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1521_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_r_1519_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_r_1519_);
                    v___x_1534_ = v_reuseFailAlloc_1538_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 4, v___x_1534_);
                    lean_ctor_set(v___x_1289_, 3, v___x_1532_);
                    lean_ctor_set(v___x_1289_, 2, v_v_1526_);
                    lean_ctor_set(v___x_1289_, 1, v_k_1525_);
                    lean_ctor_set(v___x_1289_, 0, v___x_1530_);
                    v___x_1536_ = v___x_1289_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1530_);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1525_);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1526_);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 3, v___x_1532_);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 4, v___x_1534_);
                    v___x_1536_ = v_reuseFailAlloc_1537_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1536_;
            }
            39 => {
                v___x_1553_ = lean_unsigned_to_nat(3);
                if v_isShared_1552_ == 0 {
                    lean_ctor_set(v___x_1551_, 4, v_l_1518_);
                    lean_ctor_set(v___x_1551_, 2, v_v_1285_);
                    lean_ctor_set(v___x_1551_, 1, v_k_1284_);
                    lean_ctor_set(v___x_1551_, 0, v___x_1434_);
                    v___x_1555_ = v___x_1551_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1434_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1284_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_l_1518_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_l_1518_);
                    v___x_1555_ = v_reuseFailAlloc_1559_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 4, v_r_1547_);
                    lean_ctor_set(v___x_1289_, 3, v___x_1555_);
                    lean_ctor_set(v___x_1289_, 2, v_v_1549_);
                    lean_ctor_set(v___x_1289_, 1, v_k_1548_);
                    lean_ctor_set(v___x_1289_, 0, v___x_1553_);
                    v___x_1557_ = v___x_1289_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1553_);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1548_);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1549_);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 3, v___x_1555_);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1547_);
                    v___x_1557_ = v_reuseFailAlloc_1558_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1557_;
            }
            42 => {
                return v___x_1566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(
    mut v_items_1571_: *mut LeanObject,
    mut v_cmp_1572_: *mut LeanObject,
    mut v_n_1573_: *mut LeanObject,
    mut v_j_1574_: *mut LeanObject,
    mut v_a_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1577_: u8 = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1576_ = lean_unsigned_to_nat(0);
                v_isZero_1577_ = lean_nat_dec_eq(v_j_1574_, v_zero_1576_);
                if v_isZero_1577_ == 1 {
                    lean_dec(v_j_1574_);
                    lean_dec_ref(v_cmp_1572_);
                    return v_a_1575_;
                } else {
                    v___x_1578_ = lean_nat_sub(v_n_1573_, v_j_1574_);
                    v___x_1579_ = lean_array_fget_borrowed(v_items_1571_, v___x_1578_);
                    v_fst_1580_ = lean_ctor_get(v___x_1579_, 0);
                    v_one_1581_ = lean_unsigned_to_nat(1);
                    v_n_1582_ = lean_nat_sub(v_j_1574_, v_one_1581_);
                    lean_dec(v_j_1574_);
                    lean_inc(v_fst_1580_);
                    lean_inc_ref(v_cmp_1572_);
                    v___x_1583_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1572_, v_fst_1580_, v___x_1578_, v_a_1575_);
                    v_j_1574_ = v_n_1582_;
                    v_a_1575_ = v___x_1583_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg___boxed(
    mut v_items_1585_: *mut LeanObject,
    mut v_cmp_1586_: *mut LeanObject,
    mut v_n_1587_: *mut LeanObject,
    mut v_j_1588_: *mut LeanObject,
    mut v_a_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1590_: *mut LeanObject = core::ptr::null_mut();
    v_res_1590_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1585_, v_cmp_1586_, v_n_1587_, v_j_1588_, v_a_1589_);
    lean_dec(v_n_1587_);
    lean_dec_ref(v_items_1585_);
    return v_res_1590_;
}
pub unsafe fn l_Lake_Toml_RBDict_ofArray___redArg(
    mut v_cmp_1591_: *mut LeanObject,
    mut v_items_1592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_array_get_size(v_items_1592_);
    v___x_1594_ = lean_box(1);
    v_indices_1595_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1592_, v_cmp_1591_, v___x_1593_, v___x_1593_, v___x_1594_);
    v___x_1596_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1596_, 0, v_items_1592_);
    lean_ctor_set(v___x_1596_, 1, v_indices_1595_);
    return v___x_1596_;
}
pub unsafe fn l_Lake_Toml_RBDict_ofArray(
    mut v_00_u03b1_1597_: *mut LeanObject,
    mut v_00_u03b2_1598_: *mut LeanObject,
    mut v_cmp_1599_: *mut LeanObject,
    mut v_items_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lake_Toml_RBDict_ofArray___redArg(v_cmp_1599_, v_items_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0(
    mut v_00_u03b1_1602_: *mut LeanObject,
    mut v_cmp_1603_: *mut LeanObject,
    mut v_00_u03b2_1604_: *mut LeanObject,
    mut v_k_1605_: *mut LeanObject,
    mut v_v_1606_: *mut LeanObject,
    mut v_t_1607_: *mut LeanObject,
    mut v_hl_1608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    v___x_1609_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(
            v_cmp_1603_,
            v_k_1605_,
            v_v_1606_,
            v_t_1607_,
        );
    return v___x_1609_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(
    mut v_00_u03b1_1610_: *mut LeanObject,
    mut v_00_u03b2_1611_: *mut LeanObject,
    mut v_items_1612_: *mut LeanObject,
    mut v_cmp_1613_: *mut LeanObject,
    mut v_n_1614_: *mut LeanObject,
    mut v_j_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1612_, v_cmp_1613_, v_n_1614_, v_j_1615_, v_a_1617_);
    return v___x_1618_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___boxed(
    mut v_00_u03b1_1619_: *mut LeanObject,
    mut v_00_u03b2_1620_: *mut LeanObject,
    mut v_items_1621_: *mut LeanObject,
    mut v_cmp_1622_: *mut LeanObject,
    mut v_n_1623_: *mut LeanObject,
    mut v_j_1624_: *mut LeanObject,
    mut v_a_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1627_: *mut LeanObject = core::ptr::null_mut();
    v_res_1627_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(
            v_00_u03b1_1619_,
            v_00_u03b2_1620_,
            v_items_1621_,
            v_cmp_1622_,
            v_n_1623_,
            v_j_1624_,
            v_a_1625_,
            v_a_1626_,
        );
    lean_dec(v_n_1623_);
    lean_dec_ref(v_items_1621_);
    return v_res_1627_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___redArg(
    mut v_inst_1628_: *mut LeanObject,
    mut v_self_1629_: *mut LeanObject,
    mut v_other_1630_: *mut LeanObject,
) -> u8 {
    let mut v_items_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    v_items_1631_ = lean_ctor_get(v_self_1629_, 0);
    v_items_1632_ = lean_ctor_get(v_other_1630_, 0);
    v___x_1633_ = lean_array_get_size(v_items_1631_);
    v___x_1634_ = lean_array_get_size(v_items_1632_);
    v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
    if v___x_1635_ == 0 {
        lean_dec_ref(v_inst_1628_);
        return v___x_1635_;
    } else {
        let mut v___x_1636_: u8 = 0;
        v___x_1636_ =
            l_Array_isEqvAux___redArg(v_items_1631_, v_items_1632_, v_inst_1628_, v___x_1633_);
        return v___x_1636_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_beq___redArg___boxed(
    mut v_inst_1637_: *mut LeanObject,
    mut v_self_1638_: *mut LeanObject,
    mut v_other_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1640_: u8 = 0;
    let mut v_r_1641_: *mut LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_1637_, v_self_1638_, v_other_1639_);
    lean_dec_ref(v_other_1639_);
    lean_dec_ref(v_self_1638_);
    v_r_1641_ = lean_box((v_res_1640_) as usize);
    return v_r_1641_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq(
    mut v_00_u03b1_1642_: *mut LeanObject,
    mut v_00_u03b2_1643_: *mut LeanObject,
    mut v_cmp_1644_: *mut LeanObject,
    mut v_inst_1645_: *mut LeanObject,
    mut v_self_1646_: *mut LeanObject,
    mut v_other_1647_: *mut LeanObject,
) -> u8 {
    let mut v___x_1648_: u8 = 0;
    v___x_1648_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_1645_, v_self_1646_, v_other_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___boxed(
    mut v_00_u03b1_1649_: *mut LeanObject,
    mut v_00_u03b2_1650_: *mut LeanObject,
    mut v_cmp_1651_: *mut LeanObject,
    mut v_inst_1652_: *mut LeanObject,
    mut v_self_1653_: *mut LeanObject,
    mut v_other_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1655_: u8 = 0;
    let mut v_r_1656_: *mut LeanObject = core::ptr::null_mut();
    v_res_1655_ = l_Lake_Toml_RBDict_beq(
        v_00_u03b1_1649_,
        v_00_u03b2_1650_,
        v_cmp_1651_,
        v_inst_1652_,
        v_self_1653_,
        v_other_1654_,
    );
    lean_dec_ref(v_other_1654_);
    lean_dec_ref(v_self_1653_);
    lean_dec_ref(v_cmp_1651_);
    v_r_1656_ = lean_box((v_res_1655_) as usize);
    return v_r_1656_;
}
pub unsafe fn l_Lake_Toml_RBDict_instBEqOfProd___redArg(
    mut v_cmp_1657_: *mut LeanObject,
    mut v_inst_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_alloc_closure(
        l_Lake_Toml_RBDict_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___x_1659_, 0, lean_box(0));
    lean_closure_set(v___x_1659_, 1, lean_box(0));
    lean_closure_set(v___x_1659_, 2, v_cmp_1657_);
    lean_closure_set(v___x_1659_, 3, v_inst_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Lake_Toml_RBDict_instBEqOfProd(
    mut v_00_u03b1_1660_: *mut LeanObject,
    mut v_00_u03b2_1661_: *mut LeanObject,
    mut v_cmp_1662_: *mut LeanObject,
    mut v_inst_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1664_ = lean_alloc_closure(
        l_Lake_Toml_RBDict_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___x_1664_, 0, lean_box(0));
    lean_closure_set(v___x_1664_, 1, lean_box(0));
    lean_closure_set(v___x_1664_, 2, v_cmp_1662_);
    lean_closure_set(v___x_1664_, 3, v_inst_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___redArg(mut v_t_1665_: *mut LeanObject) -> *mut LeanObject {
    let mut v_items_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v_items_1666_ = lean_ctor_get(v_t_1665_, 0);
    v___x_1667_ = lean_array_get_size(v_items_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___redArg___boxed(
    mut v_t_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1669_: *mut LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_Lake_Toml_RBDict_size___redArg(v_t_1668_);
    lean_dec_ref(v_t_1668_);
    return v_res_1669_;
}
pub unsafe fn l_Lake_Toml_RBDict_size(
    mut v_00_u03b1_1670_: *mut LeanObject,
    mut v_00_u03b2_1671_: *mut LeanObject,
    mut v_cmp_1672_: *mut LeanObject,
    mut v_t_1673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    v_items_1674_ = lean_ctor_get(v_t_1673_, 0);
    v___x_1675_ = lean_array_get_size(v_items_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___boxed(
    mut v_00_u03b1_1676_: *mut LeanObject,
    mut v_00_u03b2_1677_: *mut LeanObject,
    mut v_cmp_1678_: *mut LeanObject,
    mut v_t_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1680_: *mut LeanObject = core::ptr::null_mut();
    v_res_1680_ =
        l_Lake_Toml_RBDict_size(v_00_u03b1_1676_, v_00_u03b2_1677_, v_cmp_1678_, v_t_1679_);
    lean_dec_ref(v_t_1679_);
    lean_dec_ref(v_cmp_1678_);
    return v_res_1680_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___redArg(mut v_t_1681_: *mut LeanObject) -> u8 {
    let mut v_items_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v_items_1682_ = lean_ctor_get(v_t_1681_, 0);
    v___x_1683_ = lean_array_get_size(v_items_1682_);
    v___x_1684_ = lean_unsigned_to_nat(0);
    v___x_1685_ = lean_nat_dec_eq(v___x_1683_, v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___redArg___boxed(
    mut v_t_1686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1687_: u8 = 0;
    let mut v_r_1688_: *mut LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lake_Toml_RBDict_isEmpty___redArg(v_t_1686_);
    lean_dec_ref(v_t_1686_);
    v_r_1688_ = lean_box((v_res_1687_) as usize);
    return v_r_1688_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty(
    mut v_00_u03b1_1689_: *mut LeanObject,
    mut v_00_u03b2_1690_: *mut LeanObject,
    mut v_cmp_1691_: *mut LeanObject,
    mut v_t_1692_: *mut LeanObject,
) -> u8 {
    let mut v_items_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    v_items_1693_ = lean_ctor_get(v_t_1692_, 0);
    v___x_1694_ = lean_array_get_size(v_items_1693_);
    v___x_1695_ = lean_unsigned_to_nat(0);
    v___x_1696_ = lean_nat_dec_eq(v___x_1694_, v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___boxed(
    mut v_00_u03b1_1697_: *mut LeanObject,
    mut v_00_u03b2_1698_: *mut LeanObject,
    mut v_cmp_1699_: *mut LeanObject,
    mut v_t_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1701_: u8 = 0;
    let mut v_r_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1701_ =
        l_Lake_Toml_RBDict_isEmpty(v_00_u03b1_1697_, v_00_u03b2_1698_, v_cmp_1699_, v_t_1700_);
    lean_dec_ref(v_t_1700_);
    lean_dec_ref(v_cmp_1699_);
    v_r_1702_ = lean_box((v_res_1701_) as usize);
    return v_r_1702_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(
    mut v_sz_1703_: usize,
    mut v_i_1704_: usize,
    mut v_bs_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: u8 = 0;
    let mut v_v_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: usize = 0;
    let mut v___x_1712_: usize = 0;
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1706_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
                if v___x_1706_ == 0 {
                    return v_bs_1705_;
                } else {
                    v_v_1707_ = lean_array_uget_borrowed(v_bs_1705_, v_i_1704_);
                    v_fst_1708_ = lean_ctor_get(v_v_1707_, 0);
                    lean_inc(v_fst_1708_);
                    v___x_1709_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1710_ = lean_array_uset(v_bs_1705_, v_i_1704_, v___x_1709_);
                    v___x_1711_ = 1usize;
                    v___x_1712_ = lean_usize_add(v_i_1704_, v___x_1711_);
                    v___x_1713_ = lean_array_uset(v_bs_x27_1710_, v_i_1704_, v_fst_1708_);
                    v_i_1704_ = v___x_1712_;
                    v_bs_1705_ = v___x_1713_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg___boxed(
    mut v_sz_1715_: *mut LeanObject,
    mut v_i_1716_: *mut LeanObject,
    mut v_bs_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1718_: usize = 0;
    let mut v_i_boxed_1719_: usize = 0;
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1715_);
    lean_dec(v_sz_1715_);
    v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
    lean_dec(v_i_1716_);
    v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
    return v_res_1720_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys___redArg(mut v_t_1721_: *mut LeanObject) -> *mut LeanObject {
    let mut v_items_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1723_: usize = 0;
    let mut v___x_1724_: usize = 0;
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v_items_1722_ = lean_ctor_get(v_t_1721_, 0);
    lean_inc_ref(v_items_1722_);
    lean_dec_ref(v_t_1721_);
    v_sz_1723_ = lean_array_size(v_items_1722_);
    v___x_1724_ = 0usize;
    v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_1723_, v___x_1724_, v_items_1722_);
    return v___x_1725_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys(
    mut v_00_u03b1_1726_: *mut LeanObject,
    mut v_00_u03b2_1727_: *mut LeanObject,
    mut v_cmp_1728_: *mut LeanObject,
    mut v_t_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Lake_Toml_RBDict_keys___redArg(v_t_1729_);
    return v___x_1730_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys___boxed(
    mut v_00_u03b1_1731_: *mut LeanObject,
    mut v_00_u03b2_1732_: *mut LeanObject,
    mut v_cmp_1733_: *mut LeanObject,
    mut v_t_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1735_: *mut LeanObject = core::ptr::null_mut();
    v_res_1735_ =
        l_Lake_Toml_RBDict_keys(v_00_u03b1_1731_, v_00_u03b2_1732_, v_cmp_1733_, v_t_1734_);
    lean_dec_ref(v_cmp_1733_);
    return v_res_1735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(
    mut v_00_u03b1_1736_: *mut LeanObject,
    mut v_00_u03b2_1737_: *mut LeanObject,
    mut v_sz_1738_: usize,
    mut v_i_1739_: usize,
    mut v_bs_1740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_1738_, v_i_1739_, v_bs_1740_);
    return v___x_1741_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___boxed(
    mut v_00_u03b1_1742_: *mut LeanObject,
    mut v_00_u03b2_1743_: *mut LeanObject,
    mut v_sz_1744_: *mut LeanObject,
    mut v_i_1745_: *mut LeanObject,
    mut v_bs_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1747_: usize = 0;
    let mut v_i_boxed_1748_: usize = 0;
    let mut v_res_1749_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1747_ = lean_unbox_usize(v_sz_1744_);
    lean_dec(v_sz_1744_);
    v_i_boxed_1748_ = lean_unbox_usize(v_i_1745_);
    lean_dec(v_i_1745_);
    v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(v_00_u03b1_1742_, v_00_u03b2_1743_, v_sz_boxed_1747_, v_i_boxed_1748_, v_bs_1746_);
    return v_res_1749_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(
    mut v_sz_1750_: usize,
    mut v_i_1751_: usize,
    mut v_bs_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1753_: u8 = 0;
    let mut v_v_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1753_ = lean_usize_dec_lt(v_i_1751_, v_sz_1750_);
                if v___x_1753_ == 0 {
                    return v_bs_1752_;
                } else {
                    v_v_1754_ = lean_array_uget_borrowed(v_bs_1752_, v_i_1751_);
                    v_snd_1755_ = lean_ctor_get(v_v_1754_, 1);
                    lean_inc(v_snd_1755_);
                    v___x_1756_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1757_ = lean_array_uset(v_bs_1752_, v_i_1751_, v___x_1756_);
                    v___x_1758_ = 1usize;
                    v___x_1759_ = lean_usize_add(v_i_1751_, v___x_1758_);
                    v___x_1760_ = lean_array_uset(v_bs_x27_1757_, v_i_1751_, v_snd_1755_);
                    v_i_1751_ = v___x_1759_;
                    v_bs_1752_ = v___x_1760_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg___boxed(
    mut v_sz_1762_: *mut LeanObject,
    mut v_i_1763_: *mut LeanObject,
    mut v_bs_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1765_: usize = 0;
    let mut v_i_boxed_1766_: usize = 0;
    let mut v_res_1767_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1762_);
    lean_dec(v_sz_1762_);
    v_i_boxed_1766_ = lean_unbox_usize(v_i_1763_);
    lean_dec(v_i_1763_);
    v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_boxed_1765_, v_i_boxed_1766_, v_bs_1764_);
    return v_res_1767_;
}
pub unsafe fn l_Lake_Toml_RBDict_values___redArg(
    mut v_t_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1770_: usize = 0;
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    v_items_1769_ = lean_ctor_get(v_t_1768_, 0);
    lean_inc_ref(v_items_1769_);
    lean_dec_ref(v_t_1768_);
    v_sz_1770_ = lean_array_size(v_items_1769_);
    v___x_1771_ = 0usize;
    v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_1770_, v___x_1771_, v_items_1769_);
    return v___x_1772_;
}
pub unsafe fn l_Lake_Toml_RBDict_values(
    mut v_00_u03b1_1773_: *mut LeanObject,
    mut v_00_u03b2_1774_: *mut LeanObject,
    mut v_cmp_1775_: *mut LeanObject,
    mut v_t_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lake_Toml_RBDict_values___redArg(v_t_1776_);
    return v___x_1777_;
}
pub unsafe fn l_Lake_Toml_RBDict_values___boxed(
    mut v_00_u03b1_1778_: *mut LeanObject,
    mut v_00_u03b2_1779_: *mut LeanObject,
    mut v_cmp_1780_: *mut LeanObject,
    mut v_t_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1782_: *mut LeanObject = core::ptr::null_mut();
    v_res_1782_ =
        l_Lake_Toml_RBDict_values(v_00_u03b1_1778_, v_00_u03b2_1779_, v_cmp_1780_, v_t_1781_);
    lean_dec_ref(v_cmp_1780_);
    return v_res_1782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(
    mut v_00_u03b1_1783_: *mut LeanObject,
    mut v_00_u03b2_1784_: *mut LeanObject,
    mut v_sz_1785_: usize,
    mut v_i_1786_: usize,
    mut v_bs_1787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_1785_, v_i_1786_, v_bs_1787_);
    return v___x_1788_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___boxed(
    mut v_00_u03b1_1789_: *mut LeanObject,
    mut v_00_u03b2_1790_: *mut LeanObject,
    mut v_sz_1791_: *mut LeanObject,
    mut v_i_1792_: *mut LeanObject,
    mut v_bs_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1794_: usize = 0;
    let mut v_i_boxed_1795_: usize = 0;
    let mut v_res_1796_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1794_ = lean_unbox_usize(v_sz_1791_);
    lean_dec(v_sz_1791_);
    v_i_boxed_1795_ = lean_unbox_usize(v_i_1792_);
    lean_dec(v_i_1792_);
    v_res_1796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(v_00_u03b1_1789_, v_00_u03b2_1790_, v_sz_boxed_1794_, v_i_boxed_1795_, v_bs_1793_);
    return v_res_1796_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
    mut v_cmp_1797_: *mut LeanObject,
    mut v_k_1798_: *mut LeanObject,
    mut v_t_1799_: *mut LeanObject,
) -> u8 {
    let mut v_k_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1799_) == 0 {
                    v_k_1800_ = lean_ctor_get(v_t_1799_, 1);
                    lean_inc(v_k_1800_);
                    v_l_1801_ = lean_ctor_get(v_t_1799_, 3);
                    lean_inc(v_l_1801_);
                    v_r_1802_ = lean_ctor_get(v_t_1799_, 4);
                    lean_inc(v_r_1802_);
                    lean_dec_ref_known(v_t_1799_, 5);
                    lean_inc_ref(v_cmp_1797_);
                    lean_inc(v_k_1798_);
                    v___x_1803_ = lean_apply_2(v_cmp_1797_, v_k_1798_, v_k_1800_);
                    v___x_1804_ = (lean_unbox(v___x_1803_) as u8);
                    match v___x_1804_ {
                        0 => {
                            lean_dec(v_r_1802_);
                            v_t_1799_ = v_l_1801_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_1802_);
                            lean_dec(v_l_1801_);
                            lean_dec(v_k_1798_);
                            lean_dec_ref(v_cmp_1797_);
                            v___x_1806_ = 1;
                            return v___x_1806_;
                        }
                        _ => {
                            lean_dec(v_l_1801_);
                            v_t_1799_ = v_r_1802_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_1798_);
                    lean_dec_ref(v_cmp_1797_);
                    v___x_1808_ = 0;
                    return v___x_1808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg___boxed(
    mut v_cmp_1809_: *mut LeanObject,
    mut v_k_1810_: *mut LeanObject,
    mut v_t_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1812_: u8 = 0;
    let mut v_r_1813_: *mut LeanObject = core::ptr::null_mut();
    v_res_1812_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1809_,
            v_k_1810_,
            v_t_1811_,
        );
    v_r_1813_ = lean_box((v_res_1812_) as usize);
    return v_r_1813_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___redArg(
    mut v_cmp_1814_: *mut LeanObject,
    mut v_k_1815_: *mut LeanObject,
    mut v_t_1816_: *mut LeanObject,
) -> u8 {
    let mut v_indices_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    v_indices_1817_ = lean_ctor_get(v_t_1816_, 1);
    lean_inc(v_indices_1817_);
    lean_dec_ref(v_t_1816_);
    v___x_1818_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1814_,
            v_k_1815_,
            v_indices_1817_,
        );
    return v___x_1818_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___redArg___boxed(
    mut v_cmp_1819_: *mut LeanObject,
    mut v_k_1820_: *mut LeanObject,
    mut v_t_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1822_: u8 = 0;
    let mut v_r_1823_: *mut LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_1819_, v_k_1820_, v_t_1821_);
    v_r_1823_ = lean_box((v_res_1822_) as usize);
    return v_r_1823_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains(
    mut v_00_u03b1_1824_: *mut LeanObject,
    mut v_00_u03b2_1825_: *mut LeanObject,
    mut v_cmp_1826_: *mut LeanObject,
    mut v_k_1827_: *mut LeanObject,
    mut v_t_1828_: *mut LeanObject,
) -> u8 {
    let mut v___x_1829_: u8 = 0;
    v___x_1829_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_1826_, v_k_1827_, v_t_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___boxed(
    mut v_00_u03b1_1830_: *mut LeanObject,
    mut v_00_u03b2_1831_: *mut LeanObject,
    mut v_cmp_1832_: *mut LeanObject,
    mut v_k_1833_: *mut LeanObject,
    mut v_t_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1835_: u8 = 0;
    let mut v_r_1836_: *mut LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lake_Toml_RBDict_contains(
        v_00_u03b1_1830_,
        v_00_u03b2_1831_,
        v_cmp_1832_,
        v_k_1833_,
        v_t_1834_,
    );
    v_r_1836_ = lean_box((v_res_1835_) as usize);
    return v_r_1836_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(
    mut v_00_u03b1_1837_: *mut LeanObject,
    mut v_cmp_1838_: *mut LeanObject,
    mut v_00_u03b2_1839_: *mut LeanObject,
    mut v_k_1840_: *mut LeanObject,
    mut v_t_1841_: *mut LeanObject,
) -> u8 {
    let mut v___x_1842_: u8 = 0;
    v___x_1842_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1838_,
            v_k_1840_,
            v_t_1841_,
        );
    return v___x_1842_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___boxed(
    mut v_00_u03b1_1843_: *mut LeanObject,
    mut v_cmp_1844_: *mut LeanObject,
    mut v_00_u03b2_1845_: *mut LeanObject,
    mut v_k_1846_: *mut LeanObject,
    mut v_t_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1848_: u8 = 0;
    let mut v_r_1849_: *mut LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(
        v_00_u03b1_1843_,
        v_cmp_1844_,
        v_00_u03b2_1845_,
        v_k_1846_,
        v_t_1847_,
    );
    v_r_1849_ = lean_box((v_res_1848_) as usize);
    return v_r_1849_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(
    mut v_cmp_1850_: *mut LeanObject,
    mut v_t_1851_: *mut LeanObject,
    mut v_k_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: u8 = 0;
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1851_) == 0 {
                    v_k_1853_ = lean_ctor_get(v_t_1851_, 1);
                    lean_inc(v_k_1853_);
                    v_v_1854_ = lean_ctor_get(v_t_1851_, 2);
                    lean_inc(v_v_1854_);
                    v_l_1855_ = lean_ctor_get(v_t_1851_, 3);
                    lean_inc(v_l_1855_);
                    v_r_1856_ = lean_ctor_get(v_t_1851_, 4);
                    lean_inc(v_r_1856_);
                    lean_dec_ref_known(v_t_1851_, 5);
                    lean_inc_ref(v_cmp_1850_);
                    lean_inc(v_k_1852_);
                    v___x_1857_ = lean_apply_2(v_cmp_1850_, v_k_1852_, v_k_1853_);
                    v___x_1858_ = (lean_unbox(v___x_1857_) as u8);
                    match v___x_1858_ {
                        0 => {
                            lean_dec(v_r_1856_);
                            lean_dec(v_v_1854_);
                            v_t_1851_ = v_l_1855_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_1856_);
                            lean_dec(v_l_1855_);
                            lean_dec(v_k_1852_);
                            lean_dec_ref(v_cmp_1850_);
                            v___x_1860_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1860_, 0, v_v_1854_);
                            return v___x_1860_;
                        }
                        _ => {
                            lean_dec(v_l_1855_);
                            lean_dec(v_v_1854_);
                            v_t_1851_ = v_r_1856_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_1852_);
                    lean_dec_ref(v_cmp_1850_);
                    v___x_1862_ = lean_box(0);
                    return v___x_1862_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_findIdx_x3f___redArg(
    mut v_cmp_1863_: *mut LeanObject,
    mut v_k_1864_: *mut LeanObject,
    mut v_t_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_1866_ = lean_ctor_get(v_t_1865_, 0);
                lean_inc_ref(v_items_1866_);
                v_indices_1867_ = lean_ctor_get(v_t_1865_, 1);
                lean_inc(v_indices_1867_);
                lean_dec_ref(v_t_1865_);
                v___x_1868_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_1863_, v_indices_1867_, v_k_1864_);
                if lean_obj_tag(v___x_1868_) == 0 {
                    lean_dec_ref(v_items_1866_);
                    v___x_1869_ = lean_box(0);
                    return v___x_1869_;
                } else {
                    v_val_1870_ = lean_ctor_get(v___x_1868_, 0);
                    v_isSharedCheck_1880_ = (!lean_is_exclusive(v___x_1868_)) as u8;
                    if v_isSharedCheck_1880_ == 0 {
                        v___x_1872_ = v___x_1868_;
                        v_isShared_1873_ = v_isSharedCheck_1880_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1870_);
                        lean_dec(v___x_1868_);
                        v___x_1872_ = lean_box(0);
                        v_isShared_1873_ = v_isSharedCheck_1880_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1874_ = lean_array_get_size(v_items_1866_);
                lean_dec_ref(v_items_1866_);
                v___x_1875_ = lean_nat_dec_lt(v_val_1870_, v___x_1874_);
                if v___x_1875_ == 0 {
                    lean_del_object(v___x_1872_);
                    lean_dec(v_val_1870_);
                    v___x_1876_ = lean_box(0);
                    return v___x_1876_;
                } else {
                    if v_isShared_1873_ == 0 {
                        v___x_1878_ = v___x_1872_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_val_1870_);
                        v___x_1878_ = v_reuseFailAlloc_1879_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_findIdx_x3f(
    mut v_00_u03b1_1881_: *mut LeanObject,
    mut v_00_u03b2_1882_: *mut LeanObject,
    mut v_cmp_1883_: *mut LeanObject,
    mut v_k_1884_: *mut LeanObject,
    mut v_t_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    v___x_1886_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1883_, v_k_1884_, v_t_1885_);
    return v___x_1886_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0(
    mut v_00_u03b1_1887_: *mut LeanObject,
    mut v_cmp_1888_: *mut LeanObject,
    mut v_00_u03b4_1889_: *mut LeanObject,
    mut v_t_1890_: *mut LeanObject,
    mut v_k_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_1888_, v_t_1890_, v_k_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lake_Toml_RBDict_findEntry_x3f___redArg(
    mut v_cmp_1893_: *mut LeanObject,
    mut v_k_1894_: *mut LeanObject,
    mut v_t_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v_items_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_t_1895_);
                v___x_1896_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1893_, v_k_1894_, v_t_1895_);
                if lean_obj_tag(v___x_1896_) == 0 {
                    lean_dec_ref(v_t_1895_);
                    v___x_1897_ = lean_box(0);
                    return v___x_1897_;
                } else {
                    v_val_1898_ = lean_ctor_get(v___x_1896_, 0);
                    v_isSharedCheck_1907_ = (!lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1907_ == 0 {
                        v___x_1900_ = v___x_1896_;
                        v_isShared_1901_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1898_);
                        lean_dec(v___x_1896_);
                        v___x_1900_ = lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_items_1902_ = lean_ctor_get(v_t_1895_, 0);
                lean_inc_ref(v_items_1902_);
                lean_dec_ref(v_t_1895_);
                v___x_1903_ = lean_array_fget(v_items_1902_, v_val_1898_);
                lean_dec(v_val_1898_);
                lean_dec_ref(v_items_1902_);
                if v_isShared_1901_ == 0 {
                    lean_ctor_set(v___x_1900_, 0, v___x_1903_);
                    v___x_1905_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_findEntry_x3f(
    mut v_00_u03b1_1908_: *mut LeanObject,
    mut v_00_u03b2_1909_: *mut LeanObject,
    mut v_cmp_1910_: *mut LeanObject,
    mut v_k_1911_: *mut LeanObject,
    mut v_t_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    v___x_1913_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1910_, v_k_1911_, v_t_1912_);
    return v___x_1913_;
}
pub unsafe fn l_Lake_Toml_RBDict_find_x3f___redArg(
    mut v_cmp_1914_: *mut LeanObject,
    mut v_k_1915_: *mut LeanObject,
    mut v_t_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v_snd_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1914_, v_k_1915_, v_t_1916_);
                if lean_obj_tag(v___x_1917_) == 0 {
                    v___x_1918_ = lean_box(0);
                    return v___x_1918_;
                } else {
                    v_val_1919_ = lean_ctor_get(v___x_1917_, 0);
                    v_isSharedCheck_1927_ = (!lean_is_exclusive(v___x_1917_)) as u8;
                    if v_isSharedCheck_1927_ == 0 {
                        v___x_1921_ = v___x_1917_;
                        v_isShared_1922_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1919_);
                        lean_dec(v___x_1917_);
                        v___x_1921_ = lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1923_ = lean_ctor_get(v_val_1919_, 1);
                lean_inc(v_snd_1923_);
                lean_dec(v_val_1919_);
                if v_isShared_1922_ == 0 {
                    lean_ctor_set(v___x_1921_, 0, v_snd_1923_);
                    v___x_1925_ = v___x_1921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_snd_1923_);
                    v___x_1925_ = v_reuseFailAlloc_1926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_find_x3f(
    mut v_00_u03b1_1928_: *mut LeanObject,
    mut v_00_u03b2_1929_: *mut LeanObject,
    mut v_cmp_1930_: *mut LeanObject,
    mut v_k_1931_: *mut LeanObject,
    mut v_t_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v_snd_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1933_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1930_, v_k_1931_, v_t_1932_);
                if lean_obj_tag(v___x_1933_) == 0 {
                    v___x_1934_ = lean_box(0);
                    return v___x_1934_;
                } else {
                    v_val_1935_ = lean_ctor_get(v___x_1933_, 0);
                    v_isSharedCheck_1943_ = (!lean_is_exclusive(v___x_1933_)) as u8;
                    if v_isSharedCheck_1943_ == 0 {
                        v___x_1937_ = v___x_1933_;
                        v_isShared_1938_ = v_isSharedCheck_1943_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1935_);
                        lean_dec(v___x_1933_);
                        v___x_1937_ = lean_box(0);
                        v_isShared_1938_ = v_isSharedCheck_1943_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1939_ = lean_ctor_get(v_val_1935_, 1);
                lean_inc(v_snd_1939_);
                lean_dec(v_val_1935_);
                if v_isShared_1938_ == 0 {
                    lean_ctor_set(v___x_1937_, 0, v_snd_1939_);
                    v___x_1941_ = v___x_1937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_snd_1939_);
                    v___x_1941_ = v_reuseFailAlloc_1942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_push___redArg(
    mut v_cmp_1944_: *mut LeanObject,
    mut v_k_1945_: *mut LeanObject,
    mut v_v_1946_: *mut LeanObject,
    mut v_t_1947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_1948_ = lean_ctor_get(v_t_1947_, 0);
                v_indices_1949_ = lean_ctor_get(v_t_1947_, 1);
                v_isSharedCheck_1960_ = (!lean_is_exclusive(v_t_1947_)) as u8;
                if v_isSharedCheck_1960_ == 0 {
                    v___x_1951_ = v_t_1947_;
                    v_isShared_1952_ = v_isSharedCheck_1960_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_indices_1949_);
                    lean_inc(v_items_1948_);
                    lean_dec(v_t_1947_);
                    v___x_1951_ = lean_box(0);
                    v_isShared_1952_ = v_isSharedCheck_1960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_k_1945_);
                v___x_1953_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1953_, 0, v_k_1945_);
                lean_ctor_set(v___x_1953_, 1, v_v_1946_);
                lean_inc_ref(v_items_1948_);
                v___x_1954_ = lean_array_push(v_items_1948_, v___x_1953_);
                v___x_1955_ = lean_array_get_size(v_items_1948_);
                lean_dec_ref(v_items_1948_);
                v___x_1956_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1944_, v_k_1945_, v___x_1955_, v_indices_1949_);
                if v_isShared_1952_ == 0 {
                    lean_ctor_set(v___x_1951_, 1, v___x_1956_);
                    lean_ctor_set(v___x_1951_, 0, v___x_1954_);
                    v___x_1958_ = v___x_1951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1954_);
                    lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1956_);
                    v___x_1958_ = v_reuseFailAlloc_1959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_push(
    mut v_00_u03b1_1961_: *mut LeanObject,
    mut v_00_u03b2_1962_: *mut LeanObject,
    mut v_cmp_1963_: *mut LeanObject,
    mut v_k_1964_: *mut LeanObject,
    mut v_v_1965_: *mut LeanObject,
    mut v_t_1966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    v___x_1967_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1963_, v_k_1964_, v_v_1965_, v_t_1966_);
    return v___x_1967_;
}
pub unsafe fn l_Lake_Toml_RBDict_alter___redArg(
    mut v_cmp_1968_: *mut LeanObject,
    mut v_k_1969_: *mut LeanObject,
    mut v_f_1970_: *mut LeanObject,
    mut v_t_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v_items_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_t_1971_);
                lean_inc(v_k_1969_);
                lean_inc_ref(v_cmp_1968_);
                v___x_1972_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1968_, v_k_1969_, v_t_1971_);
                if lean_obj_tag(v___x_1972_) == 1 {
                    lean_dec(v_k_1969_);
                    lean_dec_ref(v_cmp_1968_);
                    v_val_1973_ = lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_2008_ = (!lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_1975_ = v___x_1972_;
                        v_isShared_1976_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1973_);
                        lean_dec(v___x_1972_);
                        v___x_1975_ = lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1972_);
                    v___x_2009_ = lean_box(0);
                    v___x_2010_ = lean_apply_1(v_f_1970_, v___x_2009_);
                    v___x_2011_ = l_Lake_Toml_RBDict_push___redArg(
                        v_cmp_1968_,
                        v_k_1969_,
                        v___x_2010_,
                        v_t_1971_,
                    );
                    return v___x_2011_;
                }
            }
            1 => {
                v_items_1977_ = lean_ctor_get(v_t_1971_, 0);
                v_indices_1978_ = lean_ctor_get(v_t_1971_, 1);
                v_isSharedCheck_2007_ = (!lean_is_exclusive(v_t_1971_)) as u8;
                if v_isSharedCheck_2007_ == 0 {
                    v___x_1980_ = v_t_1971_;
                    v_isShared_1981_ = v_isSharedCheck_2007_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_indices_1978_);
                    lean_inc(v_items_1977_);
                    lean_dec(v_t_1971_);
                    v___x_1980_ = lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_2007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1982_ = lean_array_get_size(v_items_1977_);
                v___x_1983_ = lean_nat_dec_lt(v_val_1973_, v___x_1982_);
                if v___x_1983_ == 0 {
                    lean_del_object(v___x_1975_);
                    lean_dec(v_val_1973_);
                    lean_dec(v_f_1970_);
                    if v_isShared_1981_ == 0 {
                        v___x_1985_ = v___x_1980_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_items_1977_);
                        lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_indices_1978_);
                        v___x_1985_ = v_reuseFailAlloc_1986_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_v_1987_ = lean_array_fget(v_items_1977_, v_val_1973_);
                    v_fst_1988_ = lean_ctor_get(v_v_1987_, 0);
                    v_snd_1989_ = lean_ctor_get(v_v_1987_, 1);
                    v_isSharedCheck_2006_ = (!lean_is_exclusive(v_v_1987_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v___x_1991_ = v_v_1987_;
                        v_isShared_1992_ = v_isSharedCheck_2006_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_1989_);
                        lean_inc(v_fst_1988_);
                        lean_dec(v_v_1987_);
                        v___x_1991_ = lean_box(0);
                        v_isShared_1992_ = v_isSharedCheck_2006_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1985_;
            }
            4 => {
                v___x_1993_ = lean_box(0);
                v_xs_x27_1994_ = lean_array_fset(v_items_1977_, v_val_1973_, v___x_1993_);
                if v_isShared_1976_ == 0 {
                    lean_ctor_set(v___x_1975_, 0, v_snd_1989_);
                    v___x_1996_ = v___x_1975_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_snd_1989_);
                    v___x_1996_ = v_reuseFailAlloc_2005_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1997_ = lean_apply_1(v_f_1970_, v___x_1996_);
                if v_isShared_1992_ == 0 {
                    lean_ctor_set(v___x_1991_, 1, v___x_1997_);
                    v___x_1999_ = v___x_1991_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_fst_1988_);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1997_);
                    v___x_1999_ = v_reuseFailAlloc_2004_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2000_ = lean_array_fset(v_xs_x27_1994_, v_val_1973_, v___x_1999_);
                lean_dec(v_val_1973_);
                if v_isShared_1981_ == 0 {
                    lean_ctor_set(v___x_1980_, 0, v___x_2000_);
                    v___x_2002_ = v___x_1980_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_indices_1978_);
                    v___x_2002_ = v_reuseFailAlloc_2003_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_alter(
    mut v_00_u03b1_2012_: *mut LeanObject,
    mut v_00_u03b2_2013_: *mut LeanObject,
    mut v_cmp_2014_: *mut LeanObject,
    mut v_k_2015_: *mut LeanObject,
    mut v_f_2016_: *mut LeanObject,
    mut v_t_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    v___x_2018_ = l_Lake_Toml_RBDict_alter___redArg(v_cmp_2014_, v_k_2015_, v_f_2016_, v_t_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Lake_Toml_RBDict_insert___redArg(
    mut v_cmp_2019_: *mut LeanObject,
    mut v_k_2020_: *mut LeanObject,
    mut v_v_2021_: *mut LeanObject,
    mut v_t_2022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_t_2022_);
                lean_inc(v_k_2020_);
                lean_inc_ref(v_cmp_2019_);
                v___x_2023_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_2019_, v_k_2020_, v_t_2022_);
                if lean_obj_tag(v___x_2023_) == 1 {
                    v_val_2024_ = lean_ctor_get(v___x_2023_, 0);
                    lean_inc(v_val_2024_);
                    lean_dec_ref_known(v___x_2023_, 1);
                    v_items_2025_ = lean_ctor_get(v_t_2022_, 0);
                    v_indices_2026_ = lean_ctor_get(v_t_2022_, 1);
                    v___x_2027_ = lean_array_get_size(v_items_2025_);
                    v___x_2028_ = lean_nat_dec_lt(v_val_2024_, v___x_2027_);
                    if v___x_2028_ == 0 {
                        lean_dec(v_val_2024_);
                        v___x_2029_ = l_Lake_Toml_RBDict_push___redArg(
                            v_cmp_2019_,
                            v_k_2020_,
                            v_v_2021_,
                            v_t_2022_,
                        );
                        return v___x_2029_;
                    } else {
                        lean_inc(v_indices_2026_);
                        lean_inc_ref(v_items_2025_);
                        lean_dec_ref(v_cmp_2019_);
                        v_isSharedCheck_2038_ = (!lean_is_exclusive(v_t_2022_)) as u8;
                        if v_isSharedCheck_2038_ == 0 {
                            v_unused_2039_ = lean_ctor_get(v_t_2022_, 1);
                            lean_dec(v_unused_2039_);
                            v_unused_2040_ = lean_ctor_get(v_t_2022_, 0);
                            lean_dec(v_unused_2040_);
                            v___x_2031_ = v_t_2022_;
                            v_isShared_2032_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_t_2022_);
                            v___x_2031_ = lean_box(0);
                            v_isShared_2032_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2023_);
                    v___x_2041_ = l_Lake_Toml_RBDict_push___redArg(
                        v_cmp_2019_,
                        v_k_2020_,
                        v_v_2021_,
                        v_t_2022_,
                    );
                    return v___x_2041_;
                }
            }
            1 => {
                v___x_2033_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2033_, 0, v_k_2020_);
                lean_ctor_set(v___x_2033_, 1, v_v_2021_);
                v___x_2034_ = lean_array_fset(v_items_2025_, v_val_2024_, v___x_2033_);
                lean_dec(v_val_2024_);
                if v_isShared_2032_ == 0 {
                    lean_ctor_set(v___x_2031_, 0, v___x_2034_);
                    v___x_2036_ = v___x_2031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
                    lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_indices_2026_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_insert(
    mut v_00_u03b1_2042_: *mut LeanObject,
    mut v_00_u03b2_2043_: *mut LeanObject,
    mut v_cmp_2044_: *mut LeanObject,
    mut v_k_2045_: *mut LeanObject,
    mut v_v_2046_: *mut LeanObject,
    mut v_t_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    v___x_2048_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_2044_, v_k_2045_, v_v_2046_, v_t_2047_);
    return v___x_2048_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(
    mut v_cmp_2049_: *mut LeanObject,
    mut v_as_2050_: *mut LeanObject,
    mut v_i_2051_: usize,
    mut v_stop_2052_: usize,
    mut v_b_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2054_ = lean_usize_dec_eq(v_i_2051_, v_stop_2052_);
                if v___x_2054_ == 0 {
                    v___x_2055_ = lean_array_uget_borrowed(v_as_2050_, v_i_2051_);
                    v_fst_2056_ = lean_ctor_get(v___x_2055_, 0);
                    v_snd_2057_ = lean_ctor_get(v___x_2055_, 1);
                    lean_inc(v_snd_2057_);
                    lean_inc(v_fst_2056_);
                    lean_inc_ref(v_cmp_2049_);
                    v___x_2058_ = l_Lake_Toml_RBDict_insert___redArg(
                        v_cmp_2049_,
                        v_fst_2056_,
                        v_snd_2057_,
                        v_b_2053_,
                    );
                    v___x_2059_ = 1usize;
                    v___x_2060_ = lean_usize_add(v_i_2051_, v___x_2059_);
                    v_i_2051_ = v___x_2060_;
                    v_b_2053_ = v___x_2058_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_cmp_2049_);
                    return v_b_2053_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg___boxed(
    mut v_cmp_2062_: *mut LeanObject,
    mut v_as_2063_: *mut LeanObject,
    mut v_i_2064_: *mut LeanObject,
    mut v_stop_2065_: *mut LeanObject,
    mut v_b_2066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2067_: usize = 0;
    let mut v_stop_boxed_2068_: usize = 0;
    let mut v_res_2069_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2067_ = lean_unbox_usize(v_i_2064_);
    lean_dec(v_i_2064_);
    v_stop_boxed_2068_ = lean_unbox_usize(v_stop_2065_);
    lean_dec(v_stop_2065_);
    v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2062_, v_as_2063_, v_i_boxed_2067_, v_stop_boxed_2068_, v_b_2066_);
    lean_dec_ref(v_as_2063_);
    return v_res_2069_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___redArg(
    mut v_cmp_2070_: *mut LeanObject,
    mut v_self_2071_: *mut LeanObject,
    mut v_other_2072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    v___x_2073_ = lean_unsigned_to_nat(0);
    v___x_2074_ = lean_array_get_size(v_other_2072_);
    v___x_2075_ = lean_nat_dec_lt(v___x_2073_, v___x_2074_);
    if v___x_2075_ == 0 {
        lean_dec_ref(v_cmp_2070_);
        return v_self_2071_;
    } else {
        let mut v___x_2076_: u8 = 0;
        v___x_2076_ = lean_nat_dec_le(v___x_2074_, v___x_2074_);
        if v___x_2076_ == 0 {
            if v___x_2075_ == 0 {
                lean_dec_ref(v_cmp_2070_);
                return v_self_2071_;
            } else {
                let mut v___x_2077_: usize = 0;
                let mut v___x_2078_: usize = 0;
                let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
                v___x_2077_ = 0usize;
                v___x_2078_ = lean_usize_of_nat(v___x_2074_);
                v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2070_, v_other_2072_, v___x_2077_, v___x_2078_, v_self_2071_);
                return v___x_2079_;
            }
        } else {
            let mut v___x_2080_: usize = 0;
            let mut v___x_2081_: usize = 0;
            let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
            v___x_2080_ = 0usize;
            v___x_2081_ = lean_usize_of_nat(v___x_2074_);
            v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2070_, v_other_2072_, v___x_2080_, v___x_2081_, v_self_2071_);
            return v___x_2082_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___redArg___boxed(
    mut v_cmp_2083_: *mut LeanObject,
    mut v_self_2084_: *mut LeanObject,
    mut v_other_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2086_: *mut LeanObject = core::ptr::null_mut();
    v_res_2086_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2083_, v_self_2084_, v_other_2085_);
    lean_dec_ref(v_other_2085_);
    return v_res_2086_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray(
    mut v_00_u03b1_2087_: *mut LeanObject,
    mut v_00_u03b2_2088_: *mut LeanObject,
    mut v_cmp_2089_: *mut LeanObject,
    mut v_self_2090_: *mut LeanObject,
    mut v_other_2091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2089_, v_self_2090_, v_other_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___boxed(
    mut v_00_u03b1_2093_: *mut LeanObject,
    mut v_00_u03b2_2094_: *mut LeanObject,
    mut v_cmp_2095_: *mut LeanObject,
    mut v_self_2096_: *mut LeanObject,
    mut v_other_2097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2098_: *mut LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lake_Toml_RBDict_appendArray(
        v_00_u03b1_2093_,
        v_00_u03b2_2094_,
        v_cmp_2095_,
        v_self_2096_,
        v_other_2097_,
    );
    lean_dec_ref(v_other_2097_);
    return v_res_2098_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(
    mut v_00_u03b1_2099_: *mut LeanObject,
    mut v_00_u03b2_2100_: *mut LeanObject,
    mut v_cmp_2101_: *mut LeanObject,
    mut v_as_2102_: *mut LeanObject,
    mut v_i_2103_: usize,
    mut v_stop_2104_: usize,
    mut v_b_2105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2101_, v_as_2102_, v_i_2103_, v_stop_2104_, v_b_2105_);
    return v___x_2106_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___boxed(
    mut v_00_u03b1_2107_: *mut LeanObject,
    mut v_00_u03b2_2108_: *mut LeanObject,
    mut v_cmp_2109_: *mut LeanObject,
    mut v_as_2110_: *mut LeanObject,
    mut v_i_2111_: *mut LeanObject,
    mut v_stop_2112_: *mut LeanObject,
    mut v_b_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2114_: usize = 0;
    let mut v_stop_boxed_2115_: usize = 0;
    let mut v_res_2116_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2114_ = lean_unbox_usize(v_i_2111_);
    lean_dec(v_i_2111_);
    v_stop_boxed_2115_ = lean_unbox_usize(v_stop_2112_);
    lean_dec(v_stop_2112_);
    v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(v_00_u03b1_2107_, v_00_u03b2_2108_, v_cmp_2109_, v_as_2110_, v_i_boxed_2114_, v_stop_boxed_2115_, v_b_2113_);
    lean_dec_ref(v_as_2110_);
    return v_res_2116_;
}
pub unsafe fn l_Lake_Toml_RBDict_instHAppendArrayProd___redArg(
    mut v_cmp_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    v___x_2118_ = lean_alloc_closure(
        l_Lake_Toml_RBDict_appendArray___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_2118_, 0, lean_box(0));
    lean_closure_set(v___x_2118_, 1, lean_box(0));
    lean_closure_set(v___x_2118_, 2, v_cmp_2117_);
    return v___x_2118_;
}
pub unsafe fn l_Lake_Toml_RBDict_instHAppendArrayProd(
    mut v_00_u03b1_2119_: *mut LeanObject,
    mut v_00_u03b2_2120_: *mut LeanObject,
    mut v_cmp_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2122_ = lean_alloc_closure(
        l_Lake_Toml_RBDict_appendArray___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_2122_, 0, lean_box(0));
    lean_closure_set(v___x_2122_, 1, lean_box(0));
    lean_closure_set(v___x_2122_, 2, v_cmp_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___redArg(
    mut v_cmp_2123_: *mut LeanObject,
    mut v_self_2124_: *mut LeanObject,
    mut v_other_2125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    v_items_2126_ = lean_ctor_get(v_other_2125_, 0);
    v___x_2127_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2123_, v_self_2124_, v_items_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___redArg___boxed(
    mut v_cmp_2128_: *mut LeanObject,
    mut v_self_2129_: *mut LeanObject,
    mut v_other_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2131_: *mut LeanObject = core::ptr::null_mut();
    v_res_2131_ = l_Lake_Toml_RBDict_append___redArg(v_cmp_2128_, v_self_2129_, v_other_2130_);
    lean_dec_ref(v_other_2130_);
    return v_res_2131_;
}
pub unsafe fn l_Lake_Toml_RBDict_append(
    mut v_00_u03b1_2132_: *mut LeanObject,
    mut v_00_u03b2_2133_: *mut LeanObject,
    mut v_cmp_2134_: *mut LeanObject,
    mut v_self_2135_: *mut LeanObject,
    mut v_other_2136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    v_items_2137_ = lean_ctor_get(v_other_2136_, 0);
    v___x_2138_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2134_, v_self_2135_, v_items_2137_);
    return v___x_2138_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___boxed(
    mut v_00_u03b1_2139_: *mut LeanObject,
    mut v_00_u03b2_2140_: *mut LeanObject,
    mut v_cmp_2141_: *mut LeanObject,
    mut v_self_2142_: *mut LeanObject,
    mut v_other_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2144_: *mut LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lake_Toml_RBDict_append(
        v_00_u03b1_2139_,
        v_00_u03b2_2140_,
        v_cmp_2141_,
        v_self_2142_,
        v_other_2143_,
    );
    lean_dec_ref(v_other_2143_);
    return v_res_2144_;
}
pub unsafe fn l_Lake_Toml_RBDict_instAppend___redArg(
    mut v_cmp_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    v___x_2146_ = lean_alloc_closure(
        l_Lake_Toml_RBDict_append___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_2146_, 0, lean_box(0));
    lean_closure_set(v___x_2146_, 1, lean_box(0));
    lean_closure_set(v___x_2146_, 2, v_cmp_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Lake_Toml_RBDict_instAppend(
    mut v_00_u03b1_2147_: *mut LeanObject,
    mut v_00_u03b2_2148_: *mut LeanObject,
    mut v_cmp_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    v___x_2150_ = lean_alloc_closure(
        l_Lake_Toml_RBDict_append___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_2150_, 0, lean_box(0));
    lean_closure_set(v___x_2150_, 1, lean_box(0));
    lean_closure_set(v___x_2150_, 2, v_cmp_2149_);
    return v___x_2150_;
}
pub unsafe fn l_Lake_Toml_RBDict_map___redArg___lam__0(
    mut v_f_2151_: *mut LeanObject,
    mut v_x_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2157_: u8 = 0;
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2153_ = lean_ctor_get(v_x_2152_, 0);
                v_snd_2154_ = lean_ctor_get(v_x_2152_, 1);
                v_isSharedCheck_2162_ = (!lean_is_exclusive(v_x_2152_)) as u8;
                if v_isSharedCheck_2162_ == 0 {
                    v___x_2156_ = v_x_2152_;
                    v_isShared_2157_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2154_);
                    lean_inc(v_fst_2153_);
                    lean_dec(v_x_2152_);
                    v___x_2156_ = lean_box(0);
                    v_isShared_2157_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_fst_2153_);
                v___x_2158_ = lean_apply_2(v_f_2151_, v_fst_2153_, v_snd_2154_);
                if v_isShared_2157_ == 0 {
                    lean_ctor_set(v___x_2156_, 1, v___x_2158_);
                    v___x_2160_ = v___x_2156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_fst_2153_);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2158_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_map___redArg(
    mut v_f_2182_: *mut LeanObject,
    mut v_t_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___f_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2191_: usize = 0;
    let mut v___x_2192_: usize = 0;
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_2184_ = lean_ctor_get(v_t_2183_, 0);
                v_indices_2185_ = lean_ctor_get(v_t_2183_, 1);
                v_isSharedCheck_2197_ = (!lean_is_exclusive(v_t_2183_)) as u8;
                if v_isSharedCheck_2197_ == 0 {
                    v___x_2187_ = v_t_2183_;
                    v_isShared_2188_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_indices_2185_);
                    lean_inc(v_items_2184_);
                    lean_dec(v_t_2183_);
                    v___x_2187_ = lean_box(0);
                    v_isShared_2188_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2189_ = lean_alloc_closure(
                    l_Lake_Toml_RBDict_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2189_, 0, v_f_2182_);
                v___x_2190_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
                v_sz_2191_ = lean_array_size(v_items_2184_);
                v___x_2192_ = 0usize;
                v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2190_,
                    v___f_2189_,
                    v_sz_2191_,
                    v___x_2192_,
                    v_items_2184_,
                );
                if v_isShared_2188_ == 0 {
                    lean_ctor_set(v___x_2187_, 0, v___x_2193_);
                    v___x_2195_ = v___x_2187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
                    lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_indices_2185_);
                    v___x_2195_ = v_reuseFailAlloc_2196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_map(
    mut v_00_u03b1_2198_: *mut LeanObject,
    mut v_00_u03b2_2199_: *mut LeanObject,
    mut v_00_u03b3_2200_: *mut LeanObject,
    mut v_cmp_2201_: *mut LeanObject,
    mut v_f_2202_: *mut LeanObject,
    mut v_t_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2208_: u8 = 0;
    let mut v___f_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2211_: usize = 0;
    let mut v___x_2212_: usize = 0;
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_2204_ = lean_ctor_get(v_t_2203_, 0);
                v_indices_2205_ = lean_ctor_get(v_t_2203_, 1);
                v_isSharedCheck_2217_ = (!lean_is_exclusive(v_t_2203_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v___x_2207_ = v_t_2203_;
                    v_isShared_2208_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_indices_2205_);
                    lean_inc(v_items_2204_);
                    lean_dec(v_t_2203_);
                    v___x_2207_ = lean_box(0);
                    v_isShared_2208_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2209_ = lean_alloc_closure(
                    l_Lake_Toml_RBDict_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2209_, 0, v_f_2202_);
                v___x_2210_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
                v_sz_2211_ = lean_array_size(v_items_2204_);
                v___x_2212_ = 0usize;
                v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2210_,
                    v___f_2209_,
                    v_sz_2211_,
                    v___x_2212_,
                    v_items_2204_,
                );
                if v_isShared_2208_ == 0 {
                    lean_ctor_set(v___x_2207_, 0, v___x_2213_);
                    v___x_2215_ = v___x_2207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_indices_2205_);
                    v___x_2215_ = v_reuseFailAlloc_2216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_map___boxed(
    mut v_00_u03b1_2218_: *mut LeanObject,
    mut v_00_u03b2_2219_: *mut LeanObject,
    mut v_00_u03b3_2220_: *mut LeanObject,
    mut v_cmp_2221_: *mut LeanObject,
    mut v_f_2222_: *mut LeanObject,
    mut v_t_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2224_: *mut LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Lake_Toml_RBDict_map(
        v_00_u03b1_2218_,
        v_00_u03b2_2219_,
        v_00_u03b3_2220_,
        v_cmp_2221_,
        v_f_2222_,
        v_t_2223_,
    );
    lean_dec_ref(v_cmp_2221_);
    return v_res_2224_;
}
pub unsafe fn l_Lake_Toml_RBDict_filter___redArg___lam__0(
    mut v_p_2225_: *mut LeanObject,
    mut v_cmp_2226_: *mut LeanObject,
    mut v_x1_2227_: *mut LeanObject,
    mut v_x2_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    v_fst_2229_ = lean_ctor_get(v_x2_2228_, 0);
    lean_inc_n(v_fst_2229_, 2);
    v_snd_2230_ = lean_ctor_get(v_x2_2228_, 1);
    lean_inc_n(v_snd_2230_, 2);
    lean_dec_ref(v_x2_2228_);
    v___x_2231_ = lean_apply_2(v_p_2225_, v_fst_2229_, v_snd_2230_);
    v___x_2232_ = (lean_unbox(v___x_2231_) as u8);
    if v___x_2232_ == 0 {
        lean_dec(v_snd_2230_);
        lean_dec(v_fst_2229_);
        lean_dec_ref(v_cmp_2226_);
        return v_x1_2227_;
    } else {
        let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
        v___x_2233_ =
            l_Lake_Toml_RBDict_push___redArg(v_cmp_2226_, v_fst_2229_, v_snd_2230_, v_x1_2227_);
        return v___x_2233_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filter___redArg(
    mut v_cmp_2234_: *mut LeanObject,
    mut v_p_2235_: *mut LeanObject,
    mut v_t_2236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    v_items_2237_ = lean_ctor_get(v_t_2236_, 0);
    lean_inc_ref(v_items_2237_);
    lean_dec_ref(v_t_2236_);
    v___x_2238_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_2234_);
    v___x_2239_ = lean_unsigned_to_nat(0);
    v___x_2240_ = lean_array_get_size(v_items_2237_);
    v___x_2241_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2242_ = lean_nat_dec_lt(v___x_2239_, v___x_2240_);
    if v___x_2242_ == 0 {
        lean_dec_ref(v_items_2237_);
        lean_dec_ref(v_p_2235_);
        lean_dec_ref(v_cmp_2234_);
        return v___x_2238_;
    } else {
        let mut v___f_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: u8 = 0;
        v___f_2243_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_filter___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2243_, 0, v_p_2235_);
        lean_closure_set(v___f_2243_, 1, v_cmp_2234_);
        v___x_2244_ = lean_nat_dec_le(v___x_2240_, v___x_2240_);
        if v___x_2244_ == 0 {
            if v___x_2242_ == 0 {
                lean_dec_ref(v___f_2243_);
                lean_dec_ref(v_items_2237_);
                return v___x_2238_;
            } else {
                let mut v___x_2245_: usize = 0;
                let mut v___x_2246_: usize = 0;
                let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
                v___x_2245_ = 0usize;
                v___x_2246_ = lean_usize_of_nat(v___x_2240_);
                v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2241_,
                    v___f_2243_,
                    v_items_2237_,
                    v___x_2245_,
                    v___x_2246_,
                    v___x_2238_,
                );
                return v___x_2247_;
            }
        } else {
            let mut v___x_2248_: usize = 0;
            let mut v___x_2249_: usize = 0;
            let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
            v___x_2248_ = 0usize;
            v___x_2249_ = lean_usize_of_nat(v___x_2240_);
            v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_2241_,
                v___f_2243_,
                v_items_2237_,
                v___x_2248_,
                v___x_2249_,
                v___x_2238_,
            );
            return v___x_2250_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filter(
    mut v_00_u03b1_2251_: *mut LeanObject,
    mut v_00_u03b2_2252_: *mut LeanObject,
    mut v_cmp_2253_: *mut LeanObject,
    mut v_p_2254_: *mut LeanObject,
    mut v_t_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    v_items_2256_ = lean_ctor_get(v_t_2255_, 0);
    lean_inc_ref(v_items_2256_);
    lean_dec_ref(v_t_2255_);
    v___x_2257_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_2253_);
    v___x_2258_ = lean_unsigned_to_nat(0);
    v___x_2259_ = lean_array_get_size(v_items_2256_);
    v___x_2260_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2261_ = lean_nat_dec_lt(v___x_2258_, v___x_2259_);
    if v___x_2261_ == 0 {
        lean_dec_ref(v_items_2256_);
        lean_dec_ref(v_p_2254_);
        lean_dec_ref(v_cmp_2253_);
        return v___x_2257_;
    } else {
        let mut v___f_2262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: u8 = 0;
        v___f_2262_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_filter___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2262_, 0, v_p_2254_);
        lean_closure_set(v___f_2262_, 1, v_cmp_2253_);
        v___x_2263_ = lean_nat_dec_le(v___x_2259_, v___x_2259_);
        if v___x_2263_ == 0 {
            if v___x_2261_ == 0 {
                lean_dec_ref(v___f_2262_);
                lean_dec_ref(v_items_2256_);
                return v___x_2257_;
            } else {
                let mut v___x_2264_: usize = 0;
                let mut v___x_2265_: usize = 0;
                let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
                v___x_2264_ = 0usize;
                v___x_2265_ = lean_usize_of_nat(v___x_2259_);
                v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2260_,
                    v___f_2262_,
                    v_items_2256_,
                    v___x_2264_,
                    v___x_2265_,
                    v___x_2257_,
                );
                return v___x_2266_;
            }
        } else {
            let mut v___x_2267_: usize = 0;
            let mut v___x_2268_: usize = 0;
            let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
            v___x_2267_ = 0usize;
            v___x_2268_ = lean_usize_of_nat(v___x_2259_);
            v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_2260_,
                v___f_2262_,
                v_items_2256_,
                v___x_2267_,
                v___x_2268_,
                v___x_2257_,
            );
            return v___x_2269_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filterMap___redArg___lam__0(
    mut v_f_2270_: *mut LeanObject,
    mut v_cmp_2271_: *mut LeanObject,
    mut v_x1_2272_: *mut LeanObject,
    mut v_x2_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2274_ = lean_ctor_get(v_x2_2273_, 0);
    lean_inc_n(v_fst_2274_, 2);
    v_snd_2275_ = lean_ctor_get(v_x2_2273_, 1);
    lean_inc(v_snd_2275_);
    lean_dec_ref(v_x2_2273_);
    v___x_2276_ = lean_apply_2(v_f_2270_, v_fst_2274_, v_snd_2275_);
    if lean_obj_tag(v___x_2276_) == 1 {
        let mut v_val_2277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
        v_val_2277_ = lean_ctor_get(v___x_2276_, 0);
        lean_inc(v_val_2277_);
        lean_dec_ref_known(v___x_2276_, 1);
        v___x_2278_ =
            l_Lake_Toml_RBDict_push___redArg(v_cmp_2271_, v_fst_2274_, v_val_2277_, v_x1_2272_);
        return v___x_2278_;
    } else {
        lean_dec(v___x_2276_);
        lean_dec(v_fst_2274_);
        lean_dec_ref(v_cmp_2271_);
        return v_x1_2272_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filterMap___redArg(
    mut v_cmp_2279_: *mut LeanObject,
    mut v_f_2280_: *mut LeanObject,
    mut v_t_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    v_items_2282_ = lean_ctor_get(v_t_2281_, 0);
    lean_inc_ref(v_items_2282_);
    lean_dec_ref(v_t_2281_);
    v___x_2283_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_2279_);
    v___x_2284_ = lean_unsigned_to_nat(0);
    v___x_2285_ = lean_array_get_size(v_items_2282_);
    v___x_2286_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2287_ = lean_nat_dec_lt(v___x_2284_, v___x_2285_);
    if v___x_2287_ == 0 {
        lean_dec_ref(v_items_2282_);
        lean_dec_ref(v_f_2280_);
        lean_dec_ref(v_cmp_2279_);
        return v___x_2283_;
    } else {
        let mut v___f_2288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: u8 = 0;
        v___f_2288_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_filterMap___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2288_, 0, v_f_2280_);
        lean_closure_set(v___f_2288_, 1, v_cmp_2279_);
        v___x_2289_ = lean_nat_dec_le(v___x_2285_, v___x_2285_);
        if v___x_2289_ == 0 {
            if v___x_2287_ == 0 {
                lean_dec_ref(v___f_2288_);
                lean_dec_ref(v_items_2282_);
                return v___x_2283_;
            } else {
                let mut v___x_2290_: usize = 0;
                let mut v___x_2291_: usize = 0;
                let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
                v___x_2290_ = 0usize;
                v___x_2291_ = lean_usize_of_nat(v___x_2285_);
                v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2286_,
                    v___f_2288_,
                    v_items_2282_,
                    v___x_2290_,
                    v___x_2291_,
                    v___x_2283_,
                );
                return v___x_2292_;
            }
        } else {
            let mut v___x_2293_: usize = 0;
            let mut v___x_2294_: usize = 0;
            let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
            v___x_2293_ = 0usize;
            v___x_2294_ = lean_usize_of_nat(v___x_2285_);
            v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_2286_,
                v___f_2288_,
                v_items_2282_,
                v___x_2293_,
                v___x_2294_,
                v___x_2283_,
            );
            return v___x_2295_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filterMap(
    mut v_00_u03b1_2296_: *mut LeanObject,
    mut v_00_u03b2_2297_: *mut LeanObject,
    mut v_00_u03b3_2298_: *mut LeanObject,
    mut v_cmp_2299_: *mut LeanObject,
    mut v_f_2300_: *mut LeanObject,
    mut v_t_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    v_items_2302_ = lean_ctor_get(v_t_2301_, 0);
    lean_inc_ref(v_items_2302_);
    lean_dec_ref(v_t_2301_);
    v___x_2303_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_2299_);
    v___x_2304_ = lean_unsigned_to_nat(0);
    v___x_2305_ = lean_array_get_size(v_items_2302_);
    v___x_2306_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2307_ = lean_nat_dec_lt(v___x_2304_, v___x_2305_);
    if v___x_2307_ == 0 {
        lean_dec_ref(v_items_2302_);
        lean_dec_ref(v_f_2300_);
        lean_dec_ref(v_cmp_2299_);
        return v___x_2303_;
    } else {
        let mut v___f_2308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: u8 = 0;
        v___f_2308_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_filterMap___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2308_, 0, v_f_2300_);
        lean_closure_set(v___f_2308_, 1, v_cmp_2299_);
        v___x_2309_ = lean_nat_dec_le(v___x_2305_, v___x_2305_);
        if v___x_2309_ == 0 {
            if v___x_2307_ == 0 {
                lean_dec_ref(v___f_2308_);
                lean_dec_ref(v_items_2302_);
                return v___x_2303_;
            } else {
                let mut v___x_2310_: usize = 0;
                let mut v___x_2311_: usize = 0;
                let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
                v___x_2310_ = 0usize;
                v___x_2311_ = lean_usize_of_nat(v___x_2305_);
                v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2306_,
                    v___f_2308_,
                    v_items_2302_,
                    v___x_2310_,
                    v___x_2311_,
                    v___x_2303_,
                );
                return v___x_2312_;
            }
        } else {
            let mut v___x_2313_: usize = 0;
            let mut v___x_2314_: usize = 0;
            let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
            v___x_2313_ = 0usize;
            v___x_2314_ = lean_usize_of_nat(v___x_2305_);
            v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_2306_,
                v___f_2308_,
                v_items_2302_,
                v___x_2313_,
                v___x_2314_,
                v___x_2303_,
            );
            return v___x_2315_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_foldM___redArg___lam__0(
    mut v_f_2316_: *mut LeanObject,
    mut v_s_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2319_ = lean_ctor_get(v_x_2318_, 0);
    lean_inc(v_fst_2319_);
    v_snd_2320_ = lean_ctor_get(v_x_2318_, 1);
    lean_inc(v_snd_2320_);
    lean_dec_ref(v_x_2318_);
    v___x_2321_ = lean_apply_3(v_f_2316_, v_s_2317_, v_fst_2319_, v_snd_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lake_Toml_RBDict_foldM___redArg(
    mut v_inst_2322_: *mut LeanObject,
    mut v_f_2323_: *mut LeanObject,
    mut v_init_2324_: *mut LeanObject,
    mut v_t_2325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    v_items_2326_ = lean_ctor_get(v_t_2325_, 0);
    lean_inc_ref(v_items_2326_);
    lean_dec_ref(v_t_2325_);
    v___x_2327_ = lean_unsigned_to_nat(0);
    v___x_2328_ = lean_array_get_size(v_items_2326_);
    v___x_2329_ = lean_nat_dec_lt(v___x_2327_, v___x_2328_);
    if v___x_2329_ == 0 {
        let mut v_toApplicative_2330_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_items_2326_);
        lean_dec(v_f_2323_);
        v_toApplicative_2330_ = lean_ctor_get(v_inst_2322_, 0);
        lean_inc_ref(v_toApplicative_2330_);
        lean_dec_ref(v_inst_2322_);
        v_toPure_2331_ = lean_ctor_get(v_toApplicative_2330_, 1);
        lean_inc(v_toPure_2331_);
        lean_dec_ref(v_toApplicative_2330_);
        v___x_2332_ = lean_apply_2(v_toPure_2331_, lean_box(0), v_init_2324_);
        return v___x_2332_;
    } else {
        let mut v___f_2333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        v___f_2333_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2333_, 0, v_f_2323_);
        v___x_2334_ = lean_nat_dec_le(v___x_2328_, v___x_2328_);
        if v___x_2334_ == 0 {
            if v___x_2329_ == 0 {
                let mut v_toApplicative_2335_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_2336_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_2333_);
                lean_dec_ref(v_items_2326_);
                v_toApplicative_2335_ = lean_ctor_get(v_inst_2322_, 0);
                lean_inc_ref(v_toApplicative_2335_);
                lean_dec_ref(v_inst_2322_);
                v_toPure_2336_ = lean_ctor_get(v_toApplicative_2335_, 1);
                lean_inc(v_toPure_2336_);
                lean_dec_ref(v_toApplicative_2335_);
                v___x_2337_ = lean_apply_2(v_toPure_2336_, lean_box(0), v_init_2324_);
                return v___x_2337_;
            } else {
                let mut v___x_2338_: usize = 0;
                let mut v___x_2339_: usize = 0;
                let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
                v___x_2338_ = 0usize;
                v___x_2339_ = lean_usize_of_nat(v___x_2328_);
                v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_2322_,
                    v___f_2333_,
                    v_items_2326_,
                    v___x_2338_,
                    v___x_2339_,
                    v_init_2324_,
                );
                return v___x_2340_;
            }
        } else {
            let mut v___x_2341_: usize = 0;
            let mut v___x_2342_: usize = 0;
            let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
            v___x_2341_ = 0usize;
            v___x_2342_ = lean_usize_of_nat(v___x_2328_);
            v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_2322_,
                v___f_2333_,
                v_items_2326_,
                v___x_2341_,
                v___x_2342_,
                v_init_2324_,
            );
            return v___x_2343_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_foldM(
    mut v_m_2344_: *mut LeanObject,
    mut v_00_u03c3_2345_: *mut LeanObject,
    mut v_00_u03b1_2346_: *mut LeanObject,
    mut v_00_u03b2_2347_: *mut LeanObject,
    mut v_cmp_2348_: *mut LeanObject,
    mut v_inst_2349_: *mut LeanObject,
    mut v_f_2350_: *mut LeanObject,
    mut v_init_2351_: *mut LeanObject,
    mut v_t_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    v_items_2353_ = lean_ctor_get(v_t_2352_, 0);
    lean_inc_ref(v_items_2353_);
    lean_dec_ref(v_t_2352_);
    v___x_2354_ = lean_unsigned_to_nat(0);
    v___x_2355_ = lean_array_get_size(v_items_2353_);
    v___x_2356_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
    if v___x_2356_ == 0 {
        let mut v_toApplicative_2357_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_items_2353_);
        lean_dec(v_f_2350_);
        v_toApplicative_2357_ = lean_ctor_get(v_inst_2349_, 0);
        lean_inc_ref(v_toApplicative_2357_);
        lean_dec_ref(v_inst_2349_);
        v_toPure_2358_ = lean_ctor_get(v_toApplicative_2357_, 1);
        lean_inc(v_toPure_2358_);
        lean_dec_ref(v_toApplicative_2357_);
        v___x_2359_ = lean_apply_2(v_toPure_2358_, lean_box(0), v_init_2351_);
        return v___x_2359_;
    } else {
        let mut v___f_2360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2361_: u8 = 0;
        v___f_2360_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2360_, 0, v_f_2350_);
        v___x_2361_ = lean_nat_dec_le(v___x_2355_, v___x_2355_);
        if v___x_2361_ == 0 {
            if v___x_2356_ == 0 {
                let mut v_toApplicative_2362_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_2363_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_2360_);
                lean_dec_ref(v_items_2353_);
                v_toApplicative_2362_ = lean_ctor_get(v_inst_2349_, 0);
                lean_inc_ref(v_toApplicative_2362_);
                lean_dec_ref(v_inst_2349_);
                v_toPure_2363_ = lean_ctor_get(v_toApplicative_2362_, 1);
                lean_inc(v_toPure_2363_);
                lean_dec_ref(v_toApplicative_2362_);
                v___x_2364_ = lean_apply_2(v_toPure_2363_, lean_box(0), v_init_2351_);
                return v___x_2364_;
            } else {
                let mut v___x_2365_: usize = 0;
                let mut v___x_2366_: usize = 0;
                let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
                v___x_2365_ = 0usize;
                v___x_2366_ = lean_usize_of_nat(v___x_2355_);
                v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_2349_,
                    v___f_2360_,
                    v_items_2353_,
                    v___x_2365_,
                    v___x_2366_,
                    v_init_2351_,
                );
                return v___x_2367_;
            }
        } else {
            let mut v___x_2368_: usize = 0;
            let mut v___x_2369_: usize = 0;
            let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
            v___x_2368_ = 0usize;
            v___x_2369_ = lean_usize_of_nat(v___x_2355_);
            v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_2349_,
                v___f_2360_,
                v_items_2353_,
                v___x_2368_,
                v___x_2369_,
                v_init_2351_,
            );
            return v___x_2370_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_foldM___boxed(
    mut v_m_2371_: *mut LeanObject,
    mut v_00_u03c3_2372_: *mut LeanObject,
    mut v_00_u03b1_2373_: *mut LeanObject,
    mut v_00_u03b2_2374_: *mut LeanObject,
    mut v_cmp_2375_: *mut LeanObject,
    mut v_inst_2376_: *mut LeanObject,
    mut v_f_2377_: *mut LeanObject,
    mut v_init_2378_: *mut LeanObject,
    mut v_t_2379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2380_: *mut LeanObject = core::ptr::null_mut();
    v_res_2380_ = l_Lake_Toml_RBDict_foldM(
        v_m_2371_,
        v_00_u03c3_2372_,
        v_00_u03b1_2373_,
        v_00_u03b2_2374_,
        v_cmp_2375_,
        v_inst_2376_,
        v_f_2377_,
        v_init_2378_,
        v_t_2379_,
    );
    lean_dec_ref(v_cmp_2375_);
    return v_res_2380_;
}
pub unsafe fn l_Lake_Toml_RBDict_fold___redArg(
    mut v_f_2381_: *mut LeanObject,
    mut v_init_2382_: *mut LeanObject,
    mut v_t_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    v___x_2384_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v_items_2385_ = lean_ctor_get(v_t_2383_, 0);
    lean_inc_ref(v_items_2385_);
    lean_dec_ref(v_t_2383_);
    v___x_2386_ = lean_unsigned_to_nat(0);
    v___x_2387_ = lean_array_get_size(v_items_2385_);
    v___x_2388_ = lean_nat_dec_lt(v___x_2386_, v___x_2387_);
    if v___x_2388_ == 0 {
        lean_dec_ref(v_items_2385_);
        lean_dec(v_f_2381_);
        return v_init_2382_;
    } else {
        let mut v___f_2389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: u8 = 0;
        v___f_2389_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2389_, 0, v_f_2381_);
        v___x_2390_ = lean_nat_dec_le(v___x_2387_, v___x_2387_);
        if v___x_2390_ == 0 {
            if v___x_2388_ == 0 {
                lean_dec_ref(v___f_2389_);
                lean_dec_ref(v_items_2385_);
                return v_init_2382_;
            } else {
                let mut v___x_2391_: usize = 0;
                let mut v___x_2392_: usize = 0;
                let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
                v___x_2391_ = 0usize;
                v___x_2392_ = lean_usize_of_nat(v___x_2387_);
                v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2384_,
                    v___f_2389_,
                    v_items_2385_,
                    v___x_2391_,
                    v___x_2392_,
                    v_init_2382_,
                );
                return v___x_2393_;
            }
        } else {
            let mut v___x_2394_: usize = 0;
            let mut v___x_2395_: usize = 0;
            let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
            v___x_2394_ = 0usize;
            v___x_2395_ = lean_usize_of_nat(v___x_2387_);
            v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_2384_,
                v___f_2389_,
                v_items_2385_,
                v___x_2394_,
                v___x_2395_,
                v_init_2382_,
            );
            return v___x_2396_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_fold(
    mut v_00_u03c3_2397_: *mut LeanObject,
    mut v_00_u03b1_2398_: *mut LeanObject,
    mut v_00_u03b2_2399_: *mut LeanObject,
    mut v_cmp_2400_: *mut LeanObject,
    mut v_f_2401_: *mut LeanObject,
    mut v_init_2402_: *mut LeanObject,
    mut v_t_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    v___x_2404_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v_items_2405_ = lean_ctor_get(v_t_2403_, 0);
    lean_inc_ref(v_items_2405_);
    lean_dec_ref(v_t_2403_);
    v___x_2406_ = lean_unsigned_to_nat(0);
    v___x_2407_ = lean_array_get_size(v_items_2405_);
    v___x_2408_ = lean_nat_dec_lt(v___x_2406_, v___x_2407_);
    if v___x_2408_ == 0 {
        lean_dec_ref(v_items_2405_);
        lean_dec(v_f_2401_);
        return v_init_2402_;
    } else {
        let mut v___f_2409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: u8 = 0;
        v___f_2409_ = lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2409_, 0, v_f_2401_);
        v___x_2410_ = lean_nat_dec_le(v___x_2407_, v___x_2407_);
        if v___x_2410_ == 0 {
            if v___x_2408_ == 0 {
                lean_dec_ref(v___f_2409_);
                lean_dec_ref(v_items_2405_);
                return v_init_2402_;
            } else {
                let mut v___x_2411_: usize = 0;
                let mut v___x_2412_: usize = 0;
                let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
                v___x_2411_ = 0usize;
                v___x_2412_ = lean_usize_of_nat(v___x_2407_);
                v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2404_,
                    v___f_2409_,
                    v_items_2405_,
                    v___x_2411_,
                    v___x_2412_,
                    v_init_2402_,
                );
                return v___x_2413_;
            }
        } else {
            let mut v___x_2414_: usize = 0;
            let mut v___x_2415_: usize = 0;
            let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
            v___x_2414_ = 0usize;
            v___x_2415_ = lean_usize_of_nat(v___x_2407_);
            v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_2404_,
                v___f_2409_,
                v_items_2405_,
                v___x_2414_,
                v___x_2415_,
                v_init_2402_,
            );
            return v___x_2416_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_fold___boxed(
    mut v_00_u03c3_2417_: *mut LeanObject,
    mut v_00_u03b1_2418_: *mut LeanObject,
    mut v_00_u03b2_2419_: *mut LeanObject,
    mut v_cmp_2420_: *mut LeanObject,
    mut v_f_2421_: *mut LeanObject,
    mut v_init_2422_: *mut LeanObject,
    mut v_t_2423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2424_: *mut LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_Lake_Toml_RBDict_fold(
        v_00_u03c3_2417_,
        v_00_u03b1_2418_,
        v_00_u03b2_2419_,
        v_cmp_2420_,
        v_f_2421_,
        v_init_2422_,
        v_t_2423_,
    );
    lean_dec_ref(v_cmp_2420_);
    return v_res_2424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Dict(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Data_Dict(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Toml_Data_Dict(builtin);
}

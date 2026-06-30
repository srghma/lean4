// Lean compiler output
// Module: Lake.Toml.Data.Dict
// Imports: Lean.Data.NameMap.Basic Init.Data.Nat.Fold
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
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
pub static l_Lake_Toml_instInhabitedRBDict_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_Toml_instInhabitedRBDict_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_instInhabitedRBDict_default___closed__1_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_Toml_instInhabitedRBDict_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_empty___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_Toml_RBDict_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_empty___closed__1_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__0_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Toml_RBDict_map___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Toml_RBDict_map___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Toml_RBDict_map___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Toml_RBDict_map___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Toml_RBDict_map___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Toml_RBDict_map___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_Toml_RBDict_map___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_Toml_instInhabitedRBDict_default(
    mut v_00_u03b1_1218_: *mut leanh::LeanObject,
    mut v_00_u03b2_1219_: *mut leanh::LeanObject,
    mut v_cmp_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lake_Toml_instInhabitedRBDict_default___closed__1;
    return v___x_1221_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict_default___boxed(
    mut v_00_u03b1_1222_: *mut leanh::LeanObject,
    mut v_00_u03b2_1223_: *mut leanh::LeanObject,
    mut v_cmp_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ =
        l_Lake_Toml_instInhabitedRBDict_default(v_00_u03b1_1222_, v_00_u03b2_1223_, v_cmp_1224_);
    leanh::lean_dec_ref(v_cmp_1224_);
    return v_res_1225_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___redArg(
    mut v_a_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = l_Lake_Toml_instInhabitedRBDict_default(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_1226_,
    );
    return v___x_1227_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___redArg___boxed(
    mut v_a_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lake_Toml_instInhabitedRBDict___redArg(v_a_1228_);
    leanh::lean_dec_ref(v_a_1228_);
    return v_res_1229_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict(
    mut v_a_1230_: *mut leanh::LeanObject,
    mut v_a_1231_: *mut leanh::LeanObject,
    mut v_a_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_Lake_Toml_instInhabitedRBDict_default(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_1232_,
    );
    return v___x_1233_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___boxed(
    mut v_a_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
    mut v_a_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lake_Toml_instInhabitedRBDict(v_a_1234_, v_a_1235_, v_a_1236_);
    leanh::lean_dec_ref(v_a_1236_);
    return v_res_1237_;
}
pub unsafe fn l_Lake_Toml_RBDict_empty(
    mut v_00_u03b1_1243_: *mut leanh::LeanObject,
    mut v_00_u03b2_1244_: *mut leanh::LeanObject,
    mut v_cmp_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lake_Toml_RBDict_empty___closed__1;
    return v___x_1246_;
}
pub unsafe fn l_Lake_Toml_RBDict_empty___boxed(
    mut v_00_u03b1_1247_: *mut leanh::LeanObject,
    mut v_00_u03b2_1248_: *mut leanh::LeanObject,
    mut v_cmp_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Lake_Toml_RBDict_empty(v_00_u03b1_1247_, v_00_u03b2_1248_, v_cmp_1249_);
    leanh::lean_dec_ref(v_cmp_1249_);
    return v_res_1250_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___redArg(
    mut v_cmp_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lake_Toml_RBDict_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_1251_,
    );
    return v___x_1252_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___redArg___boxed(
    mut v_cmp_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lake_Toml_RBDict_instEmptyCollection___redArg(v_cmp_1253_);
    leanh::lean_dec_ref(v_cmp_1253_);
    return v_res_1254_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection(
    mut v_00_u03b1_1255_: *mut leanh::LeanObject,
    mut v_00_u03b2_1256_: *mut leanh::LeanObject,
    mut v_cmp_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = l_Lake_Toml_RBDict_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_1257_,
    );
    return v___x_1258_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___boxed(
    mut v_00_u03b1_1259_: *mut leanh::LeanObject,
    mut v_00_u03b2_1260_: *mut leanh::LeanObject,
    mut v_cmp_1261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1262_ =
        l_Lake_Toml_RBDict_instEmptyCollection(v_00_u03b1_1259_, v_00_u03b2_1260_, v_cmp_1261_);
    leanh::lean_dec_ref(v_cmp_1261_);
    return v_res_1262_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___redArg(
    mut v_capacity_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ = lean_mk_empty_array_with_capacity(v_capacity_1263_);
    v___x_1265_ = leanh::lean_box(1);
    v___x_1266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1266_, 0, v___x_1264_);
    leanh::lean_ctor_set(v___x_1266_, 1, v___x_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___redArg___boxed(
    mut v_capacity_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_1267_);
    leanh::lean_dec(v_capacity_1267_);
    return v_res_1268_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty(
    mut v_00_u03b1_1269_: *mut leanh::LeanObject,
    mut v_00_u03b2_1270_: *mut leanh::LeanObject,
    mut v_cmp_1271_: *mut leanh::LeanObject,
    mut v_capacity_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___boxed(
    mut v_00_u03b1_1274_: *mut leanh::LeanObject,
    mut v_00_u03b2_1275_: *mut leanh::LeanObject,
    mut v_cmp_1276_: *mut leanh::LeanObject,
    mut v_capacity_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Lake_Toml_RBDict_mkEmpty(
        v_00_u03b1_1274_,
        v_00_u03b2_1275_,
        v_cmp_1276_,
        v_capacity_1277_,
    );
    leanh::lean_dec(v_capacity_1277_);
    leanh::lean_dec_ref(v_cmp_1276_);
    return v_res_1278_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(
    mut v_cmp_1279_: *mut leanh::LeanObject,
    mut v_k_1280_: *mut leanh::LeanObject,
    mut v_v_1281_: *mut leanh::LeanObject,
    mut v_t_1282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v_impl_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v_size_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v_unused_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1367_: u8 = 0;
    let mut v_unused_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_unused_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_unused_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v_k_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_unused_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v_unused_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v_size_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_unused_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1501_: u8 = 0;
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1505_: u8 = 0;
    let mut v_unused_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v_k_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v_unused_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_unused_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1552_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_unused_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1282_) == 0 {
                    v_size_1283_ = leanh::lean_ctor_get(v_t_1282_, 0);
                    v_k_1284_ = leanh::lean_ctor_get(v_t_1282_, 1);
                    v_v_1285_ = leanh::lean_ctor_get(v_t_1282_, 2);
                    v_l_1286_ = leanh::lean_ctor_get(v_t_1282_, 3);
                    v_r_1287_ = leanh::lean_ctor_get(v_t_1282_, 4);
                    v_isSharedCheck_1568_ = (!leanh::lean_is_exclusive(v_t_1282_)) as u8;
                    if v_isSharedCheck_1568_ == 0 {
                        v___x_1289_ = v_t_1282_;
                        v_isShared_1290_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1287_);
                        leanh::lean_inc(v_l_1286_);
                        leanh::lean_inc(v_v_1285_);
                        leanh::lean_inc(v_k_1284_);
                        leanh::lean_inc(v_size_1283_);
                        leanh::lean_dec(v_t_1282_);
                        v___x_1289_ = leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_cmp_1279_);
                    v___x_1569_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1570_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_1570_, 0, v___x_1569_);
                    leanh::lean_ctor_set(v___x_1570_, 1, v_k_1280_);
                    leanh::lean_ctor_set(v___x_1570_, 2, v_v_1281_);
                    leanh::lean_ctor_set(v___x_1570_, 3, v_t_1282_);
                    leanh::lean_ctor_set(v___x_1570_, 4, v_t_1282_);
                    return v___x_1570_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_cmp_1279_);
                leanh::lean_inc(v_k_1284_);
                leanh::lean_inc(v_k_1280_);
                v___x_1291_ = leanh::lean_apply_2(v_cmp_1279_, v_k_1280_, v_k_1284_);
                v___x_1292_ = (leanh::lean_unbox(v___x_1291_) as u8);
                match v___x_1292_ {
                    0 => {
                        leanh::lean_dec(v_size_1283_);
                        v_impl_1293_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1279_, v_k_1280_, v_v_1281_, v_l_1286_);
                        v___x_1294_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_1287_) == 0 {
                            v_size_1295_ = leanh::lean_ctor_get(v_r_1287_, 0);
                            v_size_1296_ = leanh::lean_ctor_get(v_impl_1293_, 0);
                            leanh::lean_inc(v_size_1296_);
                            v_k_1297_ = leanh::lean_ctor_get(v_impl_1293_, 1);
                            leanh::lean_inc(v_k_1297_);
                            v_v_1298_ = leanh::lean_ctor_get(v_impl_1293_, 2);
                            leanh::lean_inc(v_v_1298_);
                            v_l_1299_ = leanh::lean_ctor_get(v_impl_1293_, 3);
                            leanh::lean_inc(v_l_1299_);
                            v_r_1300_ = leanh::lean_ctor_get(v_impl_1293_, 4);
                            leanh::lean_inc(v_r_1300_);
                            v___x_1301_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1302_ = lean_nat_mul(v___x_1301_, v_size_1295_);
                            v___x_1303_ = lean_nat_dec_lt(v___x_1302_, v_size_1296_);
                            leanh::lean_dec(v___x_1302_);
                            if v___x_1303_ == 0 {
                                leanh::lean_dec(v_r_1300_);
                                leanh::lean_dec(v_l_1299_);
                                leanh::lean_dec(v_v_1298_);
                                leanh::lean_dec(v_k_1297_);
                                v___x_1304_ = lean_nat_add(v___x_1294_, v_size_1296_);
                                leanh::lean_dec(v_size_1296_);
                                v___x_1305_ = lean_nat_add(v___x_1304_, v_size_1295_);
                                leanh::lean_dec(v___x_1304_);
                                if v_isShared_1290_ == 0 {
                                    leanh::lean_ctor_set(v___x_1289_, 3, v_impl_1293_);
                                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1305_);
                                    v___x_1307_ = v___x_1289_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1308_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        0,
                                        v___x_1305_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        1,
                                        v_k_1284_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        2,
                                        v_v_1285_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        3,
                                        v_impl_1293_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        4,
                                        v_r_1287_,
                                    );
                                    v___x_1307_ = v_reuseFailAlloc_1308_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1374_ =
                                    (!leanh::lean_is_exclusive(v_impl_1293_)) as u8;
                                if v_isSharedCheck_1374_ == 0 {
                                    v_unused_1375_ = leanh::lean_ctor_get(v_impl_1293_, 4);
                                    leanh::lean_dec(v_unused_1375_);
                                    v_unused_1376_ = leanh::lean_ctor_get(v_impl_1293_, 3);
                                    leanh::lean_dec(v_unused_1376_);
                                    v_unused_1377_ = leanh::lean_ctor_get(v_impl_1293_, 2);
                                    leanh::lean_dec(v_unused_1377_);
                                    v_unused_1378_ = leanh::lean_ctor_get(v_impl_1293_, 1);
                                    leanh::lean_dec(v_unused_1378_);
                                    v_unused_1379_ = leanh::lean_ctor_get(v_impl_1293_, 0);
                                    leanh::lean_dec(v_unused_1379_);
                                    v___x_1310_ = v_impl_1293_;
                                    v_isShared_1311_ = v_isSharedCheck_1374_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_1293_);
                                    v___x_1310_ = leanh::lean_box(0);
                                    v_isShared_1311_ = v_isSharedCheck_1374_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1380_ = leanh::lean_ctor_get(v_impl_1293_, 3);
                            leanh::lean_inc(v_l_1380_);
                            if leanh::lean_obj_tag(v_l_1380_) == 0 {
                                v_r_1381_ = leanh::lean_ctor_get(v_impl_1293_, 4);
                                v_k_1382_ = leanh::lean_ctor_get(v_impl_1293_, 1);
                                v_v_1383_ = leanh::lean_ctor_get(v_impl_1293_, 2);
                                v_isSharedCheck_1394_ =
                                    (!leanh::lean_is_exclusive(v_impl_1293_)) as u8;
                                if v_isSharedCheck_1394_ == 0 {
                                    v_unused_1395_ = leanh::lean_ctor_get(v_impl_1293_, 3);
                                    leanh::lean_dec(v_unused_1395_);
                                    v_unused_1396_ = leanh::lean_ctor_get(v_impl_1293_, 0);
                                    leanh::lean_dec(v_unused_1396_);
                                    v___x_1385_ = v_impl_1293_;
                                    v_isShared_1386_ = v_isSharedCheck_1394_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_1381_);
                                    leanh::lean_inc(v_v_1383_);
                                    leanh::lean_inc(v_k_1382_);
                                    leanh::lean_dec(v_impl_1293_);
                                    v___x_1385_ = leanh::lean_box(0);
                                    v_isShared_1386_ = v_isSharedCheck_1394_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1397_ = leanh::lean_ctor_get(v_impl_1293_, 4);
                                leanh::lean_inc(v_r_1397_);
                                if leanh::lean_obj_tag(v_r_1397_) == 0 {
                                    v_k_1398_ = leanh::lean_ctor_get(v_impl_1293_, 1);
                                    v_v_1399_ = leanh::lean_ctor_get(v_impl_1293_, 2);
                                    v_isSharedCheck_1422_ =
                                        (!leanh::lean_is_exclusive(v_impl_1293_)) as u8;
                                    if v_isSharedCheck_1422_ == 0 {
                                        v_unused_1423_ =
                                            leanh::lean_ctor_get(v_impl_1293_, 4);
                                        leanh::lean_dec(v_unused_1423_);
                                        v_unused_1424_ =
                                            leanh::lean_ctor_get(v_impl_1293_, 3);
                                        leanh::lean_dec(v_unused_1424_);
                                        v_unused_1425_ =
                                            leanh::lean_ctor_get(v_impl_1293_, 0);
                                        leanh::lean_dec(v_unused_1425_);
                                        v___x_1401_ = v_impl_1293_;
                                        v_isShared_1402_ = v_isSharedCheck_1422_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_1399_);
                                        leanh::lean_inc(v_k_1398_);
                                        leanh::lean_dec(v_impl_1293_);
                                        v___x_1401_ = leanh::lean_box(0);
                                        v_isShared_1402_ = v_isSharedCheck_1422_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1426_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1290_ == 0 {
                                        leanh::lean_ctor_set(v___x_1289_, 4, v_r_1397_);
                                        leanh::lean_ctor_set(v___x_1289_, 3, v_impl_1293_);
                                        leanh::lean_ctor_set(v___x_1289_, 0, v___x_1426_);
                                        v___x_1428_ = v___x_1289_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1429_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            0,
                                            v___x_1426_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            1,
                                            v_k_1284_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            2,
                                            v_v_1285_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            3,
                                            v_impl_1293_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            4,
                                            v_r_1397_,
                                        );
                                        v___x_1428_ = v_reuseFailAlloc_1429_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_1285_);
                        leanh::lean_dec(v_k_1284_);
                        leanh::lean_dec_ref(v_cmp_1279_);
                        if v_isShared_1290_ == 0 {
                            leanh::lean_ctor_set(v___x_1289_, 2, v_v_1281_);
                            leanh::lean_ctor_set(v___x_1289_, 1, v_k_1280_);
                            v___x_1431_ = v___x_1289_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1432_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_size_1283_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1280_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1281_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_l_1286_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_r_1287_);
                            v___x_1431_ = v_reuseFailAlloc_1432_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_1283_);
                        v_impl_1433_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1279_, v_k_1280_, v_v_1281_, v_r_1287_);
                        v___x_1434_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_1286_) == 0 {
                            v_size_1435_ = leanh::lean_ctor_get(v_l_1286_, 0);
                            v_size_1436_ = leanh::lean_ctor_get(v_impl_1433_, 0);
                            leanh::lean_inc(v_size_1436_);
                            v_k_1437_ = leanh::lean_ctor_get(v_impl_1433_, 1);
                            leanh::lean_inc(v_k_1437_);
                            v_v_1438_ = leanh::lean_ctor_get(v_impl_1433_, 2);
                            leanh::lean_inc(v_v_1438_);
                            v_l_1439_ = leanh::lean_ctor_get(v_impl_1433_, 3);
                            leanh::lean_inc(v_l_1439_);
                            v_r_1440_ = leanh::lean_ctor_get(v_impl_1433_, 4);
                            leanh::lean_inc(v_r_1440_);
                            v___x_1441_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1442_ = lean_nat_mul(v___x_1441_, v_size_1435_);
                            v___x_1443_ = lean_nat_dec_lt(v___x_1442_, v_size_1436_);
                            leanh::lean_dec(v___x_1442_);
                            if v___x_1443_ == 0 {
                                leanh::lean_dec(v_r_1440_);
                                leanh::lean_dec(v_l_1439_);
                                leanh::lean_dec(v_v_1438_);
                                leanh::lean_dec(v_k_1437_);
                                v___x_1444_ = lean_nat_add(v___x_1434_, v_size_1435_);
                                v___x_1445_ = lean_nat_add(v___x_1444_, v_size_1436_);
                                leanh::lean_dec(v_size_1436_);
                                leanh::lean_dec(v___x_1444_);
                                if v_isShared_1290_ == 0 {
                                    leanh::lean_ctor_set(v___x_1289_, 4, v_impl_1433_);
                                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1445_);
                                    v___x_1447_ = v___x_1289_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1448_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        0,
                                        v___x_1445_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        1,
                                        v_k_1284_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        2,
                                        v_v_1285_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        3,
                                        v_l_1286_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        4,
                                        v_impl_1433_,
                                    );
                                    v___x_1447_ = v_reuseFailAlloc_1448_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1512_ =
                                    (!leanh::lean_is_exclusive(v_impl_1433_)) as u8;
                                if v_isSharedCheck_1512_ == 0 {
                                    v_unused_1513_ = leanh::lean_ctor_get(v_impl_1433_, 4);
                                    leanh::lean_dec(v_unused_1513_);
                                    v_unused_1514_ = leanh::lean_ctor_get(v_impl_1433_, 3);
                                    leanh::lean_dec(v_unused_1514_);
                                    v_unused_1515_ = leanh::lean_ctor_get(v_impl_1433_, 2);
                                    leanh::lean_dec(v_unused_1515_);
                                    v_unused_1516_ = leanh::lean_ctor_get(v_impl_1433_, 1);
                                    leanh::lean_dec(v_unused_1516_);
                                    v_unused_1517_ = leanh::lean_ctor_get(v_impl_1433_, 0);
                                    leanh::lean_dec(v_unused_1517_);
                                    v___x_1450_ = v_impl_1433_;
                                    v_isShared_1451_ = v_isSharedCheck_1512_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_1433_);
                                    v___x_1450_ = leanh::lean_box(0);
                                    v_isShared_1451_ = v_isSharedCheck_1512_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1518_ = leanh::lean_ctor_get(v_impl_1433_, 3);
                            leanh::lean_inc(v_l_1518_);
                            if leanh::lean_obj_tag(v_l_1518_) == 0 {
                                v_r_1519_ = leanh::lean_ctor_get(v_impl_1433_, 4);
                                v_k_1520_ = leanh::lean_ctor_get(v_impl_1433_, 1);
                                v_v_1521_ = leanh::lean_ctor_get(v_impl_1433_, 2);
                                v_isSharedCheck_1544_ =
                                    (!leanh::lean_is_exclusive(v_impl_1433_)) as u8;
                                if v_isSharedCheck_1544_ == 0 {
                                    v_unused_1545_ = leanh::lean_ctor_get(v_impl_1433_, 3);
                                    leanh::lean_dec(v_unused_1545_);
                                    v_unused_1546_ = leanh::lean_ctor_get(v_impl_1433_, 0);
                                    leanh::lean_dec(v_unused_1546_);
                                    v___x_1523_ = v_impl_1433_;
                                    v_isShared_1524_ = v_isSharedCheck_1544_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_1519_);
                                    leanh::lean_inc(v_v_1521_);
                                    leanh::lean_inc(v_k_1520_);
                                    leanh::lean_dec(v_impl_1433_);
                                    v___x_1523_ = leanh::lean_box(0);
                                    v_isShared_1524_ = v_isSharedCheck_1544_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1547_ = leanh::lean_ctor_get(v_impl_1433_, 4);
                                leanh::lean_inc(v_r_1547_);
                                if leanh::lean_obj_tag(v_r_1547_) == 0 {
                                    v_k_1548_ = leanh::lean_ctor_get(v_impl_1433_, 1);
                                    v_v_1549_ = leanh::lean_ctor_get(v_impl_1433_, 2);
                                    v_isSharedCheck_1560_ =
                                        (!leanh::lean_is_exclusive(v_impl_1433_)) as u8;
                                    if v_isSharedCheck_1560_ == 0 {
                                        v_unused_1561_ =
                                            leanh::lean_ctor_get(v_impl_1433_, 4);
                                        leanh::lean_dec(v_unused_1561_);
                                        v_unused_1562_ =
                                            leanh::lean_ctor_get(v_impl_1433_, 3);
                                        leanh::lean_dec(v_unused_1562_);
                                        v_unused_1563_ =
                                            leanh::lean_ctor_get(v_impl_1433_, 0);
                                        leanh::lean_dec(v_unused_1563_);
                                        v___x_1551_ = v_impl_1433_;
                                        v_isShared_1552_ = v_isSharedCheck_1560_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_1549_);
                                        leanh::lean_inc(v_k_1548_);
                                        leanh::lean_dec(v_impl_1433_);
                                        v___x_1551_ = leanh::lean_box(0);
                                        v_isShared_1552_ = v_isSharedCheck_1560_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1564_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1290_ == 0 {
                                        leanh::lean_ctor_set(v___x_1289_, 4, v_impl_1433_);
                                        leanh::lean_ctor_set(v___x_1289_, 3, v_r_1547_);
                                        leanh::lean_ctor_set(v___x_1289_, 0, v___x_1564_);
                                        v___x_1566_ = v___x_1289_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1567_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            0,
                                            v___x_1564_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            1,
                                            v_k_1284_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            2,
                                            v_v_1285_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            3,
                                            v_r_1547_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            4,
                                            v_impl_1433_,
                                        );
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
                v_size_1312_ = leanh::lean_ctor_get(v_l_1299_, 0);
                v_size_1313_ = leanh::lean_ctor_get(v_r_1300_, 0);
                v_k_1314_ = leanh::lean_ctor_get(v_r_1300_, 1);
                v_v_1315_ = leanh::lean_ctor_get(v_r_1300_, 2);
                v_l_1316_ = leanh::lean_ctor_get(v_r_1300_, 3);
                v_r_1317_ = leanh::lean_ctor_get(v_r_1300_, 4);
                v___x_1318_ = leanh::lean_unsigned_to_nat(2);
                v___x_1319_ = lean_nat_mul(v___x_1318_, v_size_1312_);
                v___x_1320_ = lean_nat_dec_lt(v_size_1313_, v___x_1319_);
                leanh::lean_dec(v___x_1319_);
                if v___x_1320_ == 0 {
                    leanh::lean_inc(v_r_1317_);
                    leanh::lean_inc(v_l_1316_);
                    leanh::lean_inc(v_v_1315_);
                    leanh::lean_inc(v_k_1314_);
                    v_isSharedCheck_1349_ = (!leanh::lean_is_exclusive(v_r_1300_)) as u8;
                    if v_isSharedCheck_1349_ == 0 {
                        v_unused_1350_ = leanh::lean_ctor_get(v_r_1300_, 4);
                        leanh::lean_dec(v_unused_1350_);
                        v_unused_1351_ = leanh::lean_ctor_get(v_r_1300_, 3);
                        leanh::lean_dec(v_unused_1351_);
                        v_unused_1352_ = leanh::lean_ctor_get(v_r_1300_, 2);
                        leanh::lean_dec(v_unused_1352_);
                        v_unused_1353_ = leanh::lean_ctor_get(v_r_1300_, 1);
                        leanh::lean_dec(v_unused_1353_);
                        v_unused_1354_ = leanh::lean_ctor_get(v_r_1300_, 0);
                        leanh::lean_dec(v_unused_1354_);
                        v___x_1322_ = v_r_1300_;
                        v_isShared_1323_ = v_isSharedCheck_1349_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1300_);
                        v___x_1322_ = leanh::lean_box(0);
                        v_isShared_1323_ = v_isSharedCheck_1349_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1289_);
                    v___x_1355_ = lean_nat_add(v___x_1294_, v_size_1296_);
                    leanh::lean_dec(v_size_1296_);
                    v___x_1356_ = lean_nat_add(v___x_1355_, v_size_1295_);
                    leanh::lean_dec(v___x_1355_);
                    v___x_1357_ = lean_nat_add(v___x_1294_, v_size_1295_);
                    v___x_1358_ = lean_nat_add(v___x_1357_, v_size_1313_);
                    leanh::lean_dec(v___x_1357_);
                    leanh::lean_inc_ref(v_r_1287_);
                    if v_isShared_1311_ == 0 {
                        leanh::lean_ctor_set(v___x_1310_, 4, v_r_1287_);
                        leanh::lean_ctor_set(v___x_1310_, 3, v_r_1300_);
                        leanh::lean_ctor_set(v___x_1310_, 2, v_v_1285_);
                        leanh::lean_ctor_set(v___x_1310_, 1, v_k_1284_);
                        leanh::lean_ctor_set(v___x_1310_, 0, v___x_1358_);
                        v___x_1360_ = v___x_1310_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1373_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1358_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1284_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1285_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_r_1300_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1287_);
                        v___x_1360_ = v_reuseFailAlloc_1373_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1324_ = lean_nat_add(v___x_1294_, v_size_1296_);
                leanh::lean_dec(v_size_1296_);
                v___x_1325_ = lean_nat_add(v___x_1324_, v_size_1295_);
                leanh::lean_dec(v___x_1324_);
                v___x_1337_ = lean_nat_add(v___x_1294_, v_size_1312_);
                if leanh::lean_obj_tag(v_l_1316_) == 0 {
                    v_size_1347_ = leanh::lean_ctor_get(v_l_1316_, 0);
                    leanh::lean_inc(v_size_1347_);
                    v___y_1339_ = v_size_1347_;
                    state = 8;
                    continue;
                } else {
                    v___x_1348_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1339_ = v___x_1348_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1330_ = lean_nat_add(v___y_1328_, v___y_1329_);
                leanh::lean_dec(v___y_1329_);
                leanh::lean_dec(v___y_1328_);
                if v_isShared_1323_ == 0 {
                    leanh::lean_ctor_set(v___x_1322_, 4, v_r_1287_);
                    leanh::lean_ctor_set(v___x_1322_, 3, v_r_1317_);
                    leanh::lean_ctor_set(v___x_1322_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v___x_1322_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v___x_1322_, 0, v___x_1330_);
                    v___x_1332_ = v___x_1322_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_r_1317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 4, v_r_1287_);
                    v___x_1332_ = v_reuseFailAlloc_1336_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1311_ == 0 {
                    leanh::lean_ctor_set(v___x_1310_, 4, v___x_1332_);
                    leanh::lean_ctor_set(v___x_1310_, 3, v___y_1327_);
                    leanh::lean_ctor_set(v___x_1310_, 2, v_v_1315_);
                    leanh::lean_ctor_set(v___x_1310_, 1, v_k_1314_);
                    leanh::lean_ctor_set(v___x_1310_, 0, v___x_1325_);
                    v___x_1334_ = v___x_1310_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1335_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___y_1327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 4, v___x_1332_);
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
                leanh::lean_dec(v___y_1339_);
                leanh::lean_dec(v___x_1337_);
                if v_isShared_1290_ == 0 {
                    leanh::lean_ctor_set(v___x_1289_, 4, v_l_1316_);
                    leanh::lean_ctor_set(v___x_1289_, 3, v_l_1299_);
                    leanh::lean_ctor_set(v___x_1289_, 2, v_v_1298_);
                    leanh::lean_ctor_set(v___x_1289_, 1, v_k_1297_);
                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1340_);
                    v___x_1342_ = v___x_1289_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1346_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_l_1299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_l_1316_);
                    v___x_1342_ = v_reuseFailAlloc_1346_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1343_ = lean_nat_add(v___x_1294_, v_size_1295_);
                if leanh::lean_obj_tag(v_r_1317_) == 0 {
                    v_size_1344_ = leanh::lean_ctor_get(v_r_1317_, 0);
                    leanh::lean_inc(v_size_1344_);
                    v___y_1327_ = v___x_1342_;
                    v___y_1328_ = v___x_1343_;
                    v___y_1329_ = v_size_1344_;
                    state = 5;
                    continue;
                } else {
                    v___x_1345_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1327_ = v___x_1342_;
                    v___y_1328_ = v___x_1343_;
                    v___y_1329_ = v___x_1345_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1367_ = (!leanh::lean_is_exclusive(v_r_1287_)) as u8;
                if v_isSharedCheck_1367_ == 0 {
                    v_unused_1368_ = leanh::lean_ctor_get(v_r_1287_, 4);
                    leanh::lean_dec(v_unused_1368_);
                    v_unused_1369_ = leanh::lean_ctor_get(v_r_1287_, 3);
                    leanh::lean_dec(v_unused_1369_);
                    v_unused_1370_ = leanh::lean_ctor_get(v_r_1287_, 2);
                    leanh::lean_dec(v_unused_1370_);
                    v_unused_1371_ = leanh::lean_ctor_get(v_r_1287_, 1);
                    leanh::lean_dec(v_unused_1371_);
                    v_unused_1372_ = leanh::lean_ctor_get(v_r_1287_, 0);
                    leanh::lean_dec(v_unused_1372_);
                    v___x_1362_ = v_r_1287_;
                    v_isShared_1363_ = v_isSharedCheck_1367_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_1287_);
                    v___x_1362_ = leanh::lean_box(0);
                    v_isShared_1363_ = v_isSharedCheck_1367_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1363_ == 0 {
                    leanh::lean_ctor_set(v___x_1362_, 4, v___x_1360_);
                    leanh::lean_ctor_set(v___x_1362_, 3, v_l_1299_);
                    leanh::lean_ctor_set(v___x_1362_, 2, v_v_1298_);
                    leanh::lean_ctor_set(v___x_1362_, 1, v_k_1297_);
                    leanh::lean_ctor_set(v___x_1362_, 0, v___x_1356_);
                    v___x_1365_ = v___x_1362_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1366_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1356_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_l_1299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 4, v___x_1360_);
                    v___x_1365_ = v_reuseFailAlloc_1366_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1365_;
            }
            13 => {
                v___x_1387_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_1381_);
                if v_isShared_1386_ == 0 {
                    leanh::lean_ctor_set(v___x_1385_, 3, v_r_1381_);
                    leanh::lean_ctor_set(v___x_1385_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v___x_1385_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v___x_1385_, 0, v___x_1294_);
                    v___x_1389_ = v___x_1385_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_r_1381_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_r_1381_);
                    v___x_1389_ = v_reuseFailAlloc_1393_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1290_ == 0 {
                    leanh::lean_ctor_set(v___x_1289_, 4, v___x_1389_);
                    leanh::lean_ctor_set(v___x_1289_, 3, v_l_1380_);
                    leanh::lean_ctor_set(v___x_1289_, 2, v_v_1383_);
                    leanh::lean_ctor_set(v___x_1289_, 1, v_k_1382_);
                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1387_);
                    v___x_1391_ = v___x_1289_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1392_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_l_1380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 4, v___x_1389_);
                    v___x_1391_ = v_reuseFailAlloc_1392_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1391_;
            }
            16 => {
                v_k_1403_ = leanh::lean_ctor_get(v_r_1397_, 1);
                v_v_1404_ = leanh::lean_ctor_get(v_r_1397_, 2);
                v_isSharedCheck_1418_ = (!leanh::lean_is_exclusive(v_r_1397_)) as u8;
                if v_isSharedCheck_1418_ == 0 {
                    v_unused_1419_ = leanh::lean_ctor_get(v_r_1397_, 4);
                    leanh::lean_dec(v_unused_1419_);
                    v_unused_1420_ = leanh::lean_ctor_get(v_r_1397_, 3);
                    leanh::lean_dec(v_unused_1420_);
                    v_unused_1421_ = leanh::lean_ctor_get(v_r_1397_, 0);
                    leanh::lean_dec(v_unused_1421_);
                    v___x_1406_ = v_r_1397_;
                    v_isShared_1407_ = v_isSharedCheck_1418_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1404_);
                    leanh::lean_inc(v_k_1403_);
                    leanh::lean_dec(v_r_1397_);
                    v___x_1406_ = leanh::lean_box(0);
                    v_isShared_1407_ = v_isSharedCheck_1418_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1408_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1407_ == 0 {
                    leanh::lean_ctor_set(v___x_1406_, 4, v_l_1380_);
                    leanh::lean_ctor_set(v___x_1406_, 3, v_l_1380_);
                    leanh::lean_ctor_set(v___x_1406_, 2, v_v_1399_);
                    leanh::lean_ctor_set(v___x_1406_, 1, v_k_1398_);
                    leanh::lean_ctor_set(v___x_1406_, 0, v___x_1294_);
                    v___x_1410_ = v___x_1406_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1380_);
                    v___x_1410_ = v_reuseFailAlloc_1417_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1402_ == 0 {
                    leanh::lean_ctor_set(v___x_1401_, 4, v_l_1380_);
                    leanh::lean_ctor_set(v___x_1401_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v___x_1401_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v___x_1401_, 0, v___x_1294_);
                    v___x_1412_ = v___x_1401_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_l_1380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_l_1380_);
                    v___x_1412_ = v_reuseFailAlloc_1416_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1290_ == 0 {
                    leanh::lean_ctor_set(v___x_1289_, 4, v___x_1412_);
                    leanh::lean_ctor_set(v___x_1289_, 3, v___x_1410_);
                    leanh::lean_ctor_set(v___x_1289_, 2, v_v_1404_);
                    leanh::lean_ctor_set(v___x_1289_, 1, v_k_1403_);
                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1408_);
                    v___x_1414_ = v___x_1289_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1415_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1408_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 3, v___x_1410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 4, v___x_1412_);
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
                v_size_1452_ = leanh::lean_ctor_get(v_l_1439_, 0);
                v_k_1453_ = leanh::lean_ctor_get(v_l_1439_, 1);
                v_v_1454_ = leanh::lean_ctor_get(v_l_1439_, 2);
                v_l_1455_ = leanh::lean_ctor_get(v_l_1439_, 3);
                v_r_1456_ = leanh::lean_ctor_get(v_l_1439_, 4);
                v_size_1457_ = leanh::lean_ctor_get(v_r_1440_, 0);
                v___x_1458_ = leanh::lean_unsigned_to_nat(2);
                v___x_1459_ = lean_nat_mul(v___x_1458_, v_size_1457_);
                v___x_1460_ = lean_nat_dec_lt(v_size_1452_, v___x_1459_);
                leanh::lean_dec(v___x_1459_);
                if v___x_1460_ == 0 {
                    leanh::lean_inc(v_r_1456_);
                    leanh::lean_inc(v_l_1455_);
                    leanh::lean_inc(v_v_1454_);
                    leanh::lean_inc(v_k_1453_);
                    v_isSharedCheck_1488_ = (!leanh::lean_is_exclusive(v_l_1439_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v_unused_1489_ = leanh::lean_ctor_get(v_l_1439_, 4);
                        leanh::lean_dec(v_unused_1489_);
                        v_unused_1490_ = leanh::lean_ctor_get(v_l_1439_, 3);
                        leanh::lean_dec(v_unused_1490_);
                        v_unused_1491_ = leanh::lean_ctor_get(v_l_1439_, 2);
                        leanh::lean_dec(v_unused_1491_);
                        v_unused_1492_ = leanh::lean_ctor_get(v_l_1439_, 1);
                        leanh::lean_dec(v_unused_1492_);
                        v_unused_1493_ = leanh::lean_ctor_get(v_l_1439_, 0);
                        leanh::lean_dec(v_unused_1493_);
                        v___x_1462_ = v_l_1439_;
                        v_isShared_1463_ = v_isSharedCheck_1488_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1439_);
                        v___x_1462_ = leanh::lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1488_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1289_);
                    v___x_1494_ = lean_nat_add(v___x_1434_, v_size_1435_);
                    v___x_1495_ = lean_nat_add(v___x_1494_, v_size_1436_);
                    leanh::lean_dec(v_size_1436_);
                    v___x_1496_ = lean_nat_add(v___x_1494_, v_size_1452_);
                    leanh::lean_dec(v___x_1494_);
                    leanh::lean_inc_ref(v_l_1286_);
                    if v_isShared_1451_ == 0 {
                        leanh::lean_ctor_set(v___x_1450_, 4, v_l_1439_);
                        leanh::lean_ctor_set(v___x_1450_, 3, v_l_1286_);
                        leanh::lean_ctor_set(v___x_1450_, 2, v_v_1285_);
                        leanh::lean_ctor_set(v___x_1450_, 1, v_k_1284_);
                        leanh::lean_ctor_set(v___x_1450_, 0, v___x_1496_);
                        v___x_1498_ = v___x_1450_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1511_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1496_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1284_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1285_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_l_1286_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_l_1439_);
                        v___x_1498_ = v_reuseFailAlloc_1511_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1464_ = lean_nat_add(v___x_1434_, v_size_1435_);
                v___x_1465_ = lean_nat_add(v___x_1464_, v_size_1436_);
                leanh::lean_dec(v_size_1436_);
                if leanh::lean_obj_tag(v_l_1455_) == 0 {
                    v_size_1486_ = leanh::lean_ctor_get(v_l_1455_, 0);
                    leanh::lean_inc(v_size_1486_);
                    v___y_1478_ = v_size_1486_;
                    state = 29;
                    continue;
                } else {
                    v___x_1487_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1478_ = v___x_1487_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1470_ = lean_nat_add(v___y_1467_, v___y_1469_);
                leanh::lean_dec(v___y_1469_);
                leanh::lean_dec(v___y_1467_);
                if v_isShared_1463_ == 0 {
                    leanh::lean_ctor_set(v___x_1462_, 4, v_r_1440_);
                    leanh::lean_ctor_set(v___x_1462_, 3, v_r_1456_);
                    leanh::lean_ctor_set(v___x_1462_, 2, v_v_1438_);
                    leanh::lean_ctor_set(v___x_1462_, 1, v_k_1437_);
                    leanh::lean_ctor_set(v___x_1462_, 0, v___x_1470_);
                    v___x_1472_ = v___x_1462_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_r_1456_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_r_1440_);
                    v___x_1472_ = v_reuseFailAlloc_1476_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1451_ == 0 {
                    leanh::lean_ctor_set(v___x_1450_, 4, v___x_1472_);
                    leanh::lean_ctor_set(v___x_1450_, 3, v___y_1468_);
                    leanh::lean_ctor_set(v___x_1450_, 2, v_v_1454_);
                    leanh::lean_ctor_set(v___x_1450_, 1, v_k_1453_);
                    leanh::lean_ctor_set(v___x_1450_, 0, v___x_1465_);
                    v___x_1474_ = v___x_1450_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1475_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 3, v___y_1468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1472_);
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
                leanh::lean_dec(v___y_1478_);
                leanh::lean_dec(v___x_1464_);
                if v_isShared_1290_ == 0 {
                    leanh::lean_ctor_set(v___x_1289_, 4, v_l_1455_);
                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1479_);
                    v___x_1481_ = v___x_1289_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_l_1286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_l_1455_);
                    v___x_1481_ = v_reuseFailAlloc_1485_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1482_ = lean_nat_add(v___x_1434_, v_size_1457_);
                if leanh::lean_obj_tag(v_r_1456_) == 0 {
                    v_size_1483_ = leanh::lean_ctor_get(v_r_1456_, 0);
                    leanh::lean_inc(v_size_1483_);
                    v___y_1467_ = v___x_1482_;
                    v___y_1468_ = v___x_1481_;
                    v___y_1469_ = v_size_1483_;
                    state = 26;
                    continue;
                } else {
                    v___x_1484_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1467_ = v___x_1482_;
                    v___y_1468_ = v___x_1481_;
                    v___y_1469_ = v___x_1484_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1505_ = (!leanh::lean_is_exclusive(v_l_1286_)) as u8;
                if v_isSharedCheck_1505_ == 0 {
                    v_unused_1506_ = leanh::lean_ctor_get(v_l_1286_, 4);
                    leanh::lean_dec(v_unused_1506_);
                    v_unused_1507_ = leanh::lean_ctor_get(v_l_1286_, 3);
                    leanh::lean_dec(v_unused_1507_);
                    v_unused_1508_ = leanh::lean_ctor_get(v_l_1286_, 2);
                    leanh::lean_dec(v_unused_1508_);
                    v_unused_1509_ = leanh::lean_ctor_get(v_l_1286_, 1);
                    leanh::lean_dec(v_unused_1509_);
                    v_unused_1510_ = leanh::lean_ctor_get(v_l_1286_, 0);
                    leanh::lean_dec(v_unused_1510_);
                    v___x_1500_ = v_l_1286_;
                    v_isShared_1501_ = v_isSharedCheck_1505_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_1286_);
                    v___x_1500_ = leanh::lean_box(0);
                    v_isShared_1501_ = v_isSharedCheck_1505_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1501_ == 0 {
                    leanh::lean_ctor_set(v___x_1500_, 4, v_r_1440_);
                    leanh::lean_ctor_set(v___x_1500_, 3, v___x_1498_);
                    leanh::lean_ctor_set(v___x_1500_, 2, v_v_1438_);
                    leanh::lean_ctor_set(v___x_1500_, 1, v_k_1437_);
                    leanh::lean_ctor_set(v___x_1500_, 0, v___x_1495_);
                    v___x_1503_ = v___x_1500_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1504_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 3, v___x_1498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_r_1440_);
                    v___x_1503_ = v_reuseFailAlloc_1504_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1503_;
            }
            34 => {
                v_k_1525_ = leanh::lean_ctor_get(v_l_1518_, 1);
                v_v_1526_ = leanh::lean_ctor_get(v_l_1518_, 2);
                v_isSharedCheck_1540_ = (!leanh::lean_is_exclusive(v_l_1518_)) as u8;
                if v_isSharedCheck_1540_ == 0 {
                    v_unused_1541_ = leanh::lean_ctor_get(v_l_1518_, 4);
                    leanh::lean_dec(v_unused_1541_);
                    v_unused_1542_ = leanh::lean_ctor_get(v_l_1518_, 3);
                    leanh::lean_dec(v_unused_1542_);
                    v_unused_1543_ = leanh::lean_ctor_get(v_l_1518_, 0);
                    leanh::lean_dec(v_unused_1543_);
                    v___x_1528_ = v_l_1518_;
                    v_isShared_1529_ = v_isSharedCheck_1540_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1526_);
                    leanh::lean_inc(v_k_1525_);
                    leanh::lean_dec(v_l_1518_);
                    v___x_1528_ = leanh::lean_box(0);
                    v_isShared_1529_ = v_isSharedCheck_1540_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1530_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_1519_, 2);
                if v_isShared_1529_ == 0 {
                    leanh::lean_ctor_set(v___x_1528_, 4, v_r_1519_);
                    leanh::lean_ctor_set(v___x_1528_, 3, v_r_1519_);
                    leanh::lean_ctor_set(v___x_1528_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v___x_1528_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v___x_1528_, 0, v___x_1434_);
                    v___x_1532_ = v___x_1528_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_r_1519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1519_);
                    v___x_1532_ = v_reuseFailAlloc_1539_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_1519_);
                if v_isShared_1524_ == 0 {
                    leanh::lean_ctor_set(v___x_1523_, 3, v_r_1519_);
                    leanh::lean_ctor_set(v___x_1523_, 0, v___x_1434_);
                    v___x_1534_ = v___x_1523_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1520_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_r_1519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_r_1519_);
                    v___x_1534_ = v_reuseFailAlloc_1538_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1290_ == 0 {
                    leanh::lean_ctor_set(v___x_1289_, 4, v___x_1534_);
                    leanh::lean_ctor_set(v___x_1289_, 3, v___x_1532_);
                    leanh::lean_ctor_set(v___x_1289_, 2, v_v_1526_);
                    leanh::lean_ctor_set(v___x_1289_, 1, v_k_1525_);
                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1530_);
                    v___x_1536_ = v___x_1289_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1526_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 3, v___x_1532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 4, v___x_1534_);
                    v___x_1536_ = v_reuseFailAlloc_1537_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1536_;
            }
            39 => {
                v___x_1553_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1552_ == 0 {
                    leanh::lean_ctor_set(v___x_1551_, 4, v_l_1518_);
                    leanh::lean_ctor_set(v___x_1551_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v___x_1551_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v___x_1551_, 0, v___x_1434_);
                    v___x_1555_ = v___x_1551_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_l_1518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_l_1518_);
                    v___x_1555_ = v_reuseFailAlloc_1559_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1290_ == 0 {
                    leanh::lean_ctor_set(v___x_1289_, 4, v_r_1547_);
                    leanh::lean_ctor_set(v___x_1289_, 3, v___x_1555_);
                    leanh::lean_ctor_set(v___x_1289_, 2, v_v_1549_);
                    leanh::lean_ctor_set(v___x_1289_, 1, v_k_1548_);
                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1553_);
                    v___x_1557_ = v___x_1289_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 3, v___x_1555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1547_);
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
    mut v_items_1571_: *mut leanh::LeanObject,
    mut v_cmp_1572_: *mut leanh::LeanObject,
    mut v_n_1573_: *mut leanh::LeanObject,
    mut v_j_1574_: *mut leanh::LeanObject,
    mut v_a_1575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1577_: u8 = 0;
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1576_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1577_ = lean_nat_dec_eq(v_j_1574_, v_zero_1576_);
                if v_isZero_1577_ == 1 {
                    leanh::lean_dec(v_j_1574_);
                    leanh::lean_dec_ref(v_cmp_1572_);
                    return v_a_1575_;
                } else {
                    v___x_1578_ = lean_nat_sub(v_n_1573_, v_j_1574_);
                    v___x_1579_ = lean_array_fget_borrowed(v_items_1571_, v___x_1578_);
                    v_fst_1580_ = leanh::lean_ctor_get(v___x_1579_, 0);
                    v_one_1581_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1582_ = lean_nat_sub(v_j_1574_, v_one_1581_);
                    leanh::lean_dec(v_j_1574_);
                    leanh::lean_inc(v_fst_1580_);
                    leanh::lean_inc_ref(v_cmp_1572_);
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
    mut v_items_1585_: *mut leanh::LeanObject,
    mut v_cmp_1586_: *mut leanh::LeanObject,
    mut v_n_1587_: *mut leanh::LeanObject,
    mut v_j_1588_: *mut leanh::LeanObject,
    mut v_a_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1585_, v_cmp_1586_, v_n_1587_, v_j_1588_, v_a_1589_);
    leanh::lean_dec(v_n_1587_);
    leanh::lean_dec_ref(v_items_1585_);
    return v_res_1590_;
}
pub unsafe fn l_Lake_Toml_RBDict_ofArray___redArg(
    mut v_cmp_1591_: *mut leanh::LeanObject,
    mut v_items_1592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_array_get_size(v_items_1592_);
    v___x_1594_ = leanh::lean_box(1);
    v_indices_1595_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1592_, v_cmp_1591_, v___x_1593_, v___x_1593_, v___x_1594_);
    v___x_1596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1596_, 0, v_items_1592_);
    leanh::lean_ctor_set(v___x_1596_, 1, v_indices_1595_);
    return v___x_1596_;
}
pub unsafe fn l_Lake_Toml_RBDict_ofArray(
    mut v_00_u03b1_1597_: *mut leanh::LeanObject,
    mut v_00_u03b2_1598_: *mut leanh::LeanObject,
    mut v_cmp_1599_: *mut leanh::LeanObject,
    mut v_items_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lake_Toml_RBDict_ofArray___redArg(v_cmp_1599_, v_items_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0(
    mut v_00_u03b1_1602_: *mut leanh::LeanObject,
    mut v_cmp_1603_: *mut leanh::LeanObject,
    mut v_00_u03b2_1604_: *mut leanh::LeanObject,
    mut v_k_1605_: *mut leanh::LeanObject,
    mut v_v_1606_: *mut leanh::LeanObject,
    mut v_t_1607_: *mut leanh::LeanObject,
    mut v_hl_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1610_: *mut leanh::LeanObject,
    mut v_00_u03b2_1611_: *mut leanh::LeanObject,
    mut v_items_1612_: *mut leanh::LeanObject,
    mut v_cmp_1613_: *mut leanh::LeanObject,
    mut v_n_1614_: *mut leanh::LeanObject,
    mut v_j_1615_: *mut leanh::LeanObject,
    mut v_a_1616_: *mut leanh::LeanObject,
    mut v_a_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1612_, v_cmp_1613_, v_n_1614_, v_j_1615_, v_a_1617_);
    return v___x_1618_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___boxed(
    mut v_00_u03b1_1619_: *mut leanh::LeanObject,
    mut v_00_u03b2_1620_: *mut leanh::LeanObject,
    mut v_items_1621_: *mut leanh::LeanObject,
    mut v_cmp_1622_: *mut leanh::LeanObject,
    mut v_n_1623_: *mut leanh::LeanObject,
    mut v_j_1624_: *mut leanh::LeanObject,
    mut v_a_1625_: *mut leanh::LeanObject,
    mut v_a_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_n_1623_);
    leanh::lean_dec_ref(v_items_1621_);
    return v_res_1627_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___redArg(
    mut v_inst_1628_: *mut leanh::LeanObject,
    mut v_self_1629_: *mut leanh::LeanObject,
    mut v_other_1630_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_items_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    v_items_1631_ = leanh::lean_ctor_get(v_self_1629_, 0);
    v_items_1632_ = leanh::lean_ctor_get(v_other_1630_, 0);
    v___x_1633_ = lean_array_get_size(v_items_1631_);
    v___x_1634_ = lean_array_get_size(v_items_1632_);
    v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
    if v___x_1635_ == 0 {
        leanh::lean_dec_ref(v_inst_1628_);
        return v___x_1635_;
    } else {
        let mut v___x_1636_: u8 = 0;
        v___x_1636_ =
            l_Array_isEqvAux___redArg(v_items_1631_, v_items_1632_, v_inst_1628_, v___x_1633_);
        return v___x_1636_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_beq___redArg___boxed(
    mut v_inst_1637_: *mut leanh::LeanObject,
    mut v_self_1638_: *mut leanh::LeanObject,
    mut v_other_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1640_: u8 = 0;
    let mut v_r_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_1637_, v_self_1638_, v_other_1639_);
    leanh::lean_dec_ref(v_other_1639_);
    leanh::lean_dec_ref(v_self_1638_);
    v_r_1641_ = leanh::lean_box((v_res_1640_) as usize);
    return v_r_1641_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq(
    mut v_00_u03b1_1642_: *mut leanh::LeanObject,
    mut v_00_u03b2_1643_: *mut leanh::LeanObject,
    mut v_cmp_1644_: *mut leanh::LeanObject,
    mut v_inst_1645_: *mut leanh::LeanObject,
    mut v_self_1646_: *mut leanh::LeanObject,
    mut v_other_1647_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1648_: u8 = 0;
    v___x_1648_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_1645_, v_self_1646_, v_other_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___boxed(
    mut v_00_u03b1_1649_: *mut leanh::LeanObject,
    mut v_00_u03b2_1650_: *mut leanh::LeanObject,
    mut v_cmp_1651_: *mut leanh::LeanObject,
    mut v_inst_1652_: *mut leanh::LeanObject,
    mut v_self_1653_: *mut leanh::LeanObject,
    mut v_other_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: u8 = 0;
    let mut v_r_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l_Lake_Toml_RBDict_beq(
        v_00_u03b1_1649_,
        v_00_u03b2_1650_,
        v_cmp_1651_,
        v_inst_1652_,
        v_self_1653_,
        v_other_1654_,
    );
    leanh::lean_dec_ref(v_other_1654_);
    leanh::lean_dec_ref(v_self_1653_);
    leanh::lean_dec_ref(v_cmp_1651_);
    v_r_1656_ = leanh::lean_box((v_res_1655_) as usize);
    return v_r_1656_;
}
pub unsafe fn l_Lake_Toml_RBDict_instBEqOfProd___redArg(
    mut v_cmp_1657_: *mut leanh::LeanObject,
    mut v_inst_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___x_1659_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1659_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1659_, 2, v_cmp_1657_);
    leanh::lean_closure_set(v___x_1659_, 3, v_inst_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Lake_Toml_RBDict_instBEqOfProd(
    mut v_00_u03b1_1660_: *mut leanh::LeanObject,
    mut v_00_u03b2_1661_: *mut leanh::LeanObject,
    mut v_cmp_1662_: *mut leanh::LeanObject,
    mut v_inst_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___x_1664_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1664_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1664_, 2, v_cmp_1662_);
    leanh::lean_closure_set(v___x_1664_, 3, v_inst_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___redArg(
    mut v_t_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_items_1666_ = leanh::lean_ctor_get(v_t_1665_, 0);
    v___x_1667_ = lean_array_get_size(v_items_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___redArg___boxed(
    mut v_t_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_Lake_Toml_RBDict_size___redArg(v_t_1668_);
    leanh::lean_dec_ref(v_t_1668_);
    return v_res_1669_;
}
pub unsafe fn l_Lake_Toml_RBDict_size(
    mut v_00_u03b1_1670_: *mut leanh::LeanObject,
    mut v_00_u03b2_1671_: *mut leanh::LeanObject,
    mut v_cmp_1672_: *mut leanh::LeanObject,
    mut v_t_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_items_1674_ = leanh::lean_ctor_get(v_t_1673_, 0);
    v___x_1675_ = lean_array_get_size(v_items_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___boxed(
    mut v_00_u03b1_1676_: *mut leanh::LeanObject,
    mut v_00_u03b2_1677_: *mut leanh::LeanObject,
    mut v_cmp_1678_: *mut leanh::LeanObject,
    mut v_t_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1680_ =
        l_Lake_Toml_RBDict_size(v_00_u03b1_1676_, v_00_u03b2_1677_, v_cmp_1678_, v_t_1679_);
    leanh::lean_dec_ref(v_t_1679_);
    leanh::lean_dec_ref(v_cmp_1678_);
    return v_res_1680_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___redArg(
    mut v_t_1681_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_items_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v_items_1682_ = leanh::lean_ctor_get(v_t_1681_, 0);
    v___x_1683_ = lean_array_get_size(v_items_1682_);
    v___x_1684_ = leanh::lean_unsigned_to_nat(0);
    v___x_1685_ = lean_nat_dec_eq(v___x_1683_, v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___redArg___boxed(
    mut v_t_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1687_: u8 = 0;
    let mut v_r_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lake_Toml_RBDict_isEmpty___redArg(v_t_1686_);
    leanh::lean_dec_ref(v_t_1686_);
    v_r_1688_ = leanh::lean_box((v_res_1687_) as usize);
    return v_r_1688_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty(
    mut v_00_u03b1_1689_: *mut leanh::LeanObject,
    mut v_00_u03b2_1690_: *mut leanh::LeanObject,
    mut v_cmp_1691_: *mut leanh::LeanObject,
    mut v_t_1692_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_items_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    v_items_1693_ = leanh::lean_ctor_get(v_t_1692_, 0);
    v___x_1694_ = lean_array_get_size(v_items_1693_);
    v___x_1695_ = leanh::lean_unsigned_to_nat(0);
    v___x_1696_ = lean_nat_dec_eq(v___x_1694_, v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___boxed(
    mut v_00_u03b1_1697_: *mut leanh::LeanObject,
    mut v_00_u03b2_1698_: *mut leanh::LeanObject,
    mut v_cmp_1699_: *mut leanh::LeanObject,
    mut v_t_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1701_: u8 = 0;
    let mut v_r_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ =
        l_Lake_Toml_RBDict_isEmpty(v_00_u03b1_1697_, v_00_u03b2_1698_, v_cmp_1699_, v_t_1700_);
    leanh::lean_dec_ref(v_t_1700_);
    leanh::lean_dec_ref(v_cmp_1699_);
    v_r_1702_ = leanh::lean_box((v_res_1701_) as usize);
    return v_r_1702_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(
    mut v_sz_1703_: usize,
    mut v_i_1704_: usize,
    mut v_bs_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: u8 = 0;
    let mut v_v_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: usize = 0;
    let mut v___x_1712_: usize = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1706_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
                if v___x_1706_ == 0 {
                    return v_bs_1705_;
                } else {
                    v_v_1707_ = lean_array_uget_borrowed(v_bs_1705_, v_i_1704_);
                    v_fst_1708_ = leanh::lean_ctor_get(v_v_1707_, 0);
                    leanh::lean_inc(v_fst_1708_);
                    v___x_1709_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1715_: *mut leanh::LeanObject,
    mut v_i_1716_: *mut leanh::LeanObject,
    mut v_bs_1717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1718_: usize = 0;
    let mut v_i_boxed_1719_: usize = 0;
    let mut v_res_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1718_ = leanh::lean_unbox_usize(v_sz_1715_);
    leanh::lean_dec(v_sz_1715_);
    v_i_boxed_1719_ = leanh::lean_unbox_usize(v_i_1716_);
    leanh::lean_dec(v_i_1716_);
    v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
    return v_res_1720_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys___redArg(
    mut v_t_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1723_: usize = 0;
    let mut v___x_1724_: usize = 0;
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_items_1722_ = leanh::lean_ctor_get(v_t_1721_, 0);
    leanh::lean_inc_ref(v_items_1722_);
    leanh::lean_dec_ref(v_t_1721_);
    v_sz_1723_ = lean_array_size(v_items_1722_);
    v___x_1724_ = 0usize;
    v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_1723_, v___x_1724_, v_items_1722_);
    return v___x_1725_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys(
    mut v_00_u03b1_1726_: *mut leanh::LeanObject,
    mut v_00_u03b2_1727_: *mut leanh::LeanObject,
    mut v_cmp_1728_: *mut leanh::LeanObject,
    mut v_t_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Lake_Toml_RBDict_keys___redArg(v_t_1729_);
    return v___x_1730_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys___boxed(
    mut v_00_u03b1_1731_: *mut leanh::LeanObject,
    mut v_00_u03b2_1732_: *mut leanh::LeanObject,
    mut v_cmp_1733_: *mut leanh::LeanObject,
    mut v_t_1734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1735_ =
        l_Lake_Toml_RBDict_keys(v_00_u03b1_1731_, v_00_u03b2_1732_, v_cmp_1733_, v_t_1734_);
    leanh::lean_dec_ref(v_cmp_1733_);
    return v_res_1735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(
    mut v_00_u03b1_1736_: *mut leanh::LeanObject,
    mut v_00_u03b2_1737_: *mut leanh::LeanObject,
    mut v_sz_1738_: usize,
    mut v_i_1739_: usize,
    mut v_bs_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_1738_, v_i_1739_, v_bs_1740_);
    return v___x_1741_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___boxed(
    mut v_00_u03b1_1742_: *mut leanh::LeanObject,
    mut v_00_u03b2_1743_: *mut leanh::LeanObject,
    mut v_sz_1744_: *mut leanh::LeanObject,
    mut v_i_1745_: *mut leanh::LeanObject,
    mut v_bs_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1747_: usize = 0;
    let mut v_i_boxed_1748_: usize = 0;
    let mut v_res_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1747_ = leanh::lean_unbox_usize(v_sz_1744_);
    leanh::lean_dec(v_sz_1744_);
    v_i_boxed_1748_ = leanh::lean_unbox_usize(v_i_1745_);
    leanh::lean_dec(v_i_1745_);
    v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(v_00_u03b1_1742_, v_00_u03b2_1743_, v_sz_boxed_1747_, v_i_boxed_1748_, v_bs_1746_);
    return v_res_1749_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(
    mut v_sz_1750_: usize,
    mut v_i_1751_: usize,
    mut v_bs_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1753_: u8 = 0;
    let mut v_v_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1753_ = lean_usize_dec_lt(v_i_1751_, v_sz_1750_);
                if v___x_1753_ == 0 {
                    return v_bs_1752_;
                } else {
                    v_v_1754_ = lean_array_uget_borrowed(v_bs_1752_, v_i_1751_);
                    v_snd_1755_ = leanh::lean_ctor_get(v_v_1754_, 1);
                    leanh::lean_inc(v_snd_1755_);
                    v___x_1756_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1762_: *mut leanh::LeanObject,
    mut v_i_1763_: *mut leanh::LeanObject,
    mut v_bs_1764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1765_: usize = 0;
    let mut v_i_boxed_1766_: usize = 0;
    let mut v_res_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1765_ = leanh::lean_unbox_usize(v_sz_1762_);
    leanh::lean_dec(v_sz_1762_);
    v_i_boxed_1766_ = leanh::lean_unbox_usize(v_i_1763_);
    leanh::lean_dec(v_i_1763_);
    v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_boxed_1765_, v_i_boxed_1766_, v_bs_1764_);
    return v_res_1767_;
}
pub unsafe fn l_Lake_Toml_RBDict_values___redArg(
    mut v_t_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1770_: usize = 0;
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_items_1769_ = leanh::lean_ctor_get(v_t_1768_, 0);
    leanh::lean_inc_ref(v_items_1769_);
    leanh::lean_dec_ref(v_t_1768_);
    v_sz_1770_ = lean_array_size(v_items_1769_);
    v___x_1771_ = 0usize;
    v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_1770_, v___x_1771_, v_items_1769_);
    return v___x_1772_;
}
pub unsafe fn l_Lake_Toml_RBDict_values(
    mut v_00_u03b1_1773_: *mut leanh::LeanObject,
    mut v_00_u03b2_1774_: *mut leanh::LeanObject,
    mut v_cmp_1775_: *mut leanh::LeanObject,
    mut v_t_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lake_Toml_RBDict_values___redArg(v_t_1776_);
    return v___x_1777_;
}
pub unsafe fn l_Lake_Toml_RBDict_values___boxed(
    mut v_00_u03b1_1778_: *mut leanh::LeanObject,
    mut v_00_u03b2_1779_: *mut leanh::LeanObject,
    mut v_cmp_1780_: *mut leanh::LeanObject,
    mut v_t_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ =
        l_Lake_Toml_RBDict_values(v_00_u03b1_1778_, v_00_u03b2_1779_, v_cmp_1780_, v_t_1781_);
    leanh::lean_dec_ref(v_cmp_1780_);
    return v_res_1782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(
    mut v_00_u03b1_1783_: *mut leanh::LeanObject,
    mut v_00_u03b2_1784_: *mut leanh::LeanObject,
    mut v_sz_1785_: usize,
    mut v_i_1786_: usize,
    mut v_bs_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_1785_, v_i_1786_, v_bs_1787_);
    return v___x_1788_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___boxed(
    mut v_00_u03b1_1789_: *mut leanh::LeanObject,
    mut v_00_u03b2_1790_: *mut leanh::LeanObject,
    mut v_sz_1791_: *mut leanh::LeanObject,
    mut v_i_1792_: *mut leanh::LeanObject,
    mut v_bs_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1794_: usize = 0;
    let mut v_i_boxed_1795_: usize = 0;
    let mut v_res_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1794_ = leanh::lean_unbox_usize(v_sz_1791_);
    leanh::lean_dec(v_sz_1791_);
    v_i_boxed_1795_ = leanh::lean_unbox_usize(v_i_1792_);
    leanh::lean_dec(v_i_1792_);
    v_res_1796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(v_00_u03b1_1789_, v_00_u03b2_1790_, v_sz_boxed_1794_, v_i_boxed_1795_, v_bs_1793_);
    return v_res_1796_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
    mut v_cmp_1797_: *mut leanh::LeanObject,
    mut v_k_1798_: *mut leanh::LeanObject,
    mut v_t_1799_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1799_) == 0 {
                    v_k_1800_ = leanh::lean_ctor_get(v_t_1799_, 1);
                    leanh::lean_inc(v_k_1800_);
                    v_l_1801_ = leanh::lean_ctor_get(v_t_1799_, 3);
                    leanh::lean_inc(v_l_1801_);
                    v_r_1802_ = leanh::lean_ctor_get(v_t_1799_, 4);
                    leanh::lean_inc(v_r_1802_);
                    leanh::lean_dec_ref_known(v_t_1799_, 5);
                    leanh::lean_inc_ref(v_cmp_1797_);
                    leanh::lean_inc(v_k_1798_);
                    v___x_1803_ = leanh::lean_apply_2(v_cmp_1797_, v_k_1798_, v_k_1800_);
                    v___x_1804_ = (leanh::lean_unbox(v___x_1803_) as u8);
                    match v___x_1804_ {
                        0 => {
                            leanh::lean_dec(v_r_1802_);
                            v_t_1799_ = v_l_1801_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_dec(v_r_1802_);
                            leanh::lean_dec(v_l_1801_);
                            leanh::lean_dec(v_k_1798_);
                            leanh::lean_dec_ref(v_cmp_1797_);
                            v___x_1806_ = 1;
                            return v___x_1806_;
                        }
                        _ => {
                            leanh::lean_dec(v_l_1801_);
                            v_t_1799_ = v_r_1802_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_k_1798_);
                    leanh::lean_dec_ref(v_cmp_1797_);
                    v___x_1808_ = 0;
                    return v___x_1808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg___boxed(
    mut v_cmp_1809_: *mut leanh::LeanObject,
    mut v_k_1810_: *mut leanh::LeanObject,
    mut v_t_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1812_: u8 = 0;
    let mut v_r_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1809_,
            v_k_1810_,
            v_t_1811_,
        );
    v_r_1813_ = leanh::lean_box((v_res_1812_) as usize);
    return v_r_1813_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___redArg(
    mut v_cmp_1814_: *mut leanh::LeanObject,
    mut v_k_1815_: *mut leanh::LeanObject,
    mut v_t_1816_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_indices_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    v_indices_1817_ = leanh::lean_ctor_get(v_t_1816_, 1);
    leanh::lean_inc(v_indices_1817_);
    leanh::lean_dec_ref(v_t_1816_);
    v___x_1818_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1814_,
            v_k_1815_,
            v_indices_1817_,
        );
    return v___x_1818_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___redArg___boxed(
    mut v_cmp_1819_: *mut leanh::LeanObject,
    mut v_k_1820_: *mut leanh::LeanObject,
    mut v_t_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1822_: u8 = 0;
    let mut v_r_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_1819_, v_k_1820_, v_t_1821_);
    v_r_1823_ = leanh::lean_box((v_res_1822_) as usize);
    return v_r_1823_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains(
    mut v_00_u03b1_1824_: *mut leanh::LeanObject,
    mut v_00_u03b2_1825_: *mut leanh::LeanObject,
    mut v_cmp_1826_: *mut leanh::LeanObject,
    mut v_k_1827_: *mut leanh::LeanObject,
    mut v_t_1828_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1829_: u8 = 0;
    v___x_1829_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_1826_, v_k_1827_, v_t_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___boxed(
    mut v_00_u03b1_1830_: *mut leanh::LeanObject,
    mut v_00_u03b2_1831_: *mut leanh::LeanObject,
    mut v_cmp_1832_: *mut leanh::LeanObject,
    mut v_k_1833_: *mut leanh::LeanObject,
    mut v_t_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1835_: u8 = 0;
    let mut v_r_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lake_Toml_RBDict_contains(
        v_00_u03b1_1830_,
        v_00_u03b2_1831_,
        v_cmp_1832_,
        v_k_1833_,
        v_t_1834_,
    );
    v_r_1836_ = leanh::lean_box((v_res_1835_) as usize);
    return v_r_1836_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(
    mut v_00_u03b1_1837_: *mut leanh::LeanObject,
    mut v_cmp_1838_: *mut leanh::LeanObject,
    mut v_00_u03b2_1839_: *mut leanh::LeanObject,
    mut v_k_1840_: *mut leanh::LeanObject,
    mut v_t_1841_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_1843_: *mut leanh::LeanObject,
    mut v_cmp_1844_: *mut leanh::LeanObject,
    mut v_00_u03b2_1845_: *mut leanh::LeanObject,
    mut v_k_1846_: *mut leanh::LeanObject,
    mut v_t_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1848_: u8 = 0;
    let mut v_r_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(
        v_00_u03b1_1843_,
        v_cmp_1844_,
        v_00_u03b2_1845_,
        v_k_1846_,
        v_t_1847_,
    );
    v_r_1849_ = leanh::lean_box((v_res_1848_) as usize);
    return v_r_1849_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(
    mut v_cmp_1850_: *mut leanh::LeanObject,
    mut v_t_1851_: *mut leanh::LeanObject,
    mut v_k_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: u8 = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1851_) == 0 {
                    v_k_1853_ = leanh::lean_ctor_get(v_t_1851_, 1);
                    leanh::lean_inc(v_k_1853_);
                    v_v_1854_ = leanh::lean_ctor_get(v_t_1851_, 2);
                    leanh::lean_inc(v_v_1854_);
                    v_l_1855_ = leanh::lean_ctor_get(v_t_1851_, 3);
                    leanh::lean_inc(v_l_1855_);
                    v_r_1856_ = leanh::lean_ctor_get(v_t_1851_, 4);
                    leanh::lean_inc(v_r_1856_);
                    leanh::lean_dec_ref_known(v_t_1851_, 5);
                    leanh::lean_inc_ref(v_cmp_1850_);
                    leanh::lean_inc(v_k_1852_);
                    v___x_1857_ = leanh::lean_apply_2(v_cmp_1850_, v_k_1852_, v_k_1853_);
                    v___x_1858_ = (leanh::lean_unbox(v___x_1857_) as u8);
                    match v___x_1858_ {
                        0 => {
                            leanh::lean_dec(v_r_1856_);
                            leanh::lean_dec(v_v_1854_);
                            v_t_1851_ = v_l_1855_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_dec(v_r_1856_);
                            leanh::lean_dec(v_l_1855_);
                            leanh::lean_dec(v_k_1852_);
                            leanh::lean_dec_ref(v_cmp_1850_);
                            v___x_1860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1860_, 0, v_v_1854_);
                            return v___x_1860_;
                        }
                        _ => {
                            leanh::lean_dec(v_l_1855_);
                            leanh::lean_dec(v_v_1854_);
                            v_t_1851_ = v_r_1856_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_k_1852_);
                    leanh::lean_dec_ref(v_cmp_1850_);
                    v___x_1862_ = leanh::lean_box(0);
                    return v___x_1862_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_findIdx_x3f___redArg(
    mut v_cmp_1863_: *mut leanh::LeanObject,
    mut v_k_1864_: *mut leanh::LeanObject,
    mut v_t_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_1866_ = leanh::lean_ctor_get(v_t_1865_, 0);
                leanh::lean_inc_ref(v_items_1866_);
                v_indices_1867_ = leanh::lean_ctor_get(v_t_1865_, 1);
                leanh::lean_inc(v_indices_1867_);
                leanh::lean_dec_ref(v_t_1865_);
                v___x_1868_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_1863_, v_indices_1867_, v_k_1864_);
                if leanh::lean_obj_tag(v___x_1868_) == 0 {
                    leanh::lean_dec_ref(v_items_1866_);
                    v___x_1869_ = leanh::lean_box(0);
                    return v___x_1869_;
                } else {
                    v_val_1870_ = leanh::lean_ctor_get(v___x_1868_, 0);
                    v_isSharedCheck_1880_ = (!leanh::lean_is_exclusive(v___x_1868_)) as u8;
                    if v_isSharedCheck_1880_ == 0 {
                        v___x_1872_ = v___x_1868_;
                        v_isShared_1873_ = v_isSharedCheck_1880_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1870_);
                        leanh::lean_dec(v___x_1868_);
                        v___x_1872_ = leanh::lean_box(0);
                        v_isShared_1873_ = v_isSharedCheck_1880_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1874_ = lean_array_get_size(v_items_1866_);
                leanh::lean_dec_ref(v_items_1866_);
                v___x_1875_ = lean_nat_dec_lt(v_val_1870_, v___x_1874_);
                if v___x_1875_ == 0 {
                    leanh::lean_del_object(v___x_1872_);
                    leanh::lean_dec(v_val_1870_);
                    v___x_1876_ = leanh::lean_box(0);
                    return v___x_1876_;
                } else {
                    if v_isShared_1873_ == 0 {
                        v___x_1878_ = v___x_1872_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_val_1870_);
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
    mut v_00_u03b1_1881_: *mut leanh::LeanObject,
    mut v_00_u03b2_1882_: *mut leanh::LeanObject,
    mut v_cmp_1883_: *mut leanh::LeanObject,
    mut v_k_1884_: *mut leanh::LeanObject,
    mut v_t_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1886_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1883_, v_k_1884_, v_t_1885_);
    return v___x_1886_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0(
    mut v_00_u03b1_1887_: *mut leanh::LeanObject,
    mut v_cmp_1888_: *mut leanh::LeanObject,
    mut v_00_u03b4_1889_: *mut leanh::LeanObject,
    mut v_t_1890_: *mut leanh::LeanObject,
    mut v_k_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_1888_, v_t_1890_, v_k_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lake_Toml_RBDict_findEntry_x3f___redArg(
    mut v_cmp_1893_: *mut leanh::LeanObject,
    mut v_k_1894_: *mut leanh::LeanObject,
    mut v_t_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v_items_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_t_1895_);
                v___x_1896_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1893_, v_k_1894_, v_t_1895_);
                if leanh::lean_obj_tag(v___x_1896_) == 0 {
                    leanh::lean_dec_ref(v_t_1895_);
                    v___x_1897_ = leanh::lean_box(0);
                    return v___x_1897_;
                } else {
                    v_val_1898_ = leanh::lean_ctor_get(v___x_1896_, 0);
                    v_isSharedCheck_1907_ = (!leanh::lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1907_ == 0 {
                        v___x_1900_ = v___x_1896_;
                        v_isShared_1901_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1898_);
                        leanh::lean_dec(v___x_1896_);
                        v___x_1900_ = leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_items_1902_ = leanh::lean_ctor_get(v_t_1895_, 0);
                leanh::lean_inc_ref(v_items_1902_);
                leanh::lean_dec_ref(v_t_1895_);
                v___x_1903_ = lean_array_fget(v_items_1902_, v_val_1898_);
                leanh::lean_dec(v_val_1898_);
                leanh::lean_dec_ref(v_items_1902_);
                if v_isShared_1901_ == 0 {
                    leanh::lean_ctor_set(v___x_1900_, 0, v___x_1903_);
                    v___x_1905_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
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
    mut v_00_u03b1_1908_: *mut leanh::LeanObject,
    mut v_00_u03b2_1909_: *mut leanh::LeanObject,
    mut v_cmp_1910_: *mut leanh::LeanObject,
    mut v_k_1911_: *mut leanh::LeanObject,
    mut v_t_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1910_, v_k_1911_, v_t_1912_);
    return v___x_1913_;
}
pub unsafe fn l_Lake_Toml_RBDict_find_x3f___redArg(
    mut v_cmp_1914_: *mut leanh::LeanObject,
    mut v_k_1915_: *mut leanh::LeanObject,
    mut v_t_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v_snd_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1914_, v_k_1915_, v_t_1916_);
                if leanh::lean_obj_tag(v___x_1917_) == 0 {
                    v___x_1918_ = leanh::lean_box(0);
                    return v___x_1918_;
                } else {
                    v_val_1919_ = leanh::lean_ctor_get(v___x_1917_, 0);
                    v_isSharedCheck_1927_ = (!leanh::lean_is_exclusive(v___x_1917_)) as u8;
                    if v_isSharedCheck_1927_ == 0 {
                        v___x_1921_ = v___x_1917_;
                        v_isShared_1922_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1919_);
                        leanh::lean_dec(v___x_1917_);
                        v___x_1921_ = leanh::lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1923_ = leanh::lean_ctor_get(v_val_1919_, 1);
                leanh::lean_inc(v_snd_1923_);
                leanh::lean_dec(v_val_1919_);
                if v_isShared_1922_ == 0 {
                    leanh::lean_ctor_set(v___x_1921_, 0, v_snd_1923_);
                    v___x_1925_ = v___x_1921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1926_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_snd_1923_);
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
    mut v_00_u03b1_1928_: *mut leanh::LeanObject,
    mut v_00_u03b2_1929_: *mut leanh::LeanObject,
    mut v_cmp_1930_: *mut leanh::LeanObject,
    mut v_k_1931_: *mut leanh::LeanObject,
    mut v_t_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v_snd_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1933_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1930_, v_k_1931_, v_t_1932_);
                if leanh::lean_obj_tag(v___x_1933_) == 0 {
                    v___x_1934_ = leanh::lean_box(0);
                    return v___x_1934_;
                } else {
                    v_val_1935_ = leanh::lean_ctor_get(v___x_1933_, 0);
                    v_isSharedCheck_1943_ = (!leanh::lean_is_exclusive(v___x_1933_)) as u8;
                    if v_isSharedCheck_1943_ == 0 {
                        v___x_1937_ = v___x_1933_;
                        v_isShared_1938_ = v_isSharedCheck_1943_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1935_);
                        leanh::lean_dec(v___x_1933_);
                        v___x_1937_ = leanh::lean_box(0);
                        v_isShared_1938_ = v_isSharedCheck_1943_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1939_ = leanh::lean_ctor_get(v_val_1935_, 1);
                leanh::lean_inc(v_snd_1939_);
                leanh::lean_dec(v_val_1935_);
                if v_isShared_1938_ == 0 {
                    leanh::lean_ctor_set(v___x_1937_, 0, v_snd_1939_);
                    v___x_1941_ = v___x_1937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_snd_1939_);
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
    mut v_cmp_1944_: *mut leanh::LeanObject,
    mut v_k_1945_: *mut leanh::LeanObject,
    mut v_v_1946_: *mut leanh::LeanObject,
    mut v_t_1947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_1948_ = leanh::lean_ctor_get(v_t_1947_, 0);
                v_indices_1949_ = leanh::lean_ctor_get(v_t_1947_, 1);
                v_isSharedCheck_1960_ = (!leanh::lean_is_exclusive(v_t_1947_)) as u8;
                if v_isSharedCheck_1960_ == 0 {
                    v___x_1951_ = v_t_1947_;
                    v_isShared_1952_ = v_isSharedCheck_1960_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indices_1949_);
                    leanh::lean_inc(v_items_1948_);
                    leanh::lean_dec(v_t_1947_);
                    v___x_1951_ = leanh::lean_box(0);
                    v_isShared_1952_ = v_isSharedCheck_1960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_k_1945_);
                v___x_1953_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1953_, 0, v_k_1945_);
                leanh::lean_ctor_set(v___x_1953_, 1, v_v_1946_);
                leanh::lean_inc_ref(v_items_1948_);
                v___x_1954_ = lean_array_push(v_items_1948_, v___x_1953_);
                v___x_1955_ = lean_array_get_size(v_items_1948_);
                leanh::lean_dec_ref(v_items_1948_);
                v___x_1956_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1944_, v_k_1945_, v___x_1955_, v_indices_1949_);
                if v_isShared_1952_ == 0 {
                    leanh::lean_ctor_set(v___x_1951_, 1, v___x_1956_);
                    leanh::lean_ctor_set(v___x_1951_, 0, v___x_1954_);
                    v___x_1958_ = v___x_1951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1956_);
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
    mut v_00_u03b1_1961_: *mut leanh::LeanObject,
    mut v_00_u03b2_1962_: *mut leanh::LeanObject,
    mut v_cmp_1963_: *mut leanh::LeanObject,
    mut v_k_1964_: *mut leanh::LeanObject,
    mut v_v_1965_: *mut leanh::LeanObject,
    mut v_t_1966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1967_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1963_, v_k_1964_, v_v_1965_, v_t_1966_);
    return v___x_1967_;
}
pub unsafe fn l_Lake_Toml_RBDict_alter___redArg(
    mut v_cmp_1968_: *mut leanh::LeanObject,
    mut v_k_1969_: *mut leanh::LeanObject,
    mut v_f_1970_: *mut leanh::LeanObject,
    mut v_t_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v_items_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_t_1971_);
                leanh::lean_inc(v_k_1969_);
                leanh::lean_inc_ref(v_cmp_1968_);
                v___x_1972_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1968_, v_k_1969_, v_t_1971_);
                if leanh::lean_obj_tag(v___x_1972_) == 1 {
                    leanh::lean_dec(v_k_1969_);
                    leanh::lean_dec_ref(v_cmp_1968_);
                    v_val_1973_ = leanh::lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_2008_ = (!leanh::lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_1975_ = v___x_1972_;
                        v_isShared_1976_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1973_);
                        leanh::lean_dec(v___x_1972_);
                        v___x_1975_ = leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1972_);
                    v___x_2009_ = leanh::lean_box(0);
                    v___x_2010_ = leanh::lean_apply_1(v_f_1970_, v___x_2009_);
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
                v_items_1977_ = leanh::lean_ctor_get(v_t_1971_, 0);
                v_indices_1978_ = leanh::lean_ctor_get(v_t_1971_, 1);
                v_isSharedCheck_2007_ = (!leanh::lean_is_exclusive(v_t_1971_)) as u8;
                if v_isSharedCheck_2007_ == 0 {
                    v___x_1980_ = v_t_1971_;
                    v_isShared_1981_ = v_isSharedCheck_2007_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_indices_1978_);
                    leanh::lean_inc(v_items_1977_);
                    leanh::lean_dec(v_t_1971_);
                    v___x_1980_ = leanh::lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_2007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1982_ = lean_array_get_size(v_items_1977_);
                v___x_1983_ = lean_nat_dec_lt(v_val_1973_, v___x_1982_);
                if v___x_1983_ == 0 {
                    leanh::lean_del_object(v___x_1975_);
                    leanh::lean_dec(v_val_1973_);
                    leanh::lean_dec(v_f_1970_);
                    if v_isShared_1981_ == 0 {
                        v___x_1985_ = v___x_1980_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1986_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_items_1977_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_indices_1978_);
                        v___x_1985_ = v_reuseFailAlloc_1986_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_v_1987_ = lean_array_fget(v_items_1977_, v_val_1973_);
                    v_fst_1988_ = leanh::lean_ctor_get(v_v_1987_, 0);
                    v_snd_1989_ = leanh::lean_ctor_get(v_v_1987_, 1);
                    v_isSharedCheck_2006_ = (!leanh::lean_is_exclusive(v_v_1987_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v___x_1991_ = v_v_1987_;
                        v_isShared_1992_ = v_isSharedCheck_2006_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1989_);
                        leanh::lean_inc(v_fst_1988_);
                        leanh::lean_dec(v_v_1987_);
                        v___x_1991_ = leanh::lean_box(0);
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
                v___x_1993_ = leanh::lean_box(0);
                v_xs_x27_1994_ = lean_array_fset(v_items_1977_, v_val_1973_, v___x_1993_);
                if v_isShared_1976_ == 0 {
                    leanh::lean_ctor_set(v___x_1975_, 0, v_snd_1989_);
                    v___x_1996_ = v___x_1975_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_snd_1989_);
                    v___x_1996_ = v_reuseFailAlloc_2005_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1997_ = leanh::lean_apply_1(v_f_1970_, v___x_1996_);
                if v_isShared_1992_ == 0 {
                    leanh::lean_ctor_set(v___x_1991_, 1, v___x_1997_);
                    v___x_1999_ = v___x_1991_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_fst_1988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1997_);
                    v___x_1999_ = v_reuseFailAlloc_2004_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2000_ = lean_array_fset(v_xs_x27_1994_, v_val_1973_, v___x_1999_);
                leanh::lean_dec(v_val_1973_);
                if v_isShared_1981_ == 0 {
                    leanh::lean_ctor_set(v___x_1980_, 0, v___x_2000_);
                    v___x_2002_ = v___x_1980_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_indices_1978_);
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
    mut v_00_u03b1_2012_: *mut leanh::LeanObject,
    mut v_00_u03b2_2013_: *mut leanh::LeanObject,
    mut v_cmp_2014_: *mut leanh::LeanObject,
    mut v_k_2015_: *mut leanh::LeanObject,
    mut v_f_2016_: *mut leanh::LeanObject,
    mut v_t_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2018_ = l_Lake_Toml_RBDict_alter___redArg(v_cmp_2014_, v_k_2015_, v_f_2016_, v_t_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Lake_Toml_RBDict_insert___redArg(
    mut v_cmp_2019_: *mut leanh::LeanObject,
    mut v_k_2020_: *mut leanh::LeanObject,
    mut v_v_2021_: *mut leanh::LeanObject,
    mut v_t_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_t_2022_);
                leanh::lean_inc(v_k_2020_);
                leanh::lean_inc_ref(v_cmp_2019_);
                v___x_2023_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_2019_, v_k_2020_, v_t_2022_);
                if leanh::lean_obj_tag(v___x_2023_) == 1 {
                    v_val_2024_ = leanh::lean_ctor_get(v___x_2023_, 0);
                    leanh::lean_inc(v_val_2024_);
                    leanh::lean_dec_ref_known(v___x_2023_, 1);
                    v_items_2025_ = leanh::lean_ctor_get(v_t_2022_, 0);
                    v_indices_2026_ = leanh::lean_ctor_get(v_t_2022_, 1);
                    v___x_2027_ = lean_array_get_size(v_items_2025_);
                    v___x_2028_ = lean_nat_dec_lt(v_val_2024_, v___x_2027_);
                    if v___x_2028_ == 0 {
                        leanh::lean_dec(v_val_2024_);
                        v___x_2029_ = l_Lake_Toml_RBDict_push___redArg(
                            v_cmp_2019_,
                            v_k_2020_,
                            v_v_2021_,
                            v_t_2022_,
                        );
                        return v___x_2029_;
                    } else {
                        leanh::lean_inc(v_indices_2026_);
                        leanh::lean_inc_ref(v_items_2025_);
                        leanh::lean_dec_ref(v_cmp_2019_);
                        v_isSharedCheck_2038_ = (!leanh::lean_is_exclusive(v_t_2022_)) as u8;
                        if v_isSharedCheck_2038_ == 0 {
                            v_unused_2039_ = leanh::lean_ctor_get(v_t_2022_, 1);
                            leanh::lean_dec(v_unused_2039_);
                            v_unused_2040_ = leanh::lean_ctor_get(v_t_2022_, 0);
                            leanh::lean_dec(v_unused_2040_);
                            v___x_2031_ = v_t_2022_;
                            v_isShared_2032_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_t_2022_);
                            v___x_2031_ = leanh::lean_box(0);
                            v_isShared_2032_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2023_);
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
                v___x_2033_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2033_, 0, v_k_2020_);
                leanh::lean_ctor_set(v___x_2033_, 1, v_v_2021_);
                v___x_2034_ = lean_array_fset(v_items_2025_, v_val_2024_, v___x_2033_);
                leanh::lean_dec(v_val_2024_);
                if v_isShared_2032_ == 0 {
                    leanh::lean_ctor_set(v___x_2031_, 0, v___x_2034_);
                    v___x_2036_ = v___x_2031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_indices_2026_);
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
    mut v_00_u03b1_2042_: *mut leanh::LeanObject,
    mut v_00_u03b2_2043_: *mut leanh::LeanObject,
    mut v_cmp_2044_: *mut leanh::LeanObject,
    mut v_k_2045_: *mut leanh::LeanObject,
    mut v_v_2046_: *mut leanh::LeanObject,
    mut v_t_2047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_2044_, v_k_2045_, v_v_2046_, v_t_2047_);
    return v___x_2048_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(
    mut v_cmp_2049_: *mut leanh::LeanObject,
    mut v_as_2050_: *mut leanh::LeanObject,
    mut v_i_2051_: usize,
    mut v_stop_2052_: usize,
    mut v_b_2053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2054_ = lean_usize_dec_eq(v_i_2051_, v_stop_2052_);
                if v___x_2054_ == 0 {
                    v___x_2055_ = lean_array_uget_borrowed(v_as_2050_, v_i_2051_);
                    v_fst_2056_ = leanh::lean_ctor_get(v___x_2055_, 0);
                    v_snd_2057_ = leanh::lean_ctor_get(v___x_2055_, 1);
                    leanh::lean_inc(v_snd_2057_);
                    leanh::lean_inc(v_fst_2056_);
                    leanh::lean_inc_ref(v_cmp_2049_);
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
                    leanh::lean_dec_ref(v_cmp_2049_);
                    return v_b_2053_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg___boxed(
    mut v_cmp_2062_: *mut leanh::LeanObject,
    mut v_as_2063_: *mut leanh::LeanObject,
    mut v_i_2064_: *mut leanh::LeanObject,
    mut v_stop_2065_: *mut leanh::LeanObject,
    mut v_b_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2067_: usize = 0;
    let mut v_stop_boxed_2068_: usize = 0;
    let mut v_res_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2067_ = leanh::lean_unbox_usize(v_i_2064_);
    leanh::lean_dec(v_i_2064_);
    v_stop_boxed_2068_ = leanh::lean_unbox_usize(v_stop_2065_);
    leanh::lean_dec(v_stop_2065_);
    v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2062_, v_as_2063_, v_i_boxed_2067_, v_stop_boxed_2068_, v_b_2066_);
    leanh::lean_dec_ref(v_as_2063_);
    return v_res_2069_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___redArg(
    mut v_cmp_2070_: *mut leanh::LeanObject,
    mut v_self_2071_: *mut leanh::LeanObject,
    mut v_other_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    v___x_2073_ = leanh::lean_unsigned_to_nat(0);
    v___x_2074_ = lean_array_get_size(v_other_2072_);
    v___x_2075_ = lean_nat_dec_lt(v___x_2073_, v___x_2074_);
    if v___x_2075_ == 0 {
        leanh::lean_dec_ref(v_cmp_2070_);
        return v_self_2071_;
    } else {
        let mut v___x_2076_: u8 = 0;
        v___x_2076_ = lean_nat_dec_le(v___x_2074_, v___x_2074_);
        if v___x_2076_ == 0 {
            if v___x_2075_ == 0 {
                leanh::lean_dec_ref(v_cmp_2070_);
                return v_self_2071_;
            } else {
                let mut v___x_2077_: usize = 0;
                let mut v___x_2078_: usize = 0;
                let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2077_ = 0usize;
                v___x_2078_ = lean_usize_of_nat(v___x_2074_);
                v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2070_, v_other_2072_, v___x_2077_, v___x_2078_, v_self_2071_);
                return v___x_2079_;
            }
        } else {
            let mut v___x_2080_: usize = 0;
            let mut v___x_2081_: usize = 0;
            let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2080_ = 0usize;
            v___x_2081_ = lean_usize_of_nat(v___x_2074_);
            v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2070_, v_other_2072_, v___x_2080_, v___x_2081_, v_self_2071_);
            return v___x_2082_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___redArg___boxed(
    mut v_cmp_2083_: *mut leanh::LeanObject,
    mut v_self_2084_: *mut leanh::LeanObject,
    mut v_other_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2086_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2083_, v_self_2084_, v_other_2085_);
    leanh::lean_dec_ref(v_other_2085_);
    return v_res_2086_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray(
    mut v_00_u03b1_2087_: *mut leanh::LeanObject,
    mut v_00_u03b2_2088_: *mut leanh::LeanObject,
    mut v_cmp_2089_: *mut leanh::LeanObject,
    mut v_self_2090_: *mut leanh::LeanObject,
    mut v_other_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2089_, v_self_2090_, v_other_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___boxed(
    mut v_00_u03b1_2093_: *mut leanh::LeanObject,
    mut v_00_u03b2_2094_: *mut leanh::LeanObject,
    mut v_cmp_2095_: *mut leanh::LeanObject,
    mut v_self_2096_: *mut leanh::LeanObject,
    mut v_other_2097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lake_Toml_RBDict_appendArray(
        v_00_u03b1_2093_,
        v_00_u03b2_2094_,
        v_cmp_2095_,
        v_self_2096_,
        v_other_2097_,
    );
    leanh::lean_dec_ref(v_other_2097_);
    return v_res_2098_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(
    mut v_00_u03b1_2099_: *mut leanh::LeanObject,
    mut v_00_u03b2_2100_: *mut leanh::LeanObject,
    mut v_cmp_2101_: *mut leanh::LeanObject,
    mut v_as_2102_: *mut leanh::LeanObject,
    mut v_i_2103_: usize,
    mut v_stop_2104_: usize,
    mut v_b_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2101_, v_as_2102_, v_i_2103_, v_stop_2104_, v_b_2105_);
    return v___x_2106_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___boxed(
    mut v_00_u03b1_2107_: *mut leanh::LeanObject,
    mut v_00_u03b2_2108_: *mut leanh::LeanObject,
    mut v_cmp_2109_: *mut leanh::LeanObject,
    mut v_as_2110_: *mut leanh::LeanObject,
    mut v_i_2111_: *mut leanh::LeanObject,
    mut v_stop_2112_: *mut leanh::LeanObject,
    mut v_b_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2114_: usize = 0;
    let mut v_stop_boxed_2115_: usize = 0;
    let mut v_res_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2114_ = leanh::lean_unbox_usize(v_i_2111_);
    leanh::lean_dec(v_i_2111_);
    v_stop_boxed_2115_ = leanh::lean_unbox_usize(v_stop_2112_);
    leanh::lean_dec(v_stop_2112_);
    v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(v_00_u03b1_2107_, v_00_u03b2_2108_, v_cmp_2109_, v_as_2110_, v_i_boxed_2114_, v_stop_boxed_2115_, v_b_2113_);
    leanh::lean_dec_ref(v_as_2110_);
    return v_res_2116_;
}
pub unsafe fn l_Lake_Toml_RBDict_instHAppendArrayProd___redArg(
    mut v_cmp_2117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_appendArray___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_2118_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2118_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2118_, 2, v_cmp_2117_);
    return v___x_2118_;
}
pub unsafe fn l_Lake_Toml_RBDict_instHAppendArrayProd(
    mut v_00_u03b1_2119_: *mut leanh::LeanObject,
    mut v_00_u03b2_2120_: *mut leanh::LeanObject,
    mut v_cmp_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_appendArray___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_2122_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2122_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2122_, 2, v_cmp_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___redArg(
    mut v_cmp_2123_: *mut leanh::LeanObject,
    mut v_self_2124_: *mut leanh::LeanObject,
    mut v_other_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_items_2126_ = leanh::lean_ctor_get(v_other_2125_, 0);
    v___x_2127_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2123_, v_self_2124_, v_items_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___redArg___boxed(
    mut v_cmp_2128_: *mut leanh::LeanObject,
    mut v_self_2129_: *mut leanh::LeanObject,
    mut v_other_2130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2131_ = l_Lake_Toml_RBDict_append___redArg(v_cmp_2128_, v_self_2129_, v_other_2130_);
    leanh::lean_dec_ref(v_other_2130_);
    return v_res_2131_;
}
pub unsafe fn l_Lake_Toml_RBDict_append(
    mut v_00_u03b1_2132_: *mut leanh::LeanObject,
    mut v_00_u03b2_2133_: *mut leanh::LeanObject,
    mut v_cmp_2134_: *mut leanh::LeanObject,
    mut v_self_2135_: *mut leanh::LeanObject,
    mut v_other_2136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_items_2137_ = leanh::lean_ctor_get(v_other_2136_, 0);
    v___x_2138_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2134_, v_self_2135_, v_items_2137_);
    return v___x_2138_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___boxed(
    mut v_00_u03b1_2139_: *mut leanh::LeanObject,
    mut v_00_u03b2_2140_: *mut leanh::LeanObject,
    mut v_cmp_2141_: *mut leanh::LeanObject,
    mut v_self_2142_: *mut leanh::LeanObject,
    mut v_other_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lake_Toml_RBDict_append(
        v_00_u03b1_2139_,
        v_00_u03b2_2140_,
        v_cmp_2141_,
        v_self_2142_,
        v_other_2143_,
    );
    leanh::lean_dec_ref(v_other_2143_);
    return v_res_2144_;
}
pub unsafe fn l_Lake_Toml_RBDict_instAppend___redArg(
    mut v_cmp_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_append___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_2146_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2146_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2146_, 2, v_cmp_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Lake_Toml_RBDict_instAppend(
    mut v_00_u03b1_2147_: *mut leanh::LeanObject,
    mut v_00_u03b2_2148_: *mut leanh::LeanObject,
    mut v_cmp_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_append___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_2150_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2150_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2150_, 2, v_cmp_2149_);
    return v___x_2150_;
}
pub unsafe fn l_Lake_Toml_RBDict_map___redArg___lam__0(
    mut v_f_2151_: *mut leanh::LeanObject,
    mut v_x_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2157_: u8 = 0;
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2153_ = leanh::lean_ctor_get(v_x_2152_, 0);
                v_snd_2154_ = leanh::lean_ctor_get(v_x_2152_, 1);
                v_isSharedCheck_2162_ = (!leanh::lean_is_exclusive(v_x_2152_)) as u8;
                if v_isSharedCheck_2162_ == 0 {
                    v___x_2156_ = v_x_2152_;
                    v_isShared_2157_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2154_);
                    leanh::lean_inc(v_fst_2153_);
                    leanh::lean_dec(v_x_2152_);
                    v___x_2156_ = leanh::lean_box(0);
                    v_isShared_2157_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_fst_2153_);
                v___x_2158_ = leanh::lean_apply_2(v_f_2151_, v_fst_2153_, v_snd_2154_);
                if v_isShared_2157_ == 0 {
                    leanh::lean_ctor_set(v___x_2156_, 1, v___x_2158_);
                    v___x_2160_ = v___x_2156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_fst_2153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2158_);
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
    mut v_f_2182_: *mut leanh::LeanObject,
    mut v_t_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___f_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2191_: usize = 0;
    let mut v___x_2192_: usize = 0;
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_2184_ = leanh::lean_ctor_get(v_t_2183_, 0);
                v_indices_2185_ = leanh::lean_ctor_get(v_t_2183_, 1);
                v_isSharedCheck_2197_ = (!leanh::lean_is_exclusive(v_t_2183_)) as u8;
                if v_isSharedCheck_2197_ == 0 {
                    v___x_2187_ = v_t_2183_;
                    v_isShared_2188_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indices_2185_);
                    leanh::lean_inc(v_items_2184_);
                    leanh::lean_dec(v_t_2183_);
                    v___x_2187_ = leanh::lean_box(0);
                    v_isShared_2188_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2189_ = leanh::lean_alloc_closure(
                    l_Lake_Toml_RBDict_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2189_, 0, v_f_2182_);
                v___x_2190_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
                v_sz_2191_ = lean_array_size(v_items_2184_);
                v___x_2192_ = 0usize;
                v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2190_,
                    v___f_2189_,
                    v_sz_2191_,
                    v___x_2192_,
                    v_items_2184_,
                );
                if v_isShared_2188_ == 0 {
                    leanh::lean_ctor_set(v___x_2187_, 0, v___x_2193_);
                    v___x_2195_ = v___x_2187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_indices_2185_);
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
    mut v_00_u03b1_2198_: *mut leanh::LeanObject,
    mut v_00_u03b2_2199_: *mut leanh::LeanObject,
    mut v_00_u03b3_2200_: *mut leanh::LeanObject,
    mut v_cmp_2201_: *mut leanh::LeanObject,
    mut v_f_2202_: *mut leanh::LeanObject,
    mut v_t_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2208_: u8 = 0;
    let mut v___f_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2211_: usize = 0;
    let mut v___x_2212_: usize = 0;
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_2204_ = leanh::lean_ctor_get(v_t_2203_, 0);
                v_indices_2205_ = leanh::lean_ctor_get(v_t_2203_, 1);
                v_isSharedCheck_2217_ = (!leanh::lean_is_exclusive(v_t_2203_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v___x_2207_ = v_t_2203_;
                    v_isShared_2208_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indices_2205_);
                    leanh::lean_inc(v_items_2204_);
                    leanh::lean_dec(v_t_2203_);
                    v___x_2207_ = leanh::lean_box(0);
                    v_isShared_2208_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2209_ = leanh::lean_alloc_closure(
                    l_Lake_Toml_RBDict_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2209_, 0, v_f_2202_);
                v___x_2210_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
                v_sz_2211_ = lean_array_size(v_items_2204_);
                v___x_2212_ = 0usize;
                v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2210_,
                    v___f_2209_,
                    v_sz_2211_,
                    v___x_2212_,
                    v_items_2204_,
                );
                if v_isShared_2208_ == 0 {
                    leanh::lean_ctor_set(v___x_2207_, 0, v___x_2213_);
                    v___x_2215_ = v___x_2207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_indices_2205_);
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
    mut v_00_u03b1_2218_: *mut leanh::LeanObject,
    mut v_00_u03b2_2219_: *mut leanh::LeanObject,
    mut v_00_u03b3_2220_: *mut leanh::LeanObject,
    mut v_cmp_2221_: *mut leanh::LeanObject,
    mut v_f_2222_: *mut leanh::LeanObject,
    mut v_t_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Lake_Toml_RBDict_map(
        v_00_u03b1_2218_,
        v_00_u03b2_2219_,
        v_00_u03b3_2220_,
        v_cmp_2221_,
        v_f_2222_,
        v_t_2223_,
    );
    leanh::lean_dec_ref(v_cmp_2221_);
    return v_res_2224_;
}
pub unsafe fn l_Lake_Toml_RBDict_filter___redArg___lam__0(
    mut v_p_2225_: *mut leanh::LeanObject,
    mut v_cmp_2226_: *mut leanh::LeanObject,
    mut v_x1_2227_: *mut leanh::LeanObject,
    mut v_x2_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    v_fst_2229_ = leanh::lean_ctor_get(v_x2_2228_, 0);
    leanh::lean_inc_n(v_fst_2229_, 2);
    v_snd_2230_ = leanh::lean_ctor_get(v_x2_2228_, 1);
    leanh::lean_inc_n(v_snd_2230_, 2);
    leanh::lean_dec_ref(v_x2_2228_);
    v___x_2231_ = leanh::lean_apply_2(v_p_2225_, v_fst_2229_, v_snd_2230_);
    v___x_2232_ = (leanh::lean_unbox(v___x_2231_) as u8);
    if v___x_2232_ == 0 {
        leanh::lean_dec(v_snd_2230_);
        leanh::lean_dec(v_fst_2229_);
        leanh::lean_dec_ref(v_cmp_2226_);
        return v_x1_2227_;
    } else {
        let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2233_ =
            l_Lake_Toml_RBDict_push___redArg(v_cmp_2226_, v_fst_2229_, v_snd_2230_, v_x1_2227_);
        return v___x_2233_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filter___redArg(
    mut v_cmp_2234_: *mut leanh::LeanObject,
    mut v_p_2235_: *mut leanh::LeanObject,
    mut v_t_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    v_items_2237_ = leanh::lean_ctor_get(v_t_2236_, 0);
    leanh::lean_inc_ref(v_items_2237_);
    leanh::lean_dec_ref(v_t_2236_);
    v___x_2238_ = l_Lake_Toml_RBDict_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_2234_,
    );
    v___x_2239_ = leanh::lean_unsigned_to_nat(0);
    v___x_2240_ = lean_array_get_size(v_items_2237_);
    v___x_2241_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2242_ = lean_nat_dec_lt(v___x_2239_, v___x_2240_);
    if v___x_2242_ == 0 {
        leanh::lean_dec_ref(v_items_2237_);
        leanh::lean_dec_ref(v_p_2235_);
        leanh::lean_dec_ref(v_cmp_2234_);
        return v___x_2238_;
    } else {
        let mut v___f_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: u8 = 0;
        v___f_2243_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filter___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2243_, 0, v_p_2235_);
        leanh::lean_closure_set(v___f_2243_, 1, v_cmp_2234_);
        v___x_2244_ = lean_nat_dec_le(v___x_2240_, v___x_2240_);
        if v___x_2244_ == 0 {
            if v___x_2242_ == 0 {
                leanh::lean_dec_ref(v___f_2243_);
                leanh::lean_dec_ref(v_items_2237_);
                return v___x_2238_;
            } else {
                let mut v___x_2245_: usize = 0;
                let mut v___x_2246_: usize = 0;
                let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2245_ = 0usize;
                v___x_2246_ = lean_usize_of_nat(v___x_2240_);
                v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2248_ = 0usize;
            v___x_2249_ = lean_usize_of_nat(v___x_2240_);
            v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_2251_: *mut leanh::LeanObject,
    mut v_00_u03b2_2252_: *mut leanh::LeanObject,
    mut v_cmp_2253_: *mut leanh::LeanObject,
    mut v_p_2254_: *mut leanh::LeanObject,
    mut v_t_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    v_items_2256_ = leanh::lean_ctor_get(v_t_2255_, 0);
    leanh::lean_inc_ref(v_items_2256_);
    leanh::lean_dec_ref(v_t_2255_);
    v___x_2257_ = l_Lake_Toml_RBDict_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_2253_,
    );
    v___x_2258_ = leanh::lean_unsigned_to_nat(0);
    v___x_2259_ = lean_array_get_size(v_items_2256_);
    v___x_2260_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2261_ = lean_nat_dec_lt(v___x_2258_, v___x_2259_);
    if v___x_2261_ == 0 {
        leanh::lean_dec_ref(v_items_2256_);
        leanh::lean_dec_ref(v_p_2254_);
        leanh::lean_dec_ref(v_cmp_2253_);
        return v___x_2257_;
    } else {
        let mut v___f_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: u8 = 0;
        v___f_2262_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filter___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2262_, 0, v_p_2254_);
        leanh::lean_closure_set(v___f_2262_, 1, v_cmp_2253_);
        v___x_2263_ = lean_nat_dec_le(v___x_2259_, v___x_2259_);
        if v___x_2263_ == 0 {
            if v___x_2261_ == 0 {
                leanh::lean_dec_ref(v___f_2262_);
                leanh::lean_dec_ref(v_items_2256_);
                return v___x_2257_;
            } else {
                let mut v___x_2264_: usize = 0;
                let mut v___x_2265_: usize = 0;
                let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2264_ = 0usize;
                v___x_2265_ = lean_usize_of_nat(v___x_2259_);
                v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2267_ = 0usize;
            v___x_2268_ = lean_usize_of_nat(v___x_2259_);
            v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_f_2270_: *mut leanh::LeanObject,
    mut v_cmp_2271_: *mut leanh::LeanObject,
    mut v_x1_2272_: *mut leanh::LeanObject,
    mut v_x2_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2274_ = leanh::lean_ctor_get(v_x2_2273_, 0);
    leanh::lean_inc_n(v_fst_2274_, 2);
    v_snd_2275_ = leanh::lean_ctor_get(v_x2_2273_, 1);
    leanh::lean_inc(v_snd_2275_);
    leanh::lean_dec_ref(v_x2_2273_);
    v___x_2276_ = leanh::lean_apply_2(v_f_2270_, v_fst_2274_, v_snd_2275_);
    if leanh::lean_obj_tag(v___x_2276_) == 1 {
        let mut v_val_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2277_ = leanh::lean_ctor_get(v___x_2276_, 0);
        leanh::lean_inc(v_val_2277_);
        leanh::lean_dec_ref_known(v___x_2276_, 1);
        v___x_2278_ =
            l_Lake_Toml_RBDict_push___redArg(v_cmp_2271_, v_fst_2274_, v_val_2277_, v_x1_2272_);
        return v___x_2278_;
    } else {
        leanh::lean_dec(v___x_2276_);
        leanh::lean_dec(v_fst_2274_);
        leanh::lean_dec_ref(v_cmp_2271_);
        return v_x1_2272_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filterMap___redArg(
    mut v_cmp_2279_: *mut leanh::LeanObject,
    mut v_f_2280_: *mut leanh::LeanObject,
    mut v_t_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    v_items_2282_ = leanh::lean_ctor_get(v_t_2281_, 0);
    leanh::lean_inc_ref(v_items_2282_);
    leanh::lean_dec_ref(v_t_2281_);
    v___x_2283_ = l_Lake_Toml_RBDict_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_2279_,
    );
    v___x_2284_ = leanh::lean_unsigned_to_nat(0);
    v___x_2285_ = lean_array_get_size(v_items_2282_);
    v___x_2286_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2287_ = lean_nat_dec_lt(v___x_2284_, v___x_2285_);
    if v___x_2287_ == 0 {
        leanh::lean_dec_ref(v_items_2282_);
        leanh::lean_dec_ref(v_f_2280_);
        leanh::lean_dec_ref(v_cmp_2279_);
        return v___x_2283_;
    } else {
        let mut v___f_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: u8 = 0;
        v___f_2288_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filterMap___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2288_, 0, v_f_2280_);
        leanh::lean_closure_set(v___f_2288_, 1, v_cmp_2279_);
        v___x_2289_ = lean_nat_dec_le(v___x_2285_, v___x_2285_);
        if v___x_2289_ == 0 {
            if v___x_2287_ == 0 {
                leanh::lean_dec_ref(v___f_2288_);
                leanh::lean_dec_ref(v_items_2282_);
                return v___x_2283_;
            } else {
                let mut v___x_2290_: usize = 0;
                let mut v___x_2291_: usize = 0;
                let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2290_ = 0usize;
                v___x_2291_ = lean_usize_of_nat(v___x_2285_);
                v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2293_ = 0usize;
            v___x_2294_ = lean_usize_of_nat(v___x_2285_);
            v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_2296_: *mut leanh::LeanObject,
    mut v_00_u03b2_2297_: *mut leanh::LeanObject,
    mut v_00_u03b3_2298_: *mut leanh::LeanObject,
    mut v_cmp_2299_: *mut leanh::LeanObject,
    mut v_f_2300_: *mut leanh::LeanObject,
    mut v_t_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    v_items_2302_ = leanh::lean_ctor_get(v_t_2301_, 0);
    leanh::lean_inc_ref(v_items_2302_);
    leanh::lean_dec_ref(v_t_2301_);
    v___x_2303_ = l_Lake_Toml_RBDict_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_2299_,
    );
    v___x_2304_ = leanh::lean_unsigned_to_nat(0);
    v___x_2305_ = lean_array_get_size(v_items_2302_);
    v___x_2306_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2307_ = lean_nat_dec_lt(v___x_2304_, v___x_2305_);
    if v___x_2307_ == 0 {
        leanh::lean_dec_ref(v_items_2302_);
        leanh::lean_dec_ref(v_f_2300_);
        leanh::lean_dec_ref(v_cmp_2299_);
        return v___x_2303_;
    } else {
        let mut v___f_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: u8 = 0;
        v___f_2308_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filterMap___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2308_, 0, v_f_2300_);
        leanh::lean_closure_set(v___f_2308_, 1, v_cmp_2299_);
        v___x_2309_ = lean_nat_dec_le(v___x_2305_, v___x_2305_);
        if v___x_2309_ == 0 {
            if v___x_2307_ == 0 {
                leanh::lean_dec_ref(v___f_2308_);
                leanh::lean_dec_ref(v_items_2302_);
                return v___x_2303_;
            } else {
                let mut v___x_2310_: usize = 0;
                let mut v___x_2311_: usize = 0;
                let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2310_ = 0usize;
                v___x_2311_ = lean_usize_of_nat(v___x_2305_);
                v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2313_ = 0usize;
            v___x_2314_ = lean_usize_of_nat(v___x_2305_);
            v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_f_2316_: *mut leanh::LeanObject,
    mut v_s_2317_: *mut leanh::LeanObject,
    mut v_x_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2319_ = leanh::lean_ctor_get(v_x_2318_, 0);
    leanh::lean_inc(v_fst_2319_);
    v_snd_2320_ = leanh::lean_ctor_get(v_x_2318_, 1);
    leanh::lean_inc(v_snd_2320_);
    leanh::lean_dec_ref(v_x_2318_);
    v___x_2321_ = leanh::lean_apply_3(v_f_2316_, v_s_2317_, v_fst_2319_, v_snd_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lake_Toml_RBDict_foldM___redArg(
    mut v_inst_2322_: *mut leanh::LeanObject,
    mut v_f_2323_: *mut leanh::LeanObject,
    mut v_init_2324_: *mut leanh::LeanObject,
    mut v_t_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    v_items_2326_ = leanh::lean_ctor_get(v_t_2325_, 0);
    leanh::lean_inc_ref(v_items_2326_);
    leanh::lean_dec_ref(v_t_2325_);
    v___x_2327_ = leanh::lean_unsigned_to_nat(0);
    v___x_2328_ = lean_array_get_size(v_items_2326_);
    v___x_2329_ = lean_nat_dec_lt(v___x_2327_, v___x_2328_);
    if v___x_2329_ == 0 {
        let mut v_toApplicative_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_items_2326_);
        leanh::lean_dec(v_f_2323_);
        v_toApplicative_2330_ = leanh::lean_ctor_get(v_inst_2322_, 0);
        leanh::lean_inc_ref(v_toApplicative_2330_);
        leanh::lean_dec_ref(v_inst_2322_);
        v_toPure_2331_ = leanh::lean_ctor_get(v_toApplicative_2330_, 1);
        leanh::lean_inc(v_toPure_2331_);
        leanh::lean_dec_ref(v_toApplicative_2330_);
        v___x_2332_ =
            leanh::lean_apply_2(v_toPure_2331_, leanh::lean_box(0), v_init_2324_);
        return v___x_2332_;
    } else {
        let mut v___f_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        v___f_2333_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_2333_, 0, v_f_2323_);
        v___x_2334_ = lean_nat_dec_le(v___x_2328_, v___x_2328_);
        if v___x_2334_ == 0 {
            if v___x_2329_ == 0 {
                let mut v_toApplicative_2335_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2333_);
                leanh::lean_dec_ref(v_items_2326_);
                v_toApplicative_2335_ = leanh::lean_ctor_get(v_inst_2322_, 0);
                leanh::lean_inc_ref(v_toApplicative_2335_);
                leanh::lean_dec_ref(v_inst_2322_);
                v_toPure_2336_ = leanh::lean_ctor_get(v_toApplicative_2335_, 1);
                leanh::lean_inc(v_toPure_2336_);
                leanh::lean_dec_ref(v_toApplicative_2335_);
                v___x_2337_ = leanh::lean_apply_2(
                    v_toPure_2336_,
                    leanh::lean_box(0),
                    v_init_2324_,
                );
                return v___x_2337_;
            } else {
                let mut v___x_2338_: usize = 0;
                let mut v___x_2339_: usize = 0;
                let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2338_ = 0usize;
                v___x_2339_ = lean_usize_of_nat(v___x_2328_);
                v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2341_ = 0usize;
            v___x_2342_ = lean_usize_of_nat(v___x_2328_);
            v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_m_2344_: *mut leanh::LeanObject,
    mut v_00_u03c3_2345_: *mut leanh::LeanObject,
    mut v_00_u03b1_2346_: *mut leanh::LeanObject,
    mut v_00_u03b2_2347_: *mut leanh::LeanObject,
    mut v_cmp_2348_: *mut leanh::LeanObject,
    mut v_inst_2349_: *mut leanh::LeanObject,
    mut v_f_2350_: *mut leanh::LeanObject,
    mut v_init_2351_: *mut leanh::LeanObject,
    mut v_t_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_items_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    v_items_2353_ = leanh::lean_ctor_get(v_t_2352_, 0);
    leanh::lean_inc_ref(v_items_2353_);
    leanh::lean_dec_ref(v_t_2352_);
    v___x_2354_ = leanh::lean_unsigned_to_nat(0);
    v___x_2355_ = lean_array_get_size(v_items_2353_);
    v___x_2356_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
    if v___x_2356_ == 0 {
        let mut v_toApplicative_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_items_2353_);
        leanh::lean_dec(v_f_2350_);
        v_toApplicative_2357_ = leanh::lean_ctor_get(v_inst_2349_, 0);
        leanh::lean_inc_ref(v_toApplicative_2357_);
        leanh::lean_dec_ref(v_inst_2349_);
        v_toPure_2358_ = leanh::lean_ctor_get(v_toApplicative_2357_, 1);
        leanh::lean_inc(v_toPure_2358_);
        leanh::lean_dec_ref(v_toApplicative_2357_);
        v___x_2359_ =
            leanh::lean_apply_2(v_toPure_2358_, leanh::lean_box(0), v_init_2351_);
        return v___x_2359_;
    } else {
        let mut v___f_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2361_: u8 = 0;
        v___f_2360_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_2360_, 0, v_f_2350_);
        v___x_2361_ = lean_nat_dec_le(v___x_2355_, v___x_2355_);
        if v___x_2361_ == 0 {
            if v___x_2356_ == 0 {
                let mut v_toApplicative_2362_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2360_);
                leanh::lean_dec_ref(v_items_2353_);
                v_toApplicative_2362_ = leanh::lean_ctor_get(v_inst_2349_, 0);
                leanh::lean_inc_ref(v_toApplicative_2362_);
                leanh::lean_dec_ref(v_inst_2349_);
                v_toPure_2363_ = leanh::lean_ctor_get(v_toApplicative_2362_, 1);
                leanh::lean_inc(v_toPure_2363_);
                leanh::lean_dec_ref(v_toApplicative_2362_);
                v___x_2364_ = leanh::lean_apply_2(
                    v_toPure_2363_,
                    leanh::lean_box(0),
                    v_init_2351_,
                );
                return v___x_2364_;
            } else {
                let mut v___x_2365_: usize = 0;
                let mut v___x_2366_: usize = 0;
                let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2365_ = 0usize;
                v___x_2366_ = lean_usize_of_nat(v___x_2355_);
                v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2368_ = 0usize;
            v___x_2369_ = lean_usize_of_nat(v___x_2355_);
            v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_m_2371_: *mut leanh::LeanObject,
    mut v_00_u03c3_2372_: *mut leanh::LeanObject,
    mut v_00_u03b1_2373_: *mut leanh::LeanObject,
    mut v_00_u03b2_2374_: *mut leanh::LeanObject,
    mut v_cmp_2375_: *mut leanh::LeanObject,
    mut v_inst_2376_: *mut leanh::LeanObject,
    mut v_f_2377_: *mut leanh::LeanObject,
    mut v_init_2378_: *mut leanh::LeanObject,
    mut v_t_2379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_cmp_2375_);
    return v_res_2380_;
}
pub unsafe fn l_Lake_Toml_RBDict_fold___redArg(
    mut v_f_2381_: *mut leanh::LeanObject,
    mut v_init_2382_: *mut leanh::LeanObject,
    mut v_t_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    v___x_2384_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v_items_2385_ = leanh::lean_ctor_get(v_t_2383_, 0);
    leanh::lean_inc_ref(v_items_2385_);
    leanh::lean_dec_ref(v_t_2383_);
    v___x_2386_ = leanh::lean_unsigned_to_nat(0);
    v___x_2387_ = lean_array_get_size(v_items_2385_);
    v___x_2388_ = lean_nat_dec_lt(v___x_2386_, v___x_2387_);
    if v___x_2388_ == 0 {
        leanh::lean_dec_ref(v_items_2385_);
        leanh::lean_dec(v_f_2381_);
        return v_init_2382_;
    } else {
        let mut v___f_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: u8 = 0;
        v___f_2389_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_2389_, 0, v_f_2381_);
        v___x_2390_ = lean_nat_dec_le(v___x_2387_, v___x_2387_);
        if v___x_2390_ == 0 {
            if v___x_2388_ == 0 {
                leanh::lean_dec_ref(v___f_2389_);
                leanh::lean_dec_ref(v_items_2385_);
                return v_init_2382_;
            } else {
                let mut v___x_2391_: usize = 0;
                let mut v___x_2392_: usize = 0;
                let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2391_ = 0usize;
                v___x_2392_ = lean_usize_of_nat(v___x_2387_);
                v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2394_ = 0usize;
            v___x_2395_ = lean_usize_of_nat(v___x_2387_);
            v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03c3_2397_: *mut leanh::LeanObject,
    mut v_00_u03b1_2398_: *mut leanh::LeanObject,
    mut v_00_u03b2_2399_: *mut leanh::LeanObject,
    mut v_cmp_2400_: *mut leanh::LeanObject,
    mut v_f_2401_: *mut leanh::LeanObject,
    mut v_init_2402_: *mut leanh::LeanObject,
    mut v_t_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    v___x_2404_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v_items_2405_ = leanh::lean_ctor_get(v_t_2403_, 0);
    leanh::lean_inc_ref(v_items_2405_);
    leanh::lean_dec_ref(v_t_2403_);
    v___x_2406_ = leanh::lean_unsigned_to_nat(0);
    v___x_2407_ = lean_array_get_size(v_items_2405_);
    v___x_2408_ = lean_nat_dec_lt(v___x_2406_, v___x_2407_);
    if v___x_2408_ == 0 {
        leanh::lean_dec_ref(v_items_2405_);
        leanh::lean_dec(v_f_2401_);
        return v_init_2402_;
    } else {
        let mut v___f_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: u8 = 0;
        v___f_2409_ = leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_2409_, 0, v_f_2401_);
        v___x_2410_ = lean_nat_dec_le(v___x_2407_, v___x_2407_);
        if v___x_2410_ == 0 {
            if v___x_2408_ == 0 {
                leanh::lean_dec_ref(v___f_2409_);
                leanh::lean_dec_ref(v_items_2405_);
                return v_init_2402_;
            } else {
                let mut v___x_2411_: usize = 0;
                let mut v___x_2412_: usize = 0;
                let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2411_ = 0usize;
                v___x_2412_ = lean_usize_of_nat(v___x_2407_);
                v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2414_ = 0usize;
            v___x_2415_ = lean_usize_of_nat(v___x_2407_);
            v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03c3_2417_: *mut leanh::LeanObject,
    mut v_00_u03b1_2418_: *mut leanh::LeanObject,
    mut v_00_u03b2_2419_: *mut leanh::LeanObject,
    mut v_cmp_2420_: *mut leanh::LeanObject,
    mut v_f_2421_: *mut leanh::LeanObject,
    mut v_init_2422_: *mut leanh::LeanObject,
    mut v_t_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_Lake_Toml_RBDict_fold(
        v_00_u03c3_2417_,
        v_00_u03b1_2418_,
        v_00_u03b2_2419_,
        v_cmp_2420_,
        v_f_2421_,
        v_init_2422_,
        v_t_2423_,
    );
    leanh::lean_dec_ref(v_cmp_2420_);
    return v_res_2424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Dict(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Data_Dict(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_Data_Dict(builtin);
}
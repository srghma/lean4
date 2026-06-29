// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndCollect
// Imports: Lean.Meta.Tactic.Util Lean.Meta.Tactic.FunIndInfo
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_set, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_expr_eqv, lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_ptr_addr, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_mix_hash, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_uint64,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_filter, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_hash,
    l_Lean_Expr_isFVar, l_Lean_Expr_sort___override,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_isAuxDecl, l_Lean_LocalDecl_type, l_Lean_LocalDecl_value_x3f,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::FunIndInfo::{
    initialize_Lean_Meta_Tactic_FunIndInfo, runtime_initialize_Lean_Meta_Tactic_FunIndInfo,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_getType,
    runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::PtrSet::l_Lean_mkPtrSet___redArg;
pub static l_Lean_Meta_FunInd_instHashableCall___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_FunInd_instHashableCall_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_FunInd_instHashableCall___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instHashableCall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_FunInd_instHashableCall: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instHashableCall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_FunInd_instBEqCall___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_FunInd_instBEqCall_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_FunInd_instBEqCall___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instBEqCall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_FunInd_instBEqCall: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instBEqCall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0: u64 = 0;
static mut l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_Collector_visit___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_Collector_visit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_Collector_main___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_Collector_main___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_FunInd_instHashableCall_hash(
    mut v_x_1826_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_expr_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u64 = 0;
    let mut v___x_1830_: u64 = 0;
    let mut v___x_1831_: u64 = 0;
    let mut v___x_1832_: u64 = 0;
    let mut v___x_1833_: u64 = 0;
    v_expr_1827_ = crate::leanh::lean_ctor_get(v_x_1826_, 0);
    v_relevantArgs_1828_ = crate::leanh::lean_ctor_get(v_x_1826_, 1);
    v___x_1829_ = 0u64;
    v___x_1830_ = l_Lean_Expr_hash(v_expr_1827_);
    v___x_1831_ = lean_uint64_mix_hash(v___x_1829_, v___x_1830_);
    v___x_1832_ = l_Lean_Expr_hash(v_relevantArgs_1828_);
    v___x_1833_ = lean_uint64_mix_hash(v___x_1831_, v___x_1832_);
    return v___x_1833_;
}
pub unsafe fn l_Lean_Meta_FunInd_instHashableCall_hash___boxed(
    mut v_x_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1835_: u64 = 0;
    let mut v_r_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lean_Meta_FunInd_instHashableCall_hash(v_x_1834_);
    crate::leanh::lean_dec_ref(v_x_1834_);
    v_r_1836_ = crate::leanh::lean_box_uint64(v_res_1835_);
    return v_r_1836_;
}
pub unsafe fn l_Lean_Meta_FunInd_instBEqCall_beq(
    mut v_x_1839_: *mut crate::leanh::LeanObject,
    mut v_x_1840_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_expr_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    v_expr_1841_ = crate::leanh::lean_ctor_get(v_x_1839_, 0);
    v_relevantArgs_1842_ = crate::leanh::lean_ctor_get(v_x_1839_, 1);
    v_expr_1843_ = crate::leanh::lean_ctor_get(v_x_1840_, 0);
    v_relevantArgs_1844_ = crate::leanh::lean_ctor_get(v_x_1840_, 1);
    v___x_1845_ = lean_expr_eqv(v_expr_1841_, v_expr_1843_);
    if v___x_1845_ == 0 {
        return v___x_1845_;
    } else {
        let mut v___x_1846_: u8 = 0;
        v___x_1846_ = lean_expr_eqv(v_relevantArgs_1842_, v_relevantArgs_1844_);
        return v___x_1846_;
    }
}
pub unsafe fn l_Lean_Meta_FunInd_instBEqCall_beq___boxed(
    mut v_x_1847_: *mut crate::leanh::LeanObject,
    mut v_x_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1849_: u8 = 0;
    let mut v_r_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_Meta_FunInd_instBEqCall_beq(v_x_1847_, v_x_1848_);
    crate::leanh::lean_dec_ref(v_x_1848_);
    crate::leanh::lean_dec_ref(v_x_1847_);
    v_r_1850_ = crate::leanh::lean_box((v_res_1849_) as usize);
    return v_r_1850_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = crate::leanh::lean_box(0);
    v___x_1856_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1857_ = lean_mk_array(v___x_1856_, v___x_1855_);
    return v___x_1857_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1,
    );
    v___x_1859_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 1, v___x_1858_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2,
    );
    v___x_1862_ = l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0;
    v___x_1863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3,
    );
    return v___x_1864_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_isEmpty(
    mut v_sc_1865_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_calls_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    v_calls_1866_ = crate::leanh::lean_ctor_get(v_sc_1865_, 0);
    v___x_1867_ = lean_array_get_size(v_calls_1866_);
    v___x_1868_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1869_ = lean_nat_dec_eq(v___x_1867_, v___x_1868_);
    return v___x_1869_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(
    mut v_sc_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1871_: u8 = 0;
    let mut v_r_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_Meta_FunInd_SeenCalls_isEmpty(v_sc_1870_);
    crate::leanh::lean_dec_ref(v_sc_1870_);
    v_r_1872_ = crate::leanh::lean_box((v_res_1871_) as usize);
    return v_r_1872_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(
    mut v_xs_1873_: *mut crate::leanh::LeanObject,
    mut v_ys_1874_: *mut crate::leanh::LeanObject,
    mut v_x_1875_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1877_: u8 = 0;
    let mut v_one_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1876_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1877_ = lean_nat_dec_eq(v_x_1875_, v_zero_1876_);
                if v_isZero_1877_ == 1 {
                    crate::leanh::lean_dec(v_x_1875_);
                    return v_isZero_1877_;
                } else {
                    v_one_1878_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1879_ = lean_nat_sub(v_x_1875_, v_one_1878_);
                    crate::leanh::lean_dec(v_x_1875_);
                    v___x_1880_ = lean_array_fget_borrowed(v_xs_1873_, v_n_1879_);
                    v___x_1881_ = lean_array_fget_borrowed(v_ys_1874_, v_n_1879_);
                    v___x_1882_ = lean_expr_eqv(v___x_1880_, v___x_1881_);
                    if v___x_1882_ == 0 {
                        crate::leanh::lean_dec(v_n_1879_);
                        return v___x_1882_;
                    } else {
                        v_x_1875_ = v_n_1879_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_xs_1884_: *mut crate::leanh::LeanObject,
    mut v_ys_1885_: *mut crate::leanh::LeanObject,
    mut v_x_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1887_: u8 = 0;
    let mut v_r_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_1884_, v_ys_1885_, v_x_1886_);
    crate::leanh::lean_dec_ref(v_ys_1885_);
    crate::leanh::lean_dec_ref(v_xs_1884_);
    v_r_1888_ = crate::leanh::lean_box((v_res_1887_) as usize);
    return v_r_1888_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(
    mut v_a_1889_: *mut crate::leanh::LeanObject,
    mut v_x_1890_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1891_: u8 = 0;
    let mut v_key_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: u8 = 0;
    let mut v_fst_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1890_) == 0 {
                    v___x_1891_ = 0;
                    return v___x_1891_;
                } else {
                    v_key_1892_ = crate::leanh::lean_ctor_get(v_x_1890_, 0);
                    v_tail_1893_ = crate::leanh::lean_ctor_get(v_x_1890_, 2);
                    v_fst_1897_ = crate::leanh::lean_ctor_get(v_key_1892_, 0);
                    v_snd_1898_ = crate::leanh::lean_ctor_get(v_key_1892_, 1);
                    v_fst_1899_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                    v_snd_1900_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                    v___x_1901_ = lean_name_eq(v_fst_1897_, v_fst_1899_);
                    if v___x_1901_ == 0 {
                        v___y_1895_ = v___x_1901_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1902_ = lean_array_get_size(v_snd_1898_);
                        v___x_1903_ = lean_array_get_size(v_snd_1900_);
                        v___x_1904_ = lean_nat_dec_eq(v___x_1902_, v___x_1903_);
                        if v___x_1904_ == 0 {
                            v_x_1890_ = v_tail_1893_;
                            state = 0;
                            continue;
                        } else {
                            v___x_1906_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_snd_1898_, v_snd_1900_, v___x_1902_);
                            v___y_1895_ = v___x_1906_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_1895_ == 0 {
                    v_x_1890_ = v_tail_1893_;
                    state = 0;
                    continue;
                } else {
                    return v___y_1895_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg___boxed(
    mut v_a_1907_: *mut crate::leanh::LeanObject,
    mut v_x_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1909_: u8 = 0;
    let mut v_r_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_1907_, v_x_1908_);
    crate::leanh::lean_dec(v_x_1908_);
    crate::leanh::lean_dec_ref(v_a_1907_);
    v_r_1910_ = crate::leanh::lean_box((v_res_1909_) as usize);
    return v_r_1910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(
    mut v_as_1911_: *mut crate::leanh::LeanObject,
    mut v_i_1912_: usize,
    mut v_stop_1913_: usize,
    mut v_b_1914_: u64,
) -> u64 {
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u64 = 0;
    let mut v___x_1918_: u64 = 0;
    let mut v___x_1919_: usize = 0;
    let mut v___x_1920_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1915_ = lean_usize_dec_eq(v_i_1912_, v_stop_1913_);
                if v___x_1915_ == 0 {
                    v___x_1916_ = lean_array_uget_borrowed(v_as_1911_, v_i_1912_);
                    v___x_1917_ = l_Lean_Expr_hash(v___x_1916_);
                    v___x_1918_ = lean_uint64_mix_hash(v_b_1914_, v___x_1917_);
                    v___x_1919_ = 1usize;
                    v___x_1920_ = lean_usize_add(v_i_1912_, v___x_1919_);
                    v_i_1912_ = v___x_1920_;
                    v_b_1914_ = v___x_1918_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1914_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2___boxed(
    mut v_as_1922_: *mut crate::leanh::LeanObject,
    mut v_i_1923_: *mut crate::leanh::LeanObject,
    mut v_stop_1924_: *mut crate::leanh::LeanObject,
    mut v_b_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1926_: usize = 0;
    let mut v_stop_boxed_1927_: usize = 0;
    let mut v_b_boxed_1928_: u64 = 0;
    let mut v_res_1929_: u64 = 0;
    let mut v_r_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1926_ = crate::leanh::lean_unbox_usize(v_i_1923_);
    crate::leanh::lean_dec(v_i_1923_);
    v_stop_boxed_1927_ = crate::leanh::lean_unbox_usize(v_stop_1924_);
    crate::leanh::lean_dec(v_stop_1924_);
    v_b_boxed_1928_ = crate::leanh::lean_unbox_uint64(v_b_1925_);
    crate::leanh::lean_dec_ref(v_b_1925_);
    v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_as_1922_, v_i_boxed_1926_, v_stop_boxed_1927_, v_b_boxed_1928_);
    crate::leanh::lean_dec_ref(v_as_1922_);
    v_r_1930_ = crate::leanh::lean_box_uint64(v_res_1929_);
    return v_r_1930_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u64 = 0;
    v___x_1931_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1932_ = lean_uint64_of_nat(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(
    mut v_x_1933_: *mut crate::leanh::LeanObject,
    mut v_x_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v_fst_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1945_: u64 = 0;
    let mut v___y_1946_: u64 = 0;
    let mut v___x_1947_: u64 = 0;
    let mut v___x_1948_: u64 = 0;
    let mut v___x_1949_: u64 = 0;
    let mut v_fold_1950_: u64 = 0;
    let mut v___x_1951_: u64 = 0;
    let mut v___x_1952_: u64 = 0;
    let mut v___x_1953_: u64 = 0;
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: usize = 0;
    let mut v___x_1956_: usize = 0;
    let mut v___x_1957_: usize = 0;
    let mut v___x_1958_: usize = 0;
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1966_: u64 = 0;
    let mut v___x_1967_: u64 = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: u8 = 0;
    let mut v___x_1972_: usize = 0;
    let mut v___x_1973_: usize = 0;
    let mut v___x_1974_: u64 = 0;
    let mut v___x_1975_: usize = 0;
    let mut v___x_1976_: usize = 0;
    let mut v___x_1977_: u64 = 0;
    let mut v___x_1978_: u64 = 0;
    let mut v_hash_1979_: u64 = 0;
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1934_) == 0 {
                    return v_x_1933_;
                } else {
                    v_key_1935_ = crate::leanh::lean_ctor_get(v_x_1934_, 0);
                    v_value_1936_ = crate::leanh::lean_ctor_get(v_x_1934_, 1);
                    v_tail_1937_ = crate::leanh::lean_ctor_get(v_x_1934_, 2);
                    v_isSharedCheck_1980_ = (!crate::leanh::lean_is_exclusive(v_x_1934_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v___x_1939_ = v_x_1934_;
                        v_isShared_1940_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1937_);
                        crate::leanh::lean_inc(v_value_1936_);
                        crate::leanh::lean_inc(v_key_1935_);
                        crate::leanh::lean_dec(v_x_1934_);
                        v___x_1939_ = crate::leanh::lean_box(0);
                        v_isShared_1940_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1941_ = crate::leanh::lean_ctor_get(v_key_1935_, 0);
                v_snd_1942_ = crate::leanh::lean_ctor_get(v_key_1935_, 1);
                v___x_1943_ = lean_array_get_size(v_x_1933_);
                if crate::leanh::lean_obj_tag(v_fst_1941_) == 0 {
                    v___x_1978_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_1966_ = v___x_1978_;
                    state = 4;
                    continue;
                } else {
                    v_hash_1979_ = crate::leanh::lean_ctor_get_uint64(
                        v_fst_1941_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1966_ = v_hash_1979_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1947_ = lean_uint64_mix_hash(v___y_1945_, v___y_1946_);
                v___x_1948_ = 32u64;
                v___x_1949_ = lean_uint64_shift_right(v___x_1947_, v___x_1948_);
                v_fold_1950_ = lean_uint64_xor(v___x_1947_, v___x_1949_);
                v___x_1951_ = 16u64;
                v___x_1952_ = lean_uint64_shift_right(v_fold_1950_, v___x_1951_);
                v___x_1953_ = lean_uint64_xor(v_fold_1950_, v___x_1952_);
                v___x_1954_ = lean_uint64_to_usize(v___x_1953_);
                v___x_1955_ = lean_usize_of_nat(v___x_1943_);
                v___x_1956_ = 1usize;
                v___x_1957_ = lean_usize_sub(v___x_1955_, v___x_1956_);
                v___x_1958_ = lean_usize_land(v___x_1954_, v___x_1957_);
                v___x_1959_ = lean_array_uget_borrowed(v_x_1933_, v___x_1958_);
                crate::leanh::lean_inc(v___x_1959_);
                if v_isShared_1940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1939_, 2, v___x_1959_);
                    v___x_1961_ = v___x_1939_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_key_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_value_1936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 2, v___x_1959_);
                    v___x_1961_ = v_reuseFailAlloc_1964_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1962_ = lean_array_uset(v_x_1933_, v___x_1958_, v___x_1961_);
                v_x_1933_ = v___x_1962_;
                v_x_1934_ = v_tail_1937_;
                state = 0;
                continue;
            }
            4 => {
                v___x_1967_ = 7u64;
                v___x_1968_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1969_ = lean_array_get_size(v_snd_1942_);
                v___x_1970_ = lean_nat_dec_lt(v___x_1968_, v___x_1969_);
                if v___x_1970_ == 0 {
                    v___y_1945_ = v___y_1966_;
                    v___y_1946_ = v___x_1967_;
                    state = 2;
                    continue;
                } else {
                    v___x_1971_ = lean_nat_dec_le(v___x_1969_, v___x_1969_);
                    if v___x_1971_ == 0 {
                        if v___x_1970_ == 0 {
                            v___y_1945_ = v___y_1966_;
                            v___y_1946_ = v___x_1967_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1972_ = 0usize;
                            v___x_1973_ = lean_usize_of_nat(v___x_1969_);
                            v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_1942_, v___x_1972_, v___x_1973_, v___x_1967_);
                            v___y_1945_ = v___y_1966_;
                            v___y_1946_ = v___x_1974_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1975_ = 0usize;
                        v___x_1976_ = lean_usize_of_nat(v___x_1969_);
                        v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_1942_, v___x_1975_, v___x_1976_, v___x_1967_);
                        v___y_1945_ = v___y_1966_;
                        v___y_1946_ = v___x_1977_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(
    mut v_i_1981_: *mut crate::leanh::LeanObject,
    mut v_source_1982_: *mut crate::leanh::LeanObject,
    mut v_target_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v_es_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1984_ = lean_array_get_size(v_source_1982_);
                v___x_1985_ = lean_nat_dec_lt(v_i_1981_, v___x_1984_);
                if v___x_1985_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1982_);
                    crate::leanh::lean_dec(v_i_1981_);
                    return v_target_1983_;
                } else {
                    v_es_1986_ = lean_array_fget(v_source_1982_, v_i_1981_);
                    v___x_1987_ = crate::leanh::lean_box(0);
                    v_source_1988_ = lean_array_fset(v_source_1982_, v_i_1981_, v___x_1987_);
                    v_target_1989_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_target_1983_, v_es_1986_);
                    v___x_1990_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1991_ = lean_nat_add(v_i_1981_, v___x_1990_);
                    crate::leanh::lean_dec(v_i_1981_);
                    v_i_1981_ = v___x_1991_;
                    v_source_1982_ = v_source_1988_;
                    v_target_1983_ = v_target_1989_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(
    mut v_data_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = lean_array_get_size(v_data_1993_);
    v___x_1995_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1996_ = lean_nat_mul(v___x_1994_, v___x_1995_);
    v___x_1997_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1998_ = crate::leanh::lean_box(0);
    v___x_1999_ = lean_mk_array(v_nbuckets_1996_, v___x_1998_);
    v___x_2000_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_1997_, v_data_1993_, v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(
    mut v_m_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
    mut v_b_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2010_: u64 = 0;
    let mut v___y_2011_: u64 = 0;
    let mut v___x_2012_: u64 = 0;
    let mut v___x_2013_: u64 = 0;
    let mut v___x_2014_: u64 = 0;
    let mut v_fold_2015_: u64 = 0;
    let mut v___x_2016_: u64 = 0;
    let mut v___x_2017_: u64 = 0;
    let mut v___x_2018_: u64 = 0;
    let mut v___x_2019_: usize = 0;
    let mut v___x_2020_: usize = 0;
    let mut v___x_2021_: usize = 0;
    let mut v___x_2022_: usize = 0;
    let mut v___x_2023_: usize = 0;
    let mut v_bkt_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: u8 = 0;
    let mut v_val_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_unused_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2050_: u64 = 0;
    let mut v___x_2051_: u64 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: usize = 0;
    let mut v___x_2057_: usize = 0;
    let mut v___x_2058_: u64 = 0;
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: usize = 0;
    let mut v___x_2061_: u64 = 0;
    let mut v___x_2062_: u64 = 0;
    let mut v_hash_2063_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2004_ = crate::leanh::lean_ctor_get(v_m_2001_, 0);
                v_buckets_2005_ = crate::leanh::lean_ctor_get(v_m_2001_, 1);
                v_fst_2006_ = crate::leanh::lean_ctor_get(v_a_2002_, 0);
                v_snd_2007_ = crate::leanh::lean_ctor_get(v_a_2002_, 1);
                v___x_2008_ = lean_array_get_size(v_buckets_2005_);
                if crate::leanh::lean_obj_tag(v_fst_2006_) == 0 {
                    v___x_2062_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_2050_ = v___x_2062_;
                    state = 5;
                    continue;
                } else {
                    v_hash_2063_ = crate::leanh::lean_ctor_get_uint64(
                        v_fst_2006_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2050_ = v_hash_2063_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_2012_ = lean_uint64_mix_hash(v___y_2010_, v___y_2011_);
                v___x_2013_ = 32u64;
                v___x_2014_ = lean_uint64_shift_right(v___x_2012_, v___x_2013_);
                v_fold_2015_ = lean_uint64_xor(v___x_2012_, v___x_2014_);
                v___x_2016_ = 16u64;
                v___x_2017_ = lean_uint64_shift_right(v_fold_2015_, v___x_2016_);
                v___x_2018_ = lean_uint64_xor(v_fold_2015_, v___x_2017_);
                v___x_2019_ = lean_uint64_to_usize(v___x_2018_);
                v___x_2020_ = lean_usize_of_nat(v___x_2008_);
                v___x_2021_ = 1usize;
                v___x_2022_ = lean_usize_sub(v___x_2020_, v___x_2021_);
                v___x_2023_ = lean_usize_land(v___x_2019_, v___x_2022_);
                v_bkt_2024_ = lean_array_uget_borrowed(v_buckets_2005_, v___x_2023_);
                v___x_2025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_2002_, v_bkt_2024_);
                if v___x_2025_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2005_);
                    crate::leanh::lean_inc(v_size_2004_);
                    v_isSharedCheck_2046_ = (!crate::leanh::lean_is_exclusive(v_m_2001_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v_unused_2047_ = crate::leanh::lean_ctor_get(v_m_2001_, 1);
                        crate::leanh::lean_dec(v_unused_2047_);
                        v_unused_2048_ = crate::leanh::lean_ctor_get(v_m_2001_, 0);
                        crate::leanh::lean_dec(v_unused_2048_);
                        v___x_2027_ = v_m_2001_;
                        v_isShared_2028_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2001_);
                        v___x_2027_ = crate::leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2003_);
                    crate::leanh::lean_dec_ref(v_a_2002_);
                    return v_m_2001_;
                }
            }
            2 => {
                v___x_2029_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2030_ = lean_nat_add(v_size_2004_, v___x_2029_);
                crate::leanh::lean_dec(v_size_2004_);
                crate::leanh::lean_inc(v_bkt_2024_);
                v___x_2031_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2031_, 0, v_a_2002_);
                crate::leanh::lean_ctor_set(v___x_2031_, 1, v_b_2003_);
                crate::leanh::lean_ctor_set(v___x_2031_, 2, v_bkt_2024_);
                v_buckets_x27_2032_ = lean_array_uset(v_buckets_2005_, v___x_2023_, v___x_2031_);
                v___x_2033_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2034_ = lean_nat_mul(v_size_x27_2030_, v___x_2033_);
                v___x_2035_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2036_ = lean_nat_div(v___x_2034_, v___x_2035_);
                crate::leanh::lean_dec(v___x_2034_);
                v___x_2037_ = lean_array_get_size(v_buckets_x27_2032_);
                v___x_2038_ = lean_nat_dec_le(v___x_2036_, v___x_2037_);
                crate::leanh::lean_dec(v___x_2036_);
                if v___x_2038_ == 0 {
                    v_val_2039_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_2032_);
                    if v_isShared_2028_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2027_, 1, v_val_2039_);
                        crate::leanh::lean_ctor_set(v___x_2027_, 0, v_size_x27_2030_);
                        v___x_2041_ = v___x_2027_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_size_x27_2030_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_val_2039_);
                        v___x_2041_ = v_reuseFailAlloc_2042_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2028_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2027_, 1, v_buckets_x27_2032_);
                        crate::leanh::lean_ctor_set(v___x_2027_, 0, v_size_x27_2030_);
                        v___x_2044_ = v___x_2027_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_size_x27_2030_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_buckets_x27_2032_);
                        v___x_2044_ = v_reuseFailAlloc_2045_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2041_;
            }
            4 => {
                return v___x_2044_;
            }
            5 => {
                v___x_2051_ = 7u64;
                v___x_2052_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2053_ = lean_array_get_size(v_snd_2007_);
                v___x_2054_ = lean_nat_dec_lt(v___x_2052_, v___x_2053_);
                if v___x_2054_ == 0 {
                    v___y_2010_ = v___y_2050_;
                    v___y_2011_ = v___x_2051_;
                    state = 1;
                    continue;
                } else {
                    v___x_2055_ = lean_nat_dec_le(v___x_2053_, v___x_2053_);
                    if v___x_2055_ == 0 {
                        if v___x_2054_ == 0 {
                            v___y_2010_ = v___y_2050_;
                            v___y_2011_ = v___x_2051_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2056_ = 0usize;
                            v___x_2057_ = lean_usize_of_nat(v___x_2053_);
                            v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_2007_, v___x_2056_, v___x_2057_, v___x_2051_);
                            v___y_2010_ = v___y_2050_;
                            v___y_2011_ = v___x_2058_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2059_ = 0usize;
                        v___x_2060_ = lean_usize_of_nat(v___x_2053_);
                        v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_2007_, v___x_2059_, v___x_2060_, v___x_2051_);
                        v___y_2010_ = v___y_2050_;
                        v___y_2011_ = v___x_2061_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(
    mut v_m_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2071_: u64 = 0;
    let mut v___y_2072_: u64 = 0;
    let mut v___x_2073_: u64 = 0;
    let mut v___x_2074_: u64 = 0;
    let mut v___x_2075_: u64 = 0;
    let mut v_fold_2076_: u64 = 0;
    let mut v___x_2077_: u64 = 0;
    let mut v___x_2078_: u64 = 0;
    let mut v___x_2079_: u64 = 0;
    let mut v___x_2080_: usize = 0;
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: usize = 0;
    let mut v___x_2083_: usize = 0;
    let mut v___x_2084_: usize = 0;
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    let mut v___y_2088_: u64 = 0;
    let mut v___x_2089_: u64 = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: usize = 0;
    let mut v___x_2095_: usize = 0;
    let mut v___x_2096_: u64 = 0;
    let mut v___x_2097_: usize = 0;
    let mut v___x_2098_: usize = 0;
    let mut v___x_2099_: u64 = 0;
    let mut v___x_2100_: u64 = 0;
    let mut v_hash_2101_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2066_ = crate::leanh::lean_ctor_get(v_m_2064_, 1);
                v_fst_2067_ = crate::leanh::lean_ctor_get(v_a_2065_, 0);
                v_snd_2068_ = crate::leanh::lean_ctor_get(v_a_2065_, 1);
                v___x_2069_ = lean_array_get_size(v_buckets_2066_);
                if crate::leanh::lean_obj_tag(v_fst_2067_) == 0 {
                    v___x_2100_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_2088_ = v___x_2100_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2101_ = crate::leanh::lean_ctor_get_uint64(
                        v_fst_2067_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2088_ = v_hash_2101_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2073_ = lean_uint64_mix_hash(v___y_2071_, v___y_2072_);
                v___x_2074_ = 32u64;
                v___x_2075_ = lean_uint64_shift_right(v___x_2073_, v___x_2074_);
                v_fold_2076_ = lean_uint64_xor(v___x_2073_, v___x_2075_);
                v___x_2077_ = 16u64;
                v___x_2078_ = lean_uint64_shift_right(v_fold_2076_, v___x_2077_);
                v___x_2079_ = lean_uint64_xor(v_fold_2076_, v___x_2078_);
                v___x_2080_ = lean_uint64_to_usize(v___x_2079_);
                v___x_2081_ = lean_usize_of_nat(v___x_2069_);
                v___x_2082_ = 1usize;
                v___x_2083_ = lean_usize_sub(v___x_2081_, v___x_2082_);
                v___x_2084_ = lean_usize_land(v___x_2080_, v___x_2083_);
                v___x_2085_ = lean_array_uget_borrowed(v_buckets_2066_, v___x_2084_);
                v___x_2086_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_2065_, v___x_2085_);
                return v___x_2086_;
            }
            2 => {
                v___x_2089_ = 7u64;
                v___x_2090_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2091_ = lean_array_get_size(v_snd_2068_);
                v___x_2092_ = lean_nat_dec_lt(v___x_2090_, v___x_2091_);
                if v___x_2092_ == 0 {
                    v___y_2071_ = v___y_2088_;
                    v___y_2072_ = v___x_2089_;
                    state = 1;
                    continue;
                } else {
                    v___x_2093_ = lean_nat_dec_le(v___x_2091_, v___x_2091_);
                    if v___x_2093_ == 0 {
                        if v___x_2092_ == 0 {
                            v___y_2071_ = v___y_2088_;
                            v___y_2072_ = v___x_2089_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2094_ = 0usize;
                            v___x_2095_ = lean_usize_of_nat(v___x_2091_);
                            v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_2068_, v___x_2094_, v___x_2095_, v___x_2089_);
                            v___y_2071_ = v___y_2088_;
                            v___y_2072_ = v___x_2096_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2097_ = 0usize;
                        v___x_2098_ = lean_usize_of_nat(v___x_2091_);
                        v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_2068_, v___x_2097_, v___x_2098_, v___x_2089_);
                        v___y_2071_ = v___y_2088_;
                        v___y_2072_ = v___x_2099_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(
    mut v_m_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2104_: u8 = 0;
    let mut v_r_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_2102_, v_a_2103_);
    crate::leanh::lean_dec_ref(v_a_2103_);
    crate::leanh::lean_dec_ref(v_m_2102_);
    v_r_2105_ = crate::leanh::lean_box((v_res_2104_) as usize);
    return v_r_2105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(
    mut v_calls_2106_: *mut crate::leanh::LeanObject,
    mut v_as_2107_: *mut crate::leanh::LeanObject,
    mut v_sz_2108_: usize,
    mut v_i_2109_: usize,
    mut v_b_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v_snd_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2127_: u8 = 0;
    let mut v_array_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v_a_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2171_: u8 = 0;
    let mut v_unused_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v_unused_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2117_ = lean_usize_dec_lt(v_i_2109_, v_sz_2108_);
                if v___x_2117_ == 0 {
                    crate::leanh::lean_dec_ref(v_calls_2106_);
                    v___x_2118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2118_, 0, v_b_2110_);
                    return v___x_2118_;
                } else {
                    v_snd_2119_ = crate::leanh::lean_ctor_get(v_b_2110_, 1);
                    v_isSharedCheck_2176_ = (!crate::leanh::lean_is_exclusive(v_b_2110_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v_unused_2177_ = crate::leanh::lean_ctor_get(v_b_2110_, 0);
                        crate::leanh::lean_dec(v_unused_2177_);
                        v___x_2121_ = v_b_2110_;
                        v_isShared_2122_ = v_isSharedCheck_2176_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2119_);
                        crate::leanh::lean_dec(v_b_2110_);
                        v___x_2121_ = crate::leanh::lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2176_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2114_ = 1usize;
                v___x_2115_ = lean_usize_add(v_i_2109_, v___x_2114_);
                v_i_2109_ = v___x_2115_;
                v_b_2110_ = v_a_2113_;
                state = 0;
                continue;
            }
            2 => {
                v_snd_2123_ = crate::leanh::lean_ctor_get(v_snd_2119_, 1);
                v_fst_2124_ = crate::leanh::lean_ctor_get(v_snd_2119_, 0);
                v_isSharedCheck_2175_ = (!crate::leanh::lean_is_exclusive(v_snd_2119_)) as u8;
                if v_isSharedCheck_2175_ == 0 {
                    v___x_2126_ = v_snd_2119_;
                    v_isShared_2127_ = v_isSharedCheck_2175_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2123_);
                    crate::leanh::lean_inc(v_fst_2124_);
                    crate::leanh::lean_dec(v_snd_2119_);
                    v___x_2126_ = crate::leanh::lean_box(0);
                    v_isShared_2127_ = v_isSharedCheck_2175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_2128_ = crate::leanh::lean_ctor_get(v_snd_2123_, 0);
                v_start_2129_ = crate::leanh::lean_ctor_get(v_snd_2123_, 1);
                v_stop_2130_ = crate::leanh::lean_ctor_get(v_snd_2123_, 2);
                v___x_2131_ = crate::leanh::lean_box(0);
                v___x_2132_ = lean_nat_dec_lt(v_start_2129_, v_stop_2130_);
                if v___x_2132_ == 0 {
                    crate::leanh::lean_dec_ref(v_calls_2106_);
                    if v_isShared_2127_ == 0 {
                        v___x_2134_ = v___x_2126_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2139_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_fst_2124_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_snd_2123_);
                        v___x_2134_ = v_reuseFailAlloc_2139_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_2130_);
                    crate::leanh::lean_inc(v_start_2129_);
                    crate::leanh::lean_inc_ref(v_array_2128_);
                    v_isSharedCheck_2171_ = (!crate::leanh::lean_is_exclusive(v_snd_2123_)) as u8;
                    if v_isSharedCheck_2171_ == 0 {
                        v_unused_2172_ = crate::leanh::lean_ctor_get(v_snd_2123_, 2);
                        crate::leanh::lean_dec(v_unused_2172_);
                        v_unused_2173_ = crate::leanh::lean_ctor_get(v_snd_2123_, 1);
                        crate::leanh::lean_dec(v_unused_2173_);
                        v_unused_2174_ = crate::leanh::lean_ctor_get(v_snd_2123_, 0);
                        crate::leanh::lean_dec(v_unused_2174_);
                        v___x_2141_ = v_snd_2123_;
                        v_isShared_2142_ = v_isSharedCheck_2171_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_2123_);
                        v___x_2141_ = crate::leanh::lean_box(0);
                        v_isShared_2142_ = v_isSharedCheck_2171_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2122_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2121_, 1, v___x_2134_);
                    crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2136_ = v___x_2121_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2134_);
                    v___x_2136_ = v_reuseFailAlloc_2138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2137_, 0, v___x_2136_);
                return v___x_2137_;
            }
            6 => {
                v_a_2143_ = lean_array_uget_borrowed(v_as_2107_, v_i_2109_);
                v___x_2144_ = lean_array_fget(v_array_2128_, v_start_2129_);
                v___x_2145_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2146_ = lean_nat_add(v_start_2129_, v___x_2145_);
                crate::leanh::lean_dec(v_start_2129_);
                if v_isShared_2142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2141_, 1, v___x_2146_);
                    v___x_2148_ = v___x_2141_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2170_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_array_2128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_stop_2130_);
                    v___x_2148_ = v_reuseFailAlloc_2170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2164_ = (crate::leanh::lean_unbox(v___x_2144_) as u8);
                if v___x_2164_ == 2 {
                    v___x_2165_ = l_Lean_Expr_isFVar(v_a_2143_);
                    if v___x_2165_ == 0 {
                        crate::leanh::lean_dec(v___x_2144_);
                        crate::leanh::lean_del_object(v___x_2126_);
                        crate::leanh::lean_del_object(v___x_2121_);
                        v___x_2166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2166_, 0, v_calls_2106_);
                        v___x_2167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2167_, 0, v_fst_2124_);
                        crate::leanh::lean_ctor_set(v___x_2167_, 1, v___x_2148_);
                        v___x_2168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2168_, 0, v___x_2166_);
                        crate::leanh::lean_ctor_set(v___x_2168_, 1, v___x_2167_);
                        v___x_2169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2168_);
                        return v___x_2169_;
                    } else {
                        state = 8;
                        continue;
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2150_ = (crate::leanh::lean_unbox(v___x_2144_) as u8);
                crate::leanh::lean_dec(v___x_2144_);
                if v___x_2150_ == 0 {
                    if v_isShared_2127_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2126_, 1, v___x_2148_);
                        v___x_2152_ = v___x_2126_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_fst_2124_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2148_);
                        v___x_2152_ = v_reuseFailAlloc_2156_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_a_2143_);
                    v___x_2157_ = lean_array_push(v_fst_2124_, v_a_2143_);
                    if v_isShared_2127_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2126_, 1, v___x_2148_);
                        crate::leanh::lean_ctor_set(v___x_2126_, 0, v___x_2157_);
                        v___x_2159_ = v___x_2126_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2148_);
                        v___x_2159_ = v_reuseFailAlloc_2163_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2122_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2121_, 1, v___x_2152_);
                    crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2154_ = v___x_2121_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2152_);
                    v___x_2154_ = v_reuseFailAlloc_2155_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_2113_ = v___x_2154_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_2122_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2121_, 1, v___x_2159_);
                    crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2161_ = v___x_2121_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2162_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
                    v___x_2161_ = v_reuseFailAlloc_2162_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_a_2113_ = v___x_2161_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(
    mut v_calls_2178_: *mut crate::leanh::LeanObject,
    mut v_as_2179_: *mut crate::leanh::LeanObject,
    mut v_sz_2180_: *mut crate::leanh::LeanObject,
    mut v_i_2181_: *mut crate::leanh::LeanObject,
    mut v_b_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2184_: usize = 0;
    let mut v_i_boxed_2185_: usize = 0;
    let mut v_res_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2184_ = crate::leanh::lean_unbox_usize(v_sz_2180_);
    crate::leanh::lean_dec(v_sz_2180_);
    v_i_boxed_2185_ = crate::leanh::lean_unbox_usize(v_i_2181_);
    crate::leanh::lean_dec(v_i_2181_);
    v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2178_, v_as_2179_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2182_);
    crate::leanh::lean_dec_ref(v_as_2179_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_push(
    mut v_e_2187_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2188_: *mut crate::leanh::LeanObject,
    mut v_args_2189_: *mut crate::leanh::LeanObject,
    mut v_calls_2190_: *mut crate::leanh::LeanObject,
    mut v_a_2191_: *mut crate::leanh::LeanObject,
    mut v_a_2192_: *mut crate::leanh::LeanObject,
    mut v_a_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_funName_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2208_: usize = 0;
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v_fst_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v_calls_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_unused_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_unused_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_a_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_funName_2196_ = crate::leanh::lean_ctor_get(v_funIndInfo_2188_, 0);
                crate::leanh::lean_inc(v_funName_2196_);
                v_params_2197_ = crate::leanh::lean_ctor_get(v_funIndInfo_2188_, 3);
                crate::leanh::lean_inc_ref(v_params_2197_);
                crate::leanh::lean_dec_ref(v_funIndInfo_2188_);
                v___x_2198_ = lean_array_get_size(v_params_2197_);
                v___x_2199_ = lean_array_get_size(v_args_2189_);
                v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
                if v___x_2200_ == 0 {
                    crate::leanh::lean_dec_ref(v_params_2197_);
                    crate::leanh::lean_dec(v_funName_2196_);
                    crate::leanh::lean_dec_ref(v_e_2187_);
                    v___x_2201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2201_, 0, v_calls_2190_);
                    return v___x_2201_;
                } else {
                    v___x_2202_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_keys_2203_ = l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0;
                    v___x_2204_ =
                        l_Array_toSubarray___redArg(v_params_2197_, v___x_2202_, v___x_2198_);
                    v___x_2205_ = crate::leanh::lean_box(0);
                    v___x_2206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2206_, 0, v_keys_2203_);
                    crate::leanh::lean_ctor_set(v___x_2206_, 1, v___x_2204_);
                    v___x_2207_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2207_, 0, v___x_2205_);
                    crate::leanh::lean_ctor_set(v___x_2207_, 1, v___x_2206_);
                    v_sz_2208_ = lean_array_size(v_args_2189_);
                    v___x_2209_ = 0usize;
                    crate::leanh::lean_inc_ref(v_calls_2190_);
                    v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2190_, v_args_2189_, v_sz_2208_, v___x_2209_, v___x_2207_);
                    if crate::leanh::lean_obj_tag(v___x_2210_) == 0 {
                        v_a_2211_ = crate::leanh::lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2251_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2251_ == 0 {
                            v___x_2213_ = v___x_2210_;
                            v_isShared_2214_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2211_);
                            crate::leanh::lean_dec(v___x_2210_);
                            v___x_2213_ = crate::leanh::lean_box(0);
                            v_isShared_2214_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_funName_2196_);
                        crate::leanh::lean_dec_ref(v_calls_2190_);
                        crate::leanh::lean_dec_ref(v_e_2187_);
                        v_a_2252_ = crate::leanh::lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2259_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2259_ == 0 {
                            v___x_2254_ = v___x_2210_;
                            v_isShared_2255_ = v_isSharedCheck_2259_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2252_);
                            crate::leanh::lean_dec(v___x_2210_);
                            v___x_2254_ = crate::leanh::lean_box(0);
                            v_isShared_2255_ = v_isSharedCheck_2259_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2215_ = crate::leanh::lean_ctor_get(v_a_2211_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2215_) == 0 {
                    v_snd_2216_ = crate::leanh::lean_ctor_get(v_a_2211_, 1);
                    crate::leanh::lean_inc(v_snd_2216_);
                    crate::leanh::lean_dec(v_a_2211_);
                    v_fst_2217_ = crate::leanh::lean_ctor_get(v_snd_2216_, 0);
                    v_isSharedCheck_2245_ = (!crate::leanh::lean_is_exclusive(v_snd_2216_)) as u8;
                    if v_isSharedCheck_2245_ == 0 {
                        v_unused_2246_ = crate::leanh::lean_ctor_get(v_snd_2216_, 1);
                        crate::leanh::lean_dec(v_unused_2246_);
                        v___x_2219_ = v_snd_2216_;
                        v_isShared_2220_ = v_isSharedCheck_2245_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2217_);
                        crate::leanh::lean_dec(v_snd_2216_);
                        v___x_2219_ = crate::leanh::lean_box(0);
                        v_isShared_2220_ = v_isSharedCheck_2245_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2215_);
                    crate::leanh::lean_dec(v_a_2211_);
                    crate::leanh::lean_dec(v_funName_2196_);
                    crate::leanh::lean_dec_ref(v_calls_2190_);
                    crate::leanh::lean_dec_ref(v_e_2187_);
                    v_val_2247_ = crate::leanh::lean_ctor_get(v_fst_2215_, 0);
                    crate::leanh::lean_inc(v_val_2247_);
                    crate::leanh::lean_dec_ref_known(v_fst_2215_, 1);
                    if v_isShared_2214_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2213_, 0, v_val_2247_);
                        v___x_2249_ = v___x_2213_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_val_2247_);
                        v___x_2249_ = v_reuseFailAlloc_2250_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_calls_2221_ = crate::leanh::lean_ctor_get(v_calls_2190_, 0);
                v_seen_2222_ = crate::leanh::lean_ctor_get(v_calls_2190_, 1);
                if v_isShared_2220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2219_, 1, v_fst_2217_);
                    crate::leanh::lean_ctor_set(v___x_2219_, 0, v_funName_2196_);
                    v___x_2224_ = v___x_2219_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_funName_2196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_fst_2217_);
                    v___x_2224_ = v_reuseFailAlloc_2244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2225_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_2222_, v___x_2224_);
                if v___x_2225_ == 0 {
                    crate::leanh::lean_inc_ref(v_seen_2222_);
                    crate::leanh::lean_inc_ref(v_calls_2221_);
                    v_isSharedCheck_2238_ = (!crate::leanh::lean_is_exclusive(v_calls_2190_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v_unused_2239_ = crate::leanh::lean_ctor_get(v_calls_2190_, 1);
                        crate::leanh::lean_dec(v_unused_2239_);
                        v_unused_2240_ = crate::leanh::lean_ctor_get(v_calls_2190_, 0);
                        crate::leanh::lean_dec(v_unused_2240_);
                        v___x_2227_ = v_calls_2190_;
                        v_isShared_2228_ = v_isSharedCheck_2238_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_calls_2190_);
                        v___x_2227_ = crate::leanh::lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2238_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2224_);
                    crate::leanh::lean_dec_ref(v_e_2187_);
                    if v_isShared_2214_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2213_, 0, v_calls_2190_);
                        v___x_2242_ = v___x_2213_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_calls_2190_);
                        v___x_2242_ = v_reuseFailAlloc_2243_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2229_ = lean_array_push(v_calls_2221_, v_e_2187_);
                v___x_2230_ = crate::leanh::lean_box(0);
                v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_2222_, v___x_2224_, v___x_2230_);
                if v_isShared_2228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2227_, 1, v___x_2231_);
                    crate::leanh::lean_ctor_set(v___x_2227_, 0, v___x_2229_);
                    v___x_2233_ = v___x_2227_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2231_);
                    v___x_2233_ = v_reuseFailAlloc_2237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2213_, 0, v___x_2233_);
                    v___x_2235_ = v___x_2213_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2235_;
            }
            7 => {
                return v___x_2242_;
            }
            8 => {
                return v___x_2249_;
            }
            9 => {
                if v_isShared_2255_ == 0 {
                    v___x_2257_ = v___x_2254_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
                    v___x_2257_ = v_reuseFailAlloc_2258_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_push___boxed(
    mut v_e_2260_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2261_: *mut crate::leanh::LeanObject,
    mut v_args_2262_: *mut crate::leanh::LeanObject,
    mut v_calls_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2269_ = l_Lean_Meta_FunInd_SeenCalls_push(
        v_e_2260_,
        v_funIndInfo_2261_,
        v_args_2262_,
        v_calls_2263_,
        v_a_2264_,
        v_a_2265_,
        v_a_2266_,
        v_a_2267_,
    );
    crate::leanh::lean_dec(v_a_2267_);
    crate::leanh::lean_dec_ref(v_a_2266_);
    crate::leanh::lean_dec(v_a_2265_);
    crate::leanh::lean_dec_ref(v_a_2264_);
    crate::leanh::lean_dec_ref(v_args_2262_);
    return v_res_2269_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(
    mut v_calls_2270_: *mut crate::leanh::LeanObject,
    mut v_as_2271_: *mut crate::leanh::LeanObject,
    mut v_sz_2272_: usize,
    mut v_i_2273_: usize,
    mut v_b_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2270_, v_as_2271_, v_sz_2272_, v_i_2273_, v_b_2274_);
    return v___x_2280_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(
    mut v_calls_2281_: *mut crate::leanh::LeanObject,
    mut v_as_2282_: *mut crate::leanh::LeanObject,
    mut v_sz_2283_: *mut crate::leanh::LeanObject,
    mut v_i_2284_: *mut crate::leanh::LeanObject,
    mut v_b_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2291_: usize = 0;
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_res_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2291_ = crate::leanh::lean_unbox_usize(v_sz_2283_);
    crate::leanh::lean_dec(v_sz_2283_);
    v_i_boxed_2292_ = crate::leanh::lean_unbox_usize(v_i_2284_);
    crate::leanh::lean_dec(v_i_2284_);
    v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_2281_, v_as_2282_, v_sz_boxed_2291_, v_i_boxed_2292_, v_b_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
    crate::leanh::lean_dec(v___y_2289_);
    crate::leanh::lean_dec_ref(v___y_2288_);
    crate::leanh::lean_dec(v___y_2287_);
    crate::leanh::lean_dec_ref(v___y_2286_);
    crate::leanh::lean_dec_ref(v_as_2282_);
    return v_res_2293_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(
    mut v_00_u03b2_2294_: *mut crate::leanh::LeanObject,
    mut v_m_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2297_: u8 = 0;
    v___x_2297_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_2295_, v_a_2296_);
    return v___x_2297_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(
    mut v_00_u03b2_2298_: *mut crate::leanh::LeanObject,
    mut v_m_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2301_: u8 = 0;
    let mut v_r_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(
            v_00_u03b2_2298_,
            v_m_2299_,
            v_a_2300_,
        );
    crate::leanh::lean_dec_ref(v_a_2300_);
    crate::leanh::lean_dec_ref(v_m_2299_);
    v_r_2302_ = crate::leanh::lean_box((v_res_2301_) as usize);
    return v_r_2302_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(
    mut v_00_u03b2_2303_: *mut crate::leanh::LeanObject,
    mut v_m_2304_: *mut crate::leanh::LeanObject,
    mut v_a_2305_: *mut crate::leanh::LeanObject,
    mut v_b_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_2304_, v_a_2305_, v_b_2306_);
    return v___x_2307_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(
    mut v_00_u03b2_2308_: *mut crate::leanh::LeanObject,
    mut v_a_2309_: *mut crate::leanh::LeanObject,
    mut v_x_2310_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2311_: u8 = 0;
    v___x_2311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_2309_, v_x_2310_);
    return v___x_2311_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(
    mut v_00_u03b2_2312_: *mut crate::leanh::LeanObject,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
    mut v_x_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2315_: u8 = 0;
    let mut v_r_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_2312_, v_a_2313_, v_x_2314_);
    crate::leanh::lean_dec(v_x_2314_);
    crate::leanh::lean_dec_ref(v_a_2313_);
    v_r_2316_ = crate::leanh::lean_box((v_res_2315_) as usize);
    return v_r_2316_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(
    mut v_00_u03b2_2317_: *mut crate::leanh::LeanObject,
    mut v_data_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_2318_);
    return v___x_2319_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(
    mut v_xs_2320_: *mut crate::leanh::LeanObject,
    mut v_ys_2321_: *mut crate::leanh::LeanObject,
    mut v_hsz_2322_: *mut crate::leanh::LeanObject,
    mut v_x_2323_: *mut crate::leanh::LeanObject,
    mut v_x_2324_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2325_: u8 = 0;
    v___x_2325_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_2320_, v_ys_2321_, v_x_2323_);
    return v___x_2325_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(
    mut v_xs_2326_: *mut crate::leanh::LeanObject,
    mut v_ys_2327_: *mut crate::leanh::LeanObject,
    mut v_hsz_2328_: *mut crate::leanh::LeanObject,
    mut v_x_2329_: *mut crate::leanh::LeanObject,
    mut v_x_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2331_: u8 = 0;
    let mut v_r_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_2326_, v_ys_2327_, v_hsz_2328_, v_x_2329_, v_x_2330_);
    crate::leanh::lean_dec_ref(v_ys_2327_);
    crate::leanh::lean_dec_ref(v_xs_2326_);
    v_r_2332_ = crate::leanh::lean_box((v_res_2331_) as usize);
    return v_r_2332_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(
    mut v_00_u03b2_2333_: *mut crate::leanh::LeanObject,
    mut v_i_2334_: *mut crate::leanh::LeanObject,
    mut v_source_2335_: *mut crate::leanh::LeanObject,
    mut v_target_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_2334_, v_source_2335_, v_target_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(
    mut v_00_u03b2_2338_: *mut crate::leanh::LeanObject,
    mut v_x_2339_: *mut crate::leanh::LeanObject,
    mut v_x_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_2339_, v_x_2340_);
    return v___x_2341_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(
    mut v_snd_2342_: *mut crate::leanh::LeanObject,
    mut v_x_2343_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2344_: u8 = 0;
    v___x_2344_ = l_Lean_NameSet_contains(v_snd_2342_, v_x_2343_);
    if v___x_2344_ == 0 {
        let mut v___x_2345_: u8 = 0;
        v___x_2345_ = 1;
        return v___x_2345_;
    } else {
        let mut v___x_2346_: u8 = 0;
        v___x_2346_ = 0;
        return v___x_2346_;
    }
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(
    mut v_snd_2347_: *mut crate::leanh::LeanObject,
    mut v_x_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2349_: u8 = 0;
    let mut v_r_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_2347_, v_x_2348_);
    crate::leanh::lean_dec(v_x_2348_);
    crate::leanh::lean_dec(v_snd_2347_);
    v_r_2350_ = crate::leanh::lean_box((v_res_2349_) as usize);
    return v_r_2350_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(
    mut v_a_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2351_) == 0 {
                    v___x_2353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2353_, 0, v_a_2352_);
                    return v___x_2353_;
                } else {
                    v_key_2354_ = crate::leanh::lean_ctor_get(v_a_2351_, 0);
                    crate::leanh::lean_inc(v_key_2354_);
                    v_tail_2355_ = crate::leanh::lean_ctor_get(v_a_2351_, 2);
                    crate::leanh::lean_inc(v_tail_2355_);
                    crate::leanh::lean_dec_ref_known(v_a_2351_, 3);
                    v_fst_2356_ = crate::leanh::lean_ctor_get(v_key_2354_, 0);
                    crate::leanh::lean_inc(v_fst_2356_);
                    crate::leanh::lean_dec(v_key_2354_);
                    v_fst_2357_ = crate::leanh::lean_ctor_get(v_a_2352_, 0);
                    v_snd_2358_ = crate::leanh::lean_ctor_get(v_a_2352_, 1);
                    v_isSharedCheck_2378_ = (!crate::leanh::lean_is_exclusive(v_a_2352_)) as u8;
                    if v_isSharedCheck_2378_ == 0 {
                        v___x_2360_ = v_a_2352_;
                        v_isShared_2361_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2358_);
                        crate::leanh::lean_inc(v_fst_2357_);
                        crate::leanh::lean_dec(v_a_2352_);
                        v___x_2360_ = crate::leanh::lean_box(0);
                        v_isShared_2361_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2362_ = l_Lean_NameSet_contains(v_snd_2358_, v_fst_2356_);
                if v___x_2362_ == 0 {
                    v___x_2363_ = l_Lean_NameSet_contains(v_fst_2357_, v_fst_2356_);
                    if v___x_2363_ == 0 {
                        v___x_2364_ = l_Lean_NameSet_insert(v_fst_2357_, v_fst_2356_);
                        if v_isShared_2361_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2360_, 0, v___x_2364_);
                            v___x_2366_ = v___x_2360_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2368_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2364_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_snd_2358_);
                            v___x_2366_ = v_reuseFailAlloc_2368_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2369_ = l_Lean_NameSet_insert(v_snd_2358_, v_fst_2356_);
                        if v_isShared_2361_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2360_, 1, v___x_2369_);
                            v___x_2371_ = v___x_2360_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2373_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_fst_2357_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2369_);
                            v___x_2371_ = v_reuseFailAlloc_2373_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_2356_);
                    if v_isShared_2361_ == 0 {
                        v___x_2375_ = v___x_2360_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_fst_2357_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_snd_2358_);
                        v___x_2375_ = v_reuseFailAlloc_2377_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_a_2351_ = v_tail_2355_;
                v_a_2352_ = v___x_2366_;
                state = 0;
                continue;
            }
            3 => {
                v_a_2351_ = v_tail_2355_;
                v_a_2352_ = v___x_2371_;
                state = 0;
                continue;
            }
            4 => {
                v_a_2351_ = v_tail_2355_;
                v_a_2352_ = v___x_2375_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(
    mut v_as_2379_: *mut crate::leanh::LeanObject,
    mut v_sz_2380_: usize,
    mut v_i_2381_: usize,
    mut v_b_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2383_: u8 = 0;
    let mut v_a_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: usize = 0;
    let mut v___x_2389_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2383_ = lean_usize_dec_lt(v_i_2381_, v_sz_2380_);
                if v___x_2383_ == 0 {
                    return v_b_2382_;
                } else {
                    v_a_2384_ = lean_array_uget_borrowed(v_as_2379_, v_i_2381_);
                    crate::leanh::lean_inc(v_a_2384_);
                    v___x_2385_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_2384_, v_b_2382_);
                    if crate::leanh::lean_obj_tag(v___x_2385_) == 0 {
                        v_a_2386_ = crate::leanh::lean_ctor_get(v___x_2385_, 0);
                        crate::leanh::lean_inc(v_a_2386_);
                        crate::leanh::lean_dec_ref_known(v___x_2385_, 1);
                        return v_a_2386_;
                    } else {
                        v_a_2387_ = crate::leanh::lean_ctor_get(v___x_2385_, 0);
                        crate::leanh::lean_inc(v_a_2387_);
                        crate::leanh::lean_dec_ref_known(v___x_2385_, 1);
                        v___x_2388_ = 1usize;
                        v___x_2389_ = lean_usize_add(v_i_2381_, v___x_2388_);
                        v_i_2381_ = v___x_2389_;
                        v_b_2382_ = v_a_2387_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(
    mut v_as_2391_: *mut crate::leanh::LeanObject,
    mut v_sz_2392_: *mut crate::leanh::LeanObject,
    mut v_i_2393_: *mut crate::leanh::LeanObject,
    mut v_b_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2395_: usize = 0;
    let mut v_i_boxed_2396_: usize = 0;
    let mut v_res_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2395_ = crate::leanh::lean_unbox_usize(v_sz_2392_);
    crate::leanh::lean_dec(v_sz_2392_);
    v_i_boxed_2396_ = crate::leanh::lean_unbox_usize(v_i_2393_);
    crate::leanh::lean_dec(v_i_2393_);
    v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_2391_, v_sz_boxed_2395_, v_i_boxed_2396_, v_b_2394_);
    crate::leanh::lean_dec_ref(v_as_2391_);
    return v_res_2397_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_seen_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_seen_2398_ = l_Lean_NameSet_empty;
    v___x_2399_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2399_, 0, v_seen_2398_);
    crate::leanh::lean_ctor_set(v___x_2399_, 1, v_seen_2398_);
    return v___x_2399_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques(
    mut v_calls_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_seen_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2404_: usize = 0;
    let mut v___x_2405_: usize = 0;
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_seen_2401_ = crate::leanh::lean_ctor_get(v_calls_2400_, 1);
    v___x_2402_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once),
        _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0,
    );
    v_buckets_2403_ = crate::leanh::lean_ctor_get(v_seen_2401_, 1);
    v_sz_2404_ = lean_array_size(v_buckets_2403_);
    v___x_2405_ = 0usize;
    v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_2403_, v_sz_2404_, v___x_2405_, v___x_2402_);
    v_fst_2407_ = crate::leanh::lean_ctor_get(v___x_2406_, 0);
    crate::leanh::lean_inc(v_fst_2407_);
    v_snd_2408_ = crate::leanh::lean_ctor_get(v___x_2406_, 1);
    crate::leanh::lean_inc(v_snd_2408_);
    crate::leanh::lean_dec_ref(v___x_2406_);
    v___f_2409_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2409_, 0, v_snd_2408_);
    v___x_2410_ = l_Lean_NameSet_filter(v___f_2409_, v_fst_2407_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(
    mut v_calls_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_2411_);
    crate::leanh::lean_dec_ref(v_calls_2411_);
    return v_res_2412_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
    mut v_e_2413_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2414_: *mut crate::leanh::LeanObject,
    mut v_args_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut v_a_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2422_ = lean_st_ref_get(v_a_2416_);
                v___x_2423_ = l_Lean_Meta_FunInd_SeenCalls_push(
                    v_e_2413_,
                    v_funIndInfo_2414_,
                    v_args_2415_,
                    v___x_2422_,
                    v_a_2417_,
                    v_a_2418_,
                    v_a_2419_,
                    v_a_2420_,
                );
                if crate::leanh::lean_obj_tag(v___x_2423_) == 0 {
                    v_a_2424_ = crate::leanh::lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2432_ = (!crate::leanh::lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2432_ == 0 {
                        v___x_2426_ = v___x_2423_;
                        v_isShared_2427_ = v_isSharedCheck_2432_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2424_);
                        crate::leanh::lean_dec(v___x_2423_);
                        v___x_2426_ = crate::leanh::lean_box(0);
                        v_isShared_2427_ = v_isSharedCheck_2432_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2433_ = crate::leanh::lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2440_ = (!crate::leanh::lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2440_ == 0 {
                        v___x_2435_ = v___x_2423_;
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2433_);
                        crate::leanh::lean_dec(v___x_2423_);
                        v___x_2435_ = crate::leanh::lean_box(0);
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2428_ = lean_st_ref_set(v_a_2416_, v_a_2424_);
                if v_isShared_2427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2428_);
                    v___x_2430_ = v___x_2426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
                    v___x_2430_ = v_reuseFailAlloc_2431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2430_;
            }
            3 => {
                if v_isShared_2436_ == 0 {
                    v___x_2438_ = v___x_2435_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
                    v___x_2438_ = v_reuseFailAlloc_2439_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(
    mut v_e_2441_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2442_: *mut crate::leanh::LeanObject,
    mut v_args_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
    mut v_a_2446_: *mut crate::leanh::LeanObject,
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2450_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
        v_e_2441_,
        v_funIndInfo_2442_,
        v_args_2443_,
        v_a_2444_,
        v_a_2445_,
        v_a_2446_,
        v_a_2447_,
        v_a_2448_,
    );
    crate::leanh::lean_dec(v_a_2448_);
    crate::leanh::lean_dec_ref(v_a_2447_);
    crate::leanh::lean_dec(v_a_2446_);
    crate::leanh::lean_dec_ref(v_a_2445_);
    crate::leanh::lean_dec(v_a_2444_);
    crate::leanh::lean_dec_ref(v_args_2443_);
    return v_res_2450_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd(
    mut v_e_2451_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2452_: *mut crate::leanh::LeanObject,
    mut v_args_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
        v_e_2451_,
        v_funIndInfo_2452_,
        v_args_2453_,
        v_a_2455_,
        v_a_2456_,
        v_a_2457_,
        v_a_2458_,
        v_a_2459_,
    );
    return v___x_2461_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(
    mut v_e_2462_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2463_: *mut crate::leanh::LeanObject,
    mut v_args_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2472_ = l_Lean_Meta_FunInd_Collector_saveFunInd(
        v_e_2462_,
        v_funIndInfo_2463_,
        v_args_2464_,
        v_a_2465_,
        v_a_2466_,
        v_a_2467_,
        v_a_2468_,
        v_a_2469_,
        v_a_2470_,
    );
    crate::leanh::lean_dec(v_a_2470_);
    crate::leanh::lean_dec_ref(v_a_2469_);
    crate::leanh::lean_dec(v_a_2468_);
    crate::leanh::lean_dec_ref(v_a_2467_);
    crate::leanh::lean_dec(v_a_2466_);
    crate::leanh::lean_dec_ref(v_a_2465_);
    crate::leanh::lean_dec_ref(v_args_2464_);
    return v_res_2472_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp___redArg(
    mut v_e_2473_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2474_: *mut crate::leanh::LeanObject,
    mut v_args_2475_: *mut crate::leanh::LeanObject,
    mut v_a_2476_: *mut crate::leanh::LeanObject,
    mut v_a_2477_: *mut crate::leanh::LeanObject,
    mut v_a_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
        v_e_2473_,
        v_funIndInfo_2474_,
        v_args_2475_,
        v_a_2476_,
        v_a_2477_,
        v_a_2478_,
        v_a_2479_,
        v_a_2480_,
    );
    return v___x_2482_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(
    mut v_e_2483_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2484_: *mut crate::leanh::LeanObject,
    mut v_args_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
    mut v_a_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
    mut v_a_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2492_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(
        v_e_2483_,
        v_funIndInfo_2484_,
        v_args_2485_,
        v_a_2486_,
        v_a_2487_,
        v_a_2488_,
        v_a_2489_,
        v_a_2490_,
    );
    crate::leanh::lean_dec(v_a_2490_);
    crate::leanh::lean_dec_ref(v_a_2489_);
    crate::leanh::lean_dec(v_a_2488_);
    crate::leanh::lean_dec_ref(v_a_2487_);
    crate::leanh::lean_dec(v_a_2486_);
    crate::leanh::lean_dec_ref(v_args_2485_);
    return v_res_2492_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp(
    mut v_e_2493_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2494_: *mut crate::leanh::LeanObject,
    mut v_args_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
    mut v_a_2501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
        v_e_2493_,
        v_funIndInfo_2494_,
        v_args_2495_,
        v_a_2497_,
        v_a_2498_,
        v_a_2499_,
        v_a_2500_,
        v_a_2501_,
    );
    return v___x_2503_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp___boxed(
    mut v_e_2504_: *mut crate::leanh::LeanObject,
    mut v_funIndInfo_2505_: *mut crate::leanh::LeanObject,
    mut v_args_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2514_ = l_Lean_Meta_FunInd_Collector_visitApp(
        v_e_2504_,
        v_funIndInfo_2505_,
        v_args_2506_,
        v_a_2507_,
        v_a_2508_,
        v_a_2509_,
        v_a_2510_,
        v_a_2511_,
        v_a_2512_,
    );
    crate::leanh::lean_dec(v_a_2512_);
    crate::leanh::lean_dec_ref(v_a_2511_);
    crate::leanh::lean_dec(v_a_2510_);
    crate::leanh::lean_dec_ref(v_a_2509_);
    crate::leanh::lean_dec(v_a_2508_);
    crate::leanh::lean_dec_ref(v_a_2507_);
    crate::leanh::lean_dec_ref(v_args_2506_);
    return v_res_2514_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_2515_: *mut crate::leanh::LeanObject,
    mut v_x_2516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: usize = 0;
    let mut v___x_2525_: u64 = 0;
    let mut v___x_2526_: u64 = 0;
    let mut v___x_2527_: u64 = 0;
    let mut v___x_2528_: u64 = 0;
    let mut v___x_2529_: u64 = 0;
    let mut v_fold_2530_: u64 = 0;
    let mut v___x_2531_: u64 = 0;
    let mut v___x_2532_: u64 = 0;
    let mut v___x_2533_: u64 = 0;
    let mut v___x_2534_: usize = 0;
    let mut v___x_2535_: usize = 0;
    let mut v___x_2536_: usize = 0;
    let mut v___x_2537_: usize = 0;
    let mut v___x_2538_: usize = 0;
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2516_) == 0 {
                    return v_x_2515_;
                } else {
                    v_key_2517_ = crate::leanh::lean_ctor_get(v_x_2516_, 0);
                    v_value_2518_ = crate::leanh::lean_ctor_get(v_x_2516_, 1);
                    v_tail_2519_ = crate::leanh::lean_ctor_get(v_x_2516_, 2);
                    v_isSharedCheck_2545_ = (!crate::leanh::lean_is_exclusive(v_x_2516_)) as u8;
                    if v_isSharedCheck_2545_ == 0 {
                        v___x_2521_ = v_x_2516_;
                        v_isShared_2522_ = v_isSharedCheck_2545_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2519_);
                        crate::leanh::lean_inc(v_value_2518_);
                        crate::leanh::lean_inc(v_key_2517_);
                        crate::leanh::lean_dec(v_x_2516_);
                        v___x_2521_ = crate::leanh::lean_box(0);
                        v_isShared_2522_ = v_isSharedCheck_2545_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2523_ = lean_array_get_size(v_x_2515_);
                v___x_2524_ = lean_ptr_addr(v_key_2517_);
                v___x_2525_ = lean_usize_to_uint64(v___x_2524_);
                v___x_2526_ = 11u64;
                v___x_2527_ = lean_uint64_mix_hash(v___x_2525_, v___x_2526_);
                v___x_2528_ = 32u64;
                v___x_2529_ = lean_uint64_shift_right(v___x_2527_, v___x_2528_);
                v_fold_2530_ = lean_uint64_xor(v___x_2527_, v___x_2529_);
                v___x_2531_ = 16u64;
                v___x_2532_ = lean_uint64_shift_right(v_fold_2530_, v___x_2531_);
                v___x_2533_ = lean_uint64_xor(v_fold_2530_, v___x_2532_);
                v___x_2534_ = lean_uint64_to_usize(v___x_2533_);
                v___x_2535_ = lean_usize_of_nat(v___x_2523_);
                v___x_2536_ = 1usize;
                v___x_2537_ = lean_usize_sub(v___x_2535_, v___x_2536_);
                v___x_2538_ = lean_usize_land(v___x_2534_, v___x_2537_);
                v___x_2539_ = lean_array_uget_borrowed(v_x_2515_, v___x_2538_);
                crate::leanh::lean_inc(v___x_2539_);
                if v_isShared_2522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2521_, 2, v___x_2539_);
                    v___x_2541_ = v___x_2521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_key_2517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_value_2518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 2, v___x_2539_);
                    v___x_2541_ = v_reuseFailAlloc_2544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2542_ = lean_array_uset(v_x_2515_, v___x_2538_, v___x_2541_);
                v_x_2515_ = v___x_2542_;
                v_x_2516_ = v_tail_2519_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(
    mut v_i_2546_: *mut crate::leanh::LeanObject,
    mut v_source_2547_: *mut crate::leanh::LeanObject,
    mut v_target_2548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u8 = 0;
    let mut v_es_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2549_ = lean_array_get_size(v_source_2547_);
                v___x_2550_ = lean_nat_dec_lt(v_i_2546_, v___x_2549_);
                if v___x_2550_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2547_);
                    crate::leanh::lean_dec(v_i_2546_);
                    return v_target_2548_;
                } else {
                    v_es_2551_ = lean_array_fget(v_source_2547_, v_i_2546_);
                    v___x_2552_ = crate::leanh::lean_box(0);
                    v_source_2553_ = lean_array_fset(v_source_2547_, v_i_2546_, v___x_2552_);
                    v_target_2554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_2548_, v_es_2551_);
                    v___x_2555_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2556_ = lean_nat_add(v_i_2546_, v___x_2555_);
                    crate::leanh::lean_dec(v_i_2546_);
                    v_i_2546_ = v___x_2556_;
                    v_source_2547_ = v_source_2553_;
                    v_target_2548_ = v_target_2554_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(
    mut v_data_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2559_ = lean_array_get_size(v_data_2558_);
    v___x_2560_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2561_ = lean_nat_mul(v___x_2559_, v___x_2560_);
    v___x_2562_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2563_ = crate::leanh::lean_box(0);
    v___x_2564_ = lean_mk_array(v_nbuckets_2561_, v___x_2563_);
    v___x_2565_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_2562_, v_data_2558_, v___x_2564_);
    return v___x_2565_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(
    mut v_a_2566_: *mut crate::leanh::LeanObject,
    mut v_x_2567_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2568_: u8 = 0;
    let mut v_key_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2567_) == 0 {
                    v___x_2568_ = 0;
                    return v___x_2568_;
                } else {
                    v_key_2569_ = crate::leanh::lean_ctor_get(v_x_2567_, 0);
                    v_tail_2570_ = crate::leanh::lean_ctor_get(v_x_2567_, 2);
                    v___x_2571_ = lean_ptr_addr(v_key_2569_);
                    v___x_2572_ = lean_ptr_addr(v_a_2566_);
                    v___x_2573_ = lean_usize_dec_eq(v___x_2571_, v___x_2572_);
                    if v___x_2573_ == 0 {
                        v_x_2567_ = v_tail_2570_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2573_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(
    mut v_a_2575_: *mut crate::leanh::LeanObject,
    mut v_x_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2577_: u8 = 0;
    let mut v_r_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2575_, v_x_2576_);
    crate::leanh::lean_dec(v_x_2576_);
    crate::leanh::lean_dec_ref(v_a_2575_);
    v_r_2578_ = crate::leanh::lean_box((v_res_2577_) as usize);
    return v_r_2578_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(
    mut v_m_2579_: *mut crate::leanh::LeanObject,
    mut v_a_2580_: *mut crate::leanh::LeanObject,
    mut v_b_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: usize = 0;
    let mut v___x_2586_: u64 = 0;
    let mut v___x_2587_: u64 = 0;
    let mut v___x_2588_: u64 = 0;
    let mut v___x_2589_: u64 = 0;
    let mut v___x_2590_: u64 = 0;
    let mut v_fold_2591_: u64 = 0;
    let mut v___x_2592_: u64 = 0;
    let mut v___x_2593_: u64 = 0;
    let mut v___x_2594_: u64 = 0;
    let mut v___x_2595_: usize = 0;
    let mut v___x_2596_: usize = 0;
    let mut v___x_2597_: usize = 0;
    let mut v___x_2598_: usize = 0;
    let mut v___x_2599_: usize = 0;
    let mut v_bkt_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v_val_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2622_: u8 = 0;
    let mut v_unused_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2582_ = crate::leanh::lean_ctor_get(v_m_2579_, 0);
                v_buckets_2583_ = crate::leanh::lean_ctor_get(v_m_2579_, 1);
                v___x_2584_ = lean_array_get_size(v_buckets_2583_);
                v___x_2585_ = lean_ptr_addr(v_a_2580_);
                v___x_2586_ = lean_usize_to_uint64(v___x_2585_);
                v___x_2587_ = 11u64;
                v___x_2588_ = lean_uint64_mix_hash(v___x_2586_, v___x_2587_);
                v___x_2589_ = 32u64;
                v___x_2590_ = lean_uint64_shift_right(v___x_2588_, v___x_2589_);
                v_fold_2591_ = lean_uint64_xor(v___x_2588_, v___x_2590_);
                v___x_2592_ = 16u64;
                v___x_2593_ = lean_uint64_shift_right(v_fold_2591_, v___x_2592_);
                v___x_2594_ = lean_uint64_xor(v_fold_2591_, v___x_2593_);
                v___x_2595_ = lean_uint64_to_usize(v___x_2594_);
                v___x_2596_ = lean_usize_of_nat(v___x_2584_);
                v___x_2597_ = 1usize;
                v___x_2598_ = lean_usize_sub(v___x_2596_, v___x_2597_);
                v___x_2599_ = lean_usize_land(v___x_2595_, v___x_2598_);
                v_bkt_2600_ = lean_array_uget_borrowed(v_buckets_2583_, v___x_2599_);
                v___x_2601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2580_, v_bkt_2600_);
                if v___x_2601_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2583_);
                    crate::leanh::lean_inc(v_size_2582_);
                    v_isSharedCheck_2622_ = (!crate::leanh::lean_is_exclusive(v_m_2579_)) as u8;
                    if v_isSharedCheck_2622_ == 0 {
                        v_unused_2623_ = crate::leanh::lean_ctor_get(v_m_2579_, 1);
                        crate::leanh::lean_dec(v_unused_2623_);
                        v_unused_2624_ = crate::leanh::lean_ctor_get(v_m_2579_, 0);
                        crate::leanh::lean_dec(v_unused_2624_);
                        v___x_2603_ = v_m_2579_;
                        v_isShared_2604_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2579_);
                        v___x_2603_ = crate::leanh::lean_box(0);
                        v_isShared_2604_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2581_);
                    crate::leanh::lean_dec_ref(v_a_2580_);
                    return v_m_2579_;
                }
            }
            1 => {
                v___x_2605_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2606_ = lean_nat_add(v_size_2582_, v___x_2605_);
                crate::leanh::lean_dec(v_size_2582_);
                crate::leanh::lean_inc(v_bkt_2600_);
                v___x_2607_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2607_, 0, v_a_2580_);
                crate::leanh::lean_ctor_set(v___x_2607_, 1, v_b_2581_);
                crate::leanh::lean_ctor_set(v___x_2607_, 2, v_bkt_2600_);
                v_buckets_x27_2608_ = lean_array_uset(v_buckets_2583_, v___x_2599_, v___x_2607_);
                v___x_2609_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2610_ = lean_nat_mul(v_size_x27_2606_, v___x_2609_);
                v___x_2611_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2612_ = lean_nat_div(v___x_2610_, v___x_2611_);
                crate::leanh::lean_dec(v___x_2610_);
                v___x_2613_ = lean_array_get_size(v_buckets_x27_2608_);
                v___x_2614_ = lean_nat_dec_le(v___x_2612_, v___x_2613_);
                crate::leanh::lean_dec(v___x_2612_);
                if v___x_2614_ == 0 {
                    v_val_2615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_2608_);
                    if v_isShared_2604_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2603_, 1, v_val_2615_);
                        crate::leanh::lean_ctor_set(v___x_2603_, 0, v_size_x27_2606_);
                        v___x_2617_ = v___x_2603_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_size_x27_2606_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_val_2615_);
                        v___x_2617_ = v_reuseFailAlloc_2618_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2604_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2603_, 1, v_buckets_x27_2608_);
                        crate::leanh::lean_ctor_set(v___x_2603_, 0, v_size_x27_2606_);
                        v___x_2620_ = v___x_2603_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2621_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_size_x27_2606_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_buckets_x27_2608_);
                        v___x_2620_ = v_reuseFailAlloc_2621_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2617_;
            }
            3 => {
                return v___x_2620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(
    mut v_m_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: u64 = 0;
    let mut v___x_2631_: u64 = 0;
    let mut v___x_2632_: u64 = 0;
    let mut v___x_2633_: u64 = 0;
    let mut v___x_2634_: u64 = 0;
    let mut v_fold_2635_: u64 = 0;
    let mut v___x_2636_: u64 = 0;
    let mut v___x_2637_: u64 = 0;
    let mut v___x_2638_: u64 = 0;
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v___x_2641_: usize = 0;
    let mut v___x_2642_: usize = 0;
    let mut v___x_2643_: usize = 0;
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    v_buckets_2627_ = crate::leanh::lean_ctor_get(v_m_2625_, 1);
    v___x_2628_ = lean_array_get_size(v_buckets_2627_);
    v___x_2629_ = lean_ptr_addr(v_a_2626_);
    v___x_2630_ = lean_usize_to_uint64(v___x_2629_);
    v___x_2631_ = 11u64;
    v___x_2632_ = lean_uint64_mix_hash(v___x_2630_, v___x_2631_);
    v___x_2633_ = 32u64;
    v___x_2634_ = lean_uint64_shift_right(v___x_2632_, v___x_2633_);
    v_fold_2635_ = lean_uint64_xor(v___x_2632_, v___x_2634_);
    v___x_2636_ = 16u64;
    v___x_2637_ = lean_uint64_shift_right(v_fold_2635_, v___x_2636_);
    v___x_2638_ = lean_uint64_xor(v_fold_2635_, v___x_2637_);
    v___x_2639_ = lean_uint64_to_usize(v___x_2638_);
    v___x_2640_ = lean_usize_of_nat(v___x_2628_);
    v___x_2641_ = 1usize;
    v___x_2642_ = lean_usize_sub(v___x_2640_, v___x_2641_);
    v___x_2643_ = lean_usize_land(v___x_2639_, v___x_2642_);
    v___x_2644_ = lean_array_uget_borrowed(v_buckets_2627_, v___x_2643_);
    v___x_2645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2626_, v___x_2644_);
    return v___x_2645_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(
    mut v_m_2646_: *mut crate::leanh::LeanObject,
    mut v_a_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2648_: u8 = 0;
    let mut v_r_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_2646_, v_a_2647_);
    crate::leanh::lean_dec_ref(v_a_2647_);
    crate::leanh::lean_dec_ref(v_m_2646_);
    v_r_2649_ = crate::leanh::lean_box((v_res_2648_) as usize);
    return v_r_2649_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_Collector_visit___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = crate::leanh::lean_box(0);
    v_dummy_2651_ = l_Lean_Expr_sort___override(v___x_2650_);
    return v_dummy_2651_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(
    mut v_e_2652_: *mut crate::leanh::LeanObject,
    mut v_x_2653_: *mut crate::leanh::LeanObject,
    mut v_x_2654_: *mut crate::leanh::LeanObject,
    mut v_x_2655_: *mut crate::leanh::LeanObject,
    mut v___y_2656_: *mut crate::leanh::LeanObject,
    mut v___y_2657_: *mut crate::leanh::LeanObject,
    mut v___y_2658_: *mut crate::leanh::LeanObject,
    mut v___y_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
    mut v___y_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: usize = 0;
    let mut v___x_2680_: usize = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: usize = 0;
    let mut v___x_2683_: usize = 0;
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u8 = 0;
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2653_) == 5 {
                    v_fn_2685_ = crate::leanh::lean_ctor_get(v_x_2653_, 0);
                    crate::leanh::lean_inc_ref(v_fn_2685_);
                    v_arg_2686_ = crate::leanh::lean_ctor_get(v_x_2653_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2686_);
                    crate::leanh::lean_dec_ref_known(v_x_2653_, 2);
                    v___x_2687_ = lean_array_set(v_x_2654_, v_x_2655_, v_arg_2686_);
                    v___x_2688_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2689_ = lean_nat_sub(v_x_2655_, v___x_2688_);
                    crate::leanh::lean_dec(v_x_2655_);
                    v_x_2653_ = v_fn_2685_;
                    v_x_2654_ = v___x_2687_;
                    v_x_2655_ = v___x_2689_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_2655_);
                    if crate::leanh::lean_obj_tag(v_x_2653_) == 4 {
                        v_declName_2691_ = crate::leanh::lean_ctor_get(v_x_2653_, 0);
                        crate::leanh::lean_inc(v_declName_2691_);
                        crate::leanh::lean_dec_ref_known(v_x_2653_, 2);
                        v_funName_2692_ = crate::leanh::lean_ctor_get(v___y_2657_, 0);
                        v___x_2693_ = lean_name_eq(v_declName_2691_, v_funName_2692_);
                        crate::leanh::lean_dec(v_declName_2691_);
                        if v___x_2693_ == 0 {
                            crate::leanh::lean_dec_ref(v_e_2652_);
                            v___y_2665_ = v___y_2656_;
                            v___y_2666_ = v___y_2657_;
                            v___y_2667_ = v___y_2658_;
                            v___y_2668_ = v___y_2659_;
                            v___y_2669_ = v___y_2660_;
                            v___y_2670_ = v___y_2661_;
                            v___y_2671_ = v___y_2662_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2694_ = l_Lean_Expr_hasLooseBVars(v_e_2652_);
                            if v___x_2694_ == 0 {
                                crate::leanh::lean_inc_ref(v___y_2657_);
                                v___x_2695_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
                                    v_e_2652_,
                                    v___y_2657_,
                                    v_x_2654_,
                                    v___y_2658_,
                                    v___y_2659_,
                                    v___y_2660_,
                                    v___y_2661_,
                                    v___y_2662_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2695_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2695_, 1);
                                    v___y_2665_ = v___y_2656_;
                                    v___y_2666_ = v___y_2657_;
                                    v___y_2667_ = v___y_2658_;
                                    v___y_2668_ = v___y_2659_;
                                    v___y_2669_ = v___y_2660_;
                                    v___y_2670_ = v___y_2661_;
                                    v___y_2671_ = v___y_2662_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_x_2654_);
                                    return v___x_2695_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_2652_);
                                v___y_2665_ = v___y_2656_;
                                v___y_2666_ = v___y_2657_;
                                v___y_2667_ = v___y_2658_;
                                v___y_2668_ = v___y_2659_;
                                v___y_2669_ = v___y_2660_;
                                v___y_2670_ = v___y_2661_;
                                v___y_2671_ = v___y_2662_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2652_);
                        v___x_2696_ = l_Lean_Meta_FunInd_Collector_visit(
                            v_x_2653_,
                            v___y_2656_,
                            v___y_2657_,
                            v___y_2658_,
                            v___y_2659_,
                            v___y_2660_,
                            v___y_2661_,
                            v___y_2662_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2696_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2696_, 1);
                            v___y_2665_ = v___y_2656_;
                            v___y_2666_ = v___y_2657_;
                            v___y_2667_ = v___y_2658_;
                            v___y_2668_ = v___y_2659_;
                            v___y_2669_ = v___y_2660_;
                            v___y_2670_ = v___y_2661_;
                            v___y_2671_ = v___y_2662_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_x_2654_);
                            return v___x_2696_;
                        }
                    }
                }
            }
            1 => {
                v___x_2672_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2673_ = lean_array_get_size(v_x_2654_);
                v___x_2674_ = crate::leanh::lean_box(0);
                v___x_2675_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
                if v___x_2675_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_2654_);
                    v___x_2676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2676_, 0, v___x_2674_);
                    return v___x_2676_;
                } else {
                    v___x_2677_ = lean_nat_dec_le(v___x_2673_, v___x_2673_);
                    if v___x_2677_ == 0 {
                        if v___x_2675_ == 0 {
                            crate::leanh::lean_dec_ref(v_x_2654_);
                            v___x_2678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2678_, 0, v___x_2674_);
                            return v___x_2678_;
                        } else {
                            v___x_2679_ = 0usize;
                            v___x_2680_ = lean_usize_of_nat(v___x_2673_);
                            v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_2654_, v___x_2679_, v___x_2680_, v___x_2674_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
                            crate::leanh::lean_dec_ref(v_x_2654_);
                            return v___x_2681_;
                        }
                    } else {
                        v___x_2682_ = 0usize;
                        v___x_2683_ = lean_usize_of_nat(v___x_2673_);
                        v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_2654_, v___x_2682_, v___x_2683_, v___x_2674_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
                        crate::leanh::lean_dec_ref(v_x_2654_);
                        return v___x_2684_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visit(
    mut v_e_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
    mut v_a_2699_: *mut crate::leanh::LeanObject,
    mut v_a_2700_: *mut crate::leanh::LeanObject,
    mut v_a_2701_: *mut crate::leanh::LeanObject,
    mut v_a_2702_: *mut crate::leanh::LeanObject,
    mut v_a_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2706_ = lean_st_ref_get(v_a_2698_);
                v___x_2707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_2706_, v_e_2697_);
                crate::leanh::lean_dec(v___x_2706_);
                if v___x_2707_ == 0 {
                    v___x_2708_ = lean_st_ref_take(v_a_2698_);
                    v___x_2709_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_e_2697_);
                    v___x_2710_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_2708_, v_e_2697_, v___x_2709_);
                    v___x_2711_ = lean_st_ref_set(v_a_2698_, v___x_2710_);
                    match crate::leanh::lean_obj_tag(v_e_2697_) {
                        4 => {
                            crate::leanh::lean_dec_ref_known(v_e_2697_, 2);
                            v___x_2724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2724_, 0, v___x_2709_);
                            return v___x_2724_;
                        }
                        7 => {
                            v_binderType_2725_ = crate::leanh::lean_ctor_get(v_e_2697_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_2725_);
                            v_body_2726_ = crate::leanh::lean_ctor_get(v_e_2697_, 2);
                            crate::leanh::lean_inc_ref(v_body_2726_);
                            crate::leanh::lean_dec_ref_known(v_e_2697_, 3);
                            v_d_2713_ = v_binderType_2725_;
                            v_b_2714_ = v_body_2726_;
                            v___y_2715_ = v_a_2698_;
                            v___y_2716_ = v_a_2699_;
                            v___y_2717_ = v_a_2700_;
                            v___y_2718_ = v_a_2701_;
                            v___y_2719_ = v_a_2702_;
                            v___y_2720_ = v_a_2703_;
                            v___y_2721_ = v_a_2704_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_binderType_2727_ = crate::leanh::lean_ctor_get(v_e_2697_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_2727_);
                            v_body_2728_ = crate::leanh::lean_ctor_get(v_e_2697_, 2);
                            crate::leanh::lean_inc_ref(v_body_2728_);
                            crate::leanh::lean_dec_ref_known(v_e_2697_, 3);
                            v_d_2713_ = v_binderType_2727_;
                            v_b_2714_ = v_body_2728_;
                            v___y_2715_ = v_a_2698_;
                            v___y_2716_ = v_a_2699_;
                            v___y_2717_ = v_a_2700_;
                            v___y_2718_ = v_a_2701_;
                            v___y_2719_ = v_a_2702_;
                            v___y_2720_ = v_a_2703_;
                            v___y_2721_ = v_a_2704_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_2729_ = crate::leanh::lean_ctor_get(v_e_2697_, 1);
                            crate::leanh::lean_inc_ref(v_expr_2729_);
                            crate::leanh::lean_dec_ref_known(v_e_2697_, 2);
                            v_e_2697_ = v_expr_2729_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_2731_ = crate::leanh::lean_ctor_get(v_e_2697_, 1);
                            crate::leanh::lean_inc_ref(v_type_2731_);
                            v_value_2732_ = crate::leanh::lean_ctor_get(v_e_2697_, 2);
                            crate::leanh::lean_inc_ref(v_value_2732_);
                            v_body_2733_ = crate::leanh::lean_ctor_get(v_e_2697_, 3);
                            crate::leanh::lean_inc_ref(v_body_2733_);
                            crate::leanh::lean_dec_ref_known(v_e_2697_, 4);
                            v___x_2734_ = l_Lean_Meta_FunInd_Collector_visit(
                                v_type_2731_,
                                v_a_2698_,
                                v_a_2699_,
                                v_a_2700_,
                                v_a_2701_,
                                v_a_2702_,
                                v_a_2703_,
                                v_a_2704_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2734_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2734_, 1);
                                v___x_2735_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_value_2732_,
                                    v_a_2698_,
                                    v_a_2699_,
                                    v_a_2700_,
                                    v_a_2701_,
                                    v_a_2702_,
                                    v_a_2703_,
                                    v_a_2704_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2735_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2735_, 1);
                                    v_e_2697_ = v_body_2733_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_body_2733_);
                                    return v___x_2735_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_2733_);
                                crate::leanh::lean_dec_ref(v_value_2732_);
                                return v___x_2734_;
                            }
                        }
                        5 => {
                            v_dummy_2737_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_FunInd_Collector_visit___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_FunInd_Collector_visit___closed__0_once
                                ),
                                _init_l_Lean_Meta_FunInd_Collector_visit___closed__0,
                            );
                            v_nargs_2738_ = l_Lean_Expr_getAppNumArgs(v_e_2697_);
                            crate::leanh::lean_inc(v_nargs_2738_);
                            v___x_2739_ = lean_mk_array(v_nargs_2738_, v_dummy_2737_);
                            v___x_2740_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2741_ = lean_nat_sub(v_nargs_2738_, v___x_2740_);
                            crate::leanh::lean_dec(v_nargs_2738_);
                            crate::leanh::lean_inc_ref(v_e_2697_);
                            v___x_2742_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_2697_, v_e_2697_, v___x_2739_, v___x_2741_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
                            return v___x_2742_;
                        }
                        11 => {
                            v_struct_2743_ = crate::leanh::lean_ctor_get(v_e_2697_, 2);
                            crate::leanh::lean_inc_ref(v_struct_2743_);
                            crate::leanh::lean_dec_ref_known(v_e_2697_, 3);
                            v_e_2697_ = v_struct_2743_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_2697_);
                            v___x_2745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2745_, 0, v___x_2709_);
                            return v___x_2745_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2697_);
                    v___x_2746_ = crate::leanh::lean_box(0);
                    v___x_2747_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2747_, 0, v___x_2746_);
                    return v___x_2747_;
                }
            }
            1 => {
                v___x_2722_ = l_Lean_Meta_FunInd_Collector_visit(
                    v_d_2713_,
                    v___y_2715_,
                    v___y_2716_,
                    v___y_2717_,
                    v___y_2718_,
                    v___y_2719_,
                    v___y_2720_,
                    v___y_2721_,
                );
                if crate::leanh::lean_obj_tag(v___x_2722_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2722_, 1);
                    v_e_2697_ = v_b_2714_;
                    v_a_2698_ = v___y_2715_;
                    v_a_2699_ = v___y_2716_;
                    v_a_2700_ = v___y_2717_;
                    v_a_2701_ = v___y_2718_;
                    v_a_2702_ = v___y_2719_;
                    v_a_2703_ = v___y_2720_;
                    v_a_2704_ = v___y_2721_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2714_);
                    return v___x_2722_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(
    mut v_as_2748_: *mut crate::leanh::LeanObject,
    mut v_i_2749_: usize,
    mut v_stop_2750_: usize,
    mut v_b_2751_: *mut crate::leanh::LeanObject,
    mut v___y_2752_: *mut crate::leanh::LeanObject,
    mut v___y_2753_: *mut crate::leanh::LeanObject,
    mut v___y_2754_: *mut crate::leanh::LeanObject,
    mut v___y_2755_: *mut crate::leanh::LeanObject,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2760_ = lean_usize_dec_eq(v_i_2749_, v_stop_2750_);
                if v___x_2760_ == 0 {
                    v___x_2761_ = lean_array_uget_borrowed(v_as_2748_, v_i_2749_);
                    crate::leanh::lean_inc(v___x_2761_);
                    v___x_2762_ = l_Lean_Meta_FunInd_Collector_visit(
                        v___x_2761_,
                        v___y_2752_,
                        v___y_2753_,
                        v___y_2754_,
                        v___y_2755_,
                        v___y_2756_,
                        v___y_2757_,
                        v___y_2758_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2762_) == 0 {
                        v_a_2763_ = crate::leanh::lean_ctor_get(v___x_2762_, 0);
                        crate::leanh::lean_inc(v_a_2763_);
                        crate::leanh::lean_dec_ref_known(v___x_2762_, 1);
                        v___x_2764_ = 1usize;
                        v___x_2765_ = lean_usize_add(v_i_2749_, v___x_2764_);
                        v_i_2749_ = v___x_2765_;
                        v_b_2751_ = v_a_2763_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2762_;
                    }
                } else {
                    v___x_2767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v_b_2751_);
                    return v___x_2767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(
    mut v_as_2768_: *mut crate::leanh::LeanObject,
    mut v_i_2769_: *mut crate::leanh::LeanObject,
    mut v_stop_2770_: *mut crate::leanh::LeanObject,
    mut v_b_2771_: *mut crate::leanh::LeanObject,
    mut v___y_2772_: *mut crate::leanh::LeanObject,
    mut v___y_2773_: *mut crate::leanh::LeanObject,
    mut v___y_2774_: *mut crate::leanh::LeanObject,
    mut v___y_2775_: *mut crate::leanh::LeanObject,
    mut v___y_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
    mut v___y_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2780_: usize = 0;
    let mut v_stop_boxed_2781_: usize = 0;
    let mut v_res_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2780_ = crate::leanh::lean_unbox_usize(v_i_2769_);
    crate::leanh::lean_dec(v_i_2769_);
    v_stop_boxed_2781_ = crate::leanh::lean_unbox_usize(v_stop_2770_);
    crate::leanh::lean_dec(v_stop_2770_);
    v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_2768_, v_i_boxed_2780_, v_stop_boxed_2781_, v_b_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
    crate::leanh::lean_dec(v___y_2778_);
    crate::leanh::lean_dec_ref(v___y_2777_);
    crate::leanh::lean_dec(v___y_2776_);
    crate::leanh::lean_dec_ref(v___y_2775_);
    crate::leanh::lean_dec(v___y_2774_);
    crate::leanh::lean_dec_ref(v___y_2773_);
    crate::leanh::lean_dec(v___y_2772_);
    crate::leanh::lean_dec_ref(v_as_2768_);
    return v_res_2782_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visit___boxed(
    mut v_e_2783_: *mut crate::leanh::LeanObject,
    mut v_a_2784_: *mut crate::leanh::LeanObject,
    mut v_a_2785_: *mut crate::leanh::LeanObject,
    mut v_a_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_a_2789_: *mut crate::leanh::LeanObject,
    mut v_a_2790_: *mut crate::leanh::LeanObject,
    mut v_a_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_Meta_FunInd_Collector_visit(
        v_e_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_,
    );
    crate::leanh::lean_dec(v_a_2790_);
    crate::leanh::lean_dec_ref(v_a_2789_);
    crate::leanh::lean_dec(v_a_2788_);
    crate::leanh::lean_dec_ref(v_a_2787_);
    crate::leanh::lean_dec(v_a_2786_);
    crate::leanh::lean_dec_ref(v_a_2785_);
    crate::leanh::lean_dec(v_a_2784_);
    return v_res_2792_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(
    mut v_e_2793_: *mut crate::leanh::LeanObject,
    mut v_x_2794_: *mut crate::leanh::LeanObject,
    mut v_x_2795_: *mut crate::leanh::LeanObject,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
    mut v___y_2799_: *mut crate::leanh::LeanObject,
    mut v___y_2800_: *mut crate::leanh::LeanObject,
    mut v___y_2801_: *mut crate::leanh::LeanObject,
    mut v___y_2802_: *mut crate::leanh::LeanObject,
    mut v___y_2803_: *mut crate::leanh::LeanObject,
    mut v___y_2804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2805_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(
        v_e_2793_,
        v_x_2794_,
        v_x_2795_,
        v_x_2796_,
        v___y_2797_,
        v___y_2798_,
        v___y_2799_,
        v___y_2800_,
        v___y_2801_,
        v___y_2802_,
        v___y_2803_,
    );
    crate::leanh::lean_dec(v___y_2803_);
    crate::leanh::lean_dec_ref(v___y_2802_);
    crate::leanh::lean_dec(v___y_2801_);
    crate::leanh::lean_dec_ref(v___y_2800_);
    crate::leanh::lean_dec(v___y_2799_);
    crate::leanh::lean_dec_ref(v___y_2798_);
    crate::leanh::lean_dec(v___y_2797_);
    return v_res_2805_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(
    mut v_00_u03b2_2806_: *mut crate::leanh::LeanObject,
    mut v_m_2807_: *mut crate::leanh::LeanObject,
    mut v_a_2808_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2809_: u8 = 0;
    v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_2807_, v_a_2808_);
    return v___x_2809_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(
    mut v_00_u03b2_2810_: *mut crate::leanh::LeanObject,
    mut v_m_2811_: *mut crate::leanh::LeanObject,
    mut v_a_2812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2813_: u8 = 0;
    let mut v_r_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2813_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_2810_, v_m_2811_, v_a_2812_);
    crate::leanh::lean_dec_ref(v_a_2812_);
    crate::leanh::lean_dec_ref(v_m_2811_);
    v_r_2814_ = crate::leanh::lean_box((v_res_2813_) as usize);
    return v_r_2814_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(
    mut v_00_u03b2_2815_: *mut crate::leanh::LeanObject,
    mut v_m_2816_: *mut crate::leanh::LeanObject,
    mut v_a_2817_: *mut crate::leanh::LeanObject,
    mut v_b_2818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_2816_, v_a_2817_, v_b_2818_);
    return v___x_2819_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(
    mut v_00_u03b2_2820_: *mut crate::leanh::LeanObject,
    mut v_a_2821_: *mut crate::leanh::LeanObject,
    mut v_x_2822_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2823_: u8 = 0;
    v___x_2823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2821_, v_x_2822_);
    return v___x_2823_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(
    mut v_00_u03b2_2824_: *mut crate::leanh::LeanObject,
    mut v_a_2825_: *mut crate::leanh::LeanObject,
    mut v_x_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2827_: u8 = 0;
    let mut v_r_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_2824_, v_a_2825_, v_x_2826_);
    crate::leanh::lean_dec(v_x_2826_);
    crate::leanh::lean_dec_ref(v_a_2825_);
    v_r_2828_ = crate::leanh::lean_box((v_res_2827_) as usize);
    return v_r_2828_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(
    mut v_00_u03b2_2829_: *mut crate::leanh::LeanObject,
    mut v_data_2830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_2830_);
    return v___x_2831_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2832_: *mut crate::leanh::LeanObject,
    mut v_i_2833_: *mut crate::leanh::LeanObject,
    mut v_source_2834_: *mut crate::leanh::LeanObject,
    mut v_target_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2836_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_2833_, v_source_2834_, v_target_2835_);
    return v___x_2836_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_2837_: *mut crate::leanh::LeanObject,
    mut v_x_2838_: *mut crate::leanh::LeanObject,
    mut v_x_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_2838_, v_x_2839_);
    return v___x_2840_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(
    mut v_e_2841_: *mut crate::leanh::LeanObject,
    mut v___y_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2864_: u8 = 0;
    let mut v_unused_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2844_ = l_Lean_Expr_hasMVar(v_e_2841_);
                if v___x_2844_ == 0 {
                    v___x_2845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2845_, 0, v_e_2841_);
                    return v___x_2845_;
                } else {
                    v___x_2846_ = lean_st_ref_get(v___y_2842_);
                    v_mctx_2847_ = crate::leanh::lean_ctor_get(v___x_2846_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2847_);
                    crate::leanh::lean_dec(v___x_2846_);
                    v___x_2848_ = l_Lean_instantiateMVarsCore(v_mctx_2847_, v_e_2841_);
                    v_fst_2849_ = crate::leanh::lean_ctor_get(v___x_2848_, 0);
                    crate::leanh::lean_inc(v_fst_2849_);
                    v_snd_2850_ = crate::leanh::lean_ctor_get(v___x_2848_, 1);
                    crate::leanh::lean_inc(v_snd_2850_);
                    crate::leanh::lean_dec_ref(v___x_2848_);
                    v___x_2851_ = lean_st_ref_take(v___y_2842_);
                    v_cache_2852_ = crate::leanh::lean_ctor_get(v___x_2851_, 1);
                    v_zetaDeltaFVarIds_2853_ = crate::leanh::lean_ctor_get(v___x_2851_, 2);
                    v_postponed_2854_ = crate::leanh::lean_ctor_get(v___x_2851_, 3);
                    v_diag_2855_ = crate::leanh::lean_ctor_get(v___x_2851_, 4);
                    v_isSharedCheck_2864_ = (!crate::leanh::lean_is_exclusive(v___x_2851_)) as u8;
                    if v_isSharedCheck_2864_ == 0 {
                        v_unused_2865_ = crate::leanh::lean_ctor_get(v___x_2851_, 0);
                        crate::leanh::lean_dec(v_unused_2865_);
                        v___x_2857_ = v___x_2851_;
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2855_);
                        crate::leanh::lean_inc(v_postponed_2854_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2853_);
                        crate::leanh::lean_inc(v_cache_2852_);
                        crate::leanh::lean_dec(v___x_2851_);
                        v___x_2857_ = crate::leanh::lean_box(0);
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2857_, 0, v_snd_2850_);
                    v___x_2860_ = v___x_2857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2863_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_snd_2850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_cache_2852_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2863_,
                        2,
                        v_zetaDeltaFVarIds_2853_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_postponed_2854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_diag_2855_);
                    v___x_2860_ = v_reuseFailAlloc_2863_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2861_ = lean_st_ref_set(v___y_2842_, v___x_2860_);
                v___x_2862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2862_, 0, v_fst_2849_);
                return v___x_2862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(
    mut v_e_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
    mut v___y_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_2866_, v___y_2867_);
    crate::leanh::lean_dec(v___y_2867_);
    return v_res_2869_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(
    mut v_e_2870_: *mut crate::leanh::LeanObject,
    mut v___y_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
    mut v___y_2874_: *mut crate::leanh::LeanObject,
    mut v___y_2875_: *mut crate::leanh::LeanObject,
    mut v___y_2876_: *mut crate::leanh::LeanObject,
    mut v___y_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2879_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_2870_, v___y_2875_);
    return v___x_2879_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(
    mut v_e_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    crate::leanh::lean_dec(v___y_2887_);
    crate::leanh::lean_dec_ref(v___y_2886_);
    crate::leanh::lean_dec(v___y_2885_);
    crate::leanh::lean_dec_ref(v___y_2884_);
    crate::leanh::lean_dec(v___y_2883_);
    crate::leanh::lean_dec_ref(v___y_2882_);
    crate::leanh::lean_dec(v___y_2881_);
    return v_res_2889_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(
    mut v_as_2890_: *mut crate::leanh::LeanObject,
    mut v_sz_2891_: usize,
    mut v_i_2892_: usize,
    mut v_b_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: usize = 0;
    let mut v___x_2914_: usize = 0;
    let mut v_reuseFailAlloc_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_a_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2953_: u8 = 0;
    let mut v_a_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_unused_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2902_ = lean_usize_dec_lt(v_i_2892_, v_sz_2891_);
                if v___x_2902_ == 0 {
                    v___x_2903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2903_, 0, v_b_2893_);
                    return v___x_2903_;
                } else {
                    v_snd_2904_ = crate::leanh::lean_ctor_get(v_b_2893_, 1);
                    v_isSharedCheck_2962_ = (!crate::leanh::lean_is_exclusive(v_b_2893_)) as u8;
                    if v_isSharedCheck_2962_ == 0 {
                        v_unused_2963_ = crate::leanh::lean_ctor_get(v_b_2893_, 0);
                        crate::leanh::lean_dec(v_unused_2963_);
                        v___x_2906_ = v_b_2893_;
                        v_isShared_2907_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2904_);
                        crate::leanh::lean_dec(v_b_2893_);
                        v___x_2906_ = crate::leanh::lean_box(0);
                        v_isShared_2907_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2908_ = crate::leanh::lean_box(0);
                v_a_2917_ = lean_array_uget_borrowed(v_as_2890_, v_i_2892_);
                if crate::leanh::lean_obj_tag(v_a_2917_) == 0 {
                    v_a_2910_ = v_snd_2904_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_2904_);
                    v_val_2918_ = crate::leanh::lean_ctor_get(v_a_2917_, 0);
                    v___x_2919_ = crate::leanh::lean_box(0);
                    v___x_2920_ = l_Lean_LocalDecl_isAuxDecl(v_val_2918_);
                    if v___x_2920_ == 0 {
                        v___x_2921_ = l_Lean_LocalDecl_value_x3f(v_val_2918_, v___x_2920_);
                        if crate::leanh::lean_obj_tag(v___x_2921_) == 1 {
                            v_val_2922_ = crate::leanh::lean_ctor_get(v___x_2921_, 0);
                            crate::leanh::lean_inc(v_val_2922_);
                            crate::leanh::lean_dec_ref_known(v___x_2921_, 1);
                            v___x_2923_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_2922_, v___y_2898_);
                            if crate::leanh::lean_obj_tag(v___x_2923_) == 0 {
                                v_a_2924_ = crate::leanh::lean_ctor_get(v___x_2923_, 0);
                                crate::leanh::lean_inc(v_a_2924_);
                                crate::leanh::lean_dec_ref_known(v___x_2923_, 1);
                                v___x_2925_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_2924_,
                                    v___y_2894_,
                                    v___y_2895_,
                                    v___y_2896_,
                                    v___y_2897_,
                                    v___y_2898_,
                                    v___y_2899_,
                                    v___y_2900_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2925_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2925_, 1);
                                    v_a_2910_ = v___x_2919_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_2906_);
                                    v_a_2926_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                                    v_isSharedCheck_2933_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2925_)) as u8;
                                    if v_isSharedCheck_2933_ == 0 {
                                        v___x_2928_ = v___x_2925_;
                                        v_isShared_2929_ = v_isSharedCheck_2933_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2926_);
                                        crate::leanh::lean_dec(v___x_2925_);
                                        v___x_2928_ = crate::leanh::lean_box(0);
                                        v_isShared_2929_ = v_isSharedCheck_2933_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2906_);
                                v_a_2934_ = crate::leanh::lean_ctor_get(v___x_2923_, 0);
                                v_isSharedCheck_2941_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2923_)) as u8;
                                if v_isSharedCheck_2941_ == 0 {
                                    v___x_2936_ = v___x_2923_;
                                    v_isShared_2937_ = v_isSharedCheck_2941_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2934_);
                                    crate::leanh::lean_dec(v___x_2923_);
                                    v___x_2936_ = crate::leanh::lean_box(0);
                                    v_isShared_2937_ = v_isSharedCheck_2941_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2921_);
                            v___x_2942_ = l_Lean_LocalDecl_type(v_val_2918_);
                            v___x_2943_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_2942_, v___y_2898_);
                            if crate::leanh::lean_obj_tag(v___x_2943_) == 0 {
                                v_a_2944_ = crate::leanh::lean_ctor_get(v___x_2943_, 0);
                                crate::leanh::lean_inc(v_a_2944_);
                                crate::leanh::lean_dec_ref_known(v___x_2943_, 1);
                                v___x_2945_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_2944_,
                                    v___y_2894_,
                                    v___y_2895_,
                                    v___y_2896_,
                                    v___y_2897_,
                                    v___y_2898_,
                                    v___y_2899_,
                                    v___y_2900_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2945_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2945_, 1);
                                    v_a_2910_ = v___x_2919_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_2906_);
                                    v_a_2946_ = crate::leanh::lean_ctor_get(v___x_2945_, 0);
                                    v_isSharedCheck_2953_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2945_)) as u8;
                                    if v_isSharedCheck_2953_ == 0 {
                                        v___x_2948_ = v___x_2945_;
                                        v_isShared_2949_ = v_isSharedCheck_2953_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2946_);
                                        crate::leanh::lean_dec(v___x_2945_);
                                        v___x_2948_ = crate::leanh::lean_box(0);
                                        v_isShared_2949_ = v_isSharedCheck_2953_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2906_);
                                v_a_2954_ = crate::leanh::lean_ctor_get(v___x_2943_, 0);
                                v_isSharedCheck_2961_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2943_)) as u8;
                                if v_isSharedCheck_2961_ == 0 {
                                    v___x_2956_ = v___x_2943_;
                                    v_isShared_2957_ = v_isSharedCheck_2961_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2954_);
                                    crate::leanh::lean_dec(v___x_2943_);
                                    v___x_2956_ = crate::leanh::lean_box(0);
                                    v_isShared_2957_ = v_isSharedCheck_2961_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_2910_ = v___x_2919_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2906_, 1, v_a_2910_);
                    crate::leanh::lean_ctor_set(v___x_2906_, 0, v___x_2908_);
                    v___x_2912_ = v___x_2906_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_a_2910_);
                    v___x_2912_ = v_reuseFailAlloc_2916_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2913_ = 1usize;
                v___x_2914_ = lean_usize_add(v_i_2892_, v___x_2913_);
                v_i_2892_ = v___x_2914_;
                v_b_2893_ = v___x_2912_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2929_ == 0 {
                    v___x_2931_ = v___x_2928_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
                    v___x_2931_ = v_reuseFailAlloc_2932_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2931_;
            }
            6 => {
                if v_isShared_2937_ == 0 {
                    v___x_2939_ = v___x_2936_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
                    v___x_2939_ = v_reuseFailAlloc_2940_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2939_;
            }
            8 => {
                if v_isShared_2949_ == 0 {
                    v___x_2951_ = v___x_2948_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2952_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
                    v___x_2951_ = v_reuseFailAlloc_2952_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2951_;
            }
            10 => {
                if v_isShared_2957_ == 0 {
                    v___x_2959_ = v___x_2956_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(
    mut v_as_2964_: *mut crate::leanh::LeanObject,
    mut v_sz_2965_: *mut crate::leanh::LeanObject,
    mut v_i_2966_: *mut crate::leanh::LeanObject,
    mut v_b_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2976_: usize = 0;
    let mut v_i_boxed_2977_: usize = 0;
    let mut v_res_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2976_ = crate::leanh::lean_unbox_usize(v_sz_2965_);
    crate::leanh::lean_dec(v_sz_2965_);
    v_i_boxed_2977_ = crate::leanh::lean_unbox_usize(v_i_2966_);
    crate::leanh::lean_dec(v_i_2966_);
    v_res_2978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_2964_, v_sz_boxed_2976_, v_i_boxed_2977_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
    crate::leanh::lean_dec(v___y_2974_);
    crate::leanh::lean_dec_ref(v___y_2973_);
    crate::leanh::lean_dec(v___y_2972_);
    crate::leanh::lean_dec_ref(v___y_2971_);
    crate::leanh::lean_dec(v___y_2970_);
    crate::leanh::lean_dec_ref(v___y_2969_);
    crate::leanh::lean_dec(v___y_2968_);
    crate::leanh::lean_dec_ref(v_as_2964_);
    return v_res_2978_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(
    mut v_as_2979_: *mut crate::leanh::LeanObject,
    mut v_sz_2980_: usize,
    mut v_i_2981_: usize,
    mut v_b_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
    mut v___y_2988_: *mut crate::leanh::LeanObject,
    mut v___y_2989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: usize = 0;
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_a_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v_a_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_unused_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_usize_dec_lt(v_i_2981_, v_sz_2980_);
                if v___x_2991_ == 0 {
                    v___x_2992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2992_, 0, v_b_2982_);
                    return v___x_2992_;
                } else {
                    v_snd_2993_ = crate::leanh::lean_ctor_get(v_b_2982_, 1);
                    v_isSharedCheck_3051_ = (!crate::leanh::lean_is_exclusive(v_b_2982_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v_unused_3052_ = crate::leanh::lean_ctor_get(v_b_2982_, 0);
                        crate::leanh::lean_dec(v_unused_3052_);
                        v___x_2995_ = v_b_2982_;
                        v_isShared_2996_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2993_);
                        crate::leanh::lean_dec(v_b_2982_);
                        v___x_2995_ = crate::leanh::lean_box(0);
                        v_isShared_2996_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2997_ = crate::leanh::lean_box(0);
                v_a_3006_ = lean_array_uget_borrowed(v_as_2979_, v_i_2981_);
                if crate::leanh::lean_obj_tag(v_a_3006_) == 0 {
                    v_a_2999_ = v_snd_2993_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_2993_);
                    v_val_3007_ = crate::leanh::lean_ctor_get(v_a_3006_, 0);
                    v___x_3008_ = crate::leanh::lean_box(0);
                    v___x_3009_ = l_Lean_LocalDecl_isAuxDecl(v_val_3007_);
                    if v___x_3009_ == 0 {
                        v___x_3010_ = l_Lean_LocalDecl_value_x3f(v_val_3007_, v___x_3009_);
                        if crate::leanh::lean_obj_tag(v___x_3010_) == 1 {
                            v_val_3011_ = crate::leanh::lean_ctor_get(v___x_3010_, 0);
                            crate::leanh::lean_inc(v_val_3011_);
                            crate::leanh::lean_dec_ref_known(v___x_3010_, 1);
                            v___x_3012_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3011_, v___y_2987_);
                            if crate::leanh::lean_obj_tag(v___x_3012_) == 0 {
                                v_a_3013_ = crate::leanh::lean_ctor_get(v___x_3012_, 0);
                                crate::leanh::lean_inc(v_a_3013_);
                                crate::leanh::lean_dec_ref_known(v___x_3012_, 1);
                                v___x_3014_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_3013_,
                                    v___y_2983_,
                                    v___y_2984_,
                                    v___y_2985_,
                                    v___y_2986_,
                                    v___y_2987_,
                                    v___y_2988_,
                                    v___y_2989_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3014_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3014_, 1);
                                    v_a_2999_ = v___x_3008_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_2995_);
                                    v_a_3015_ = crate::leanh::lean_ctor_get(v___x_3014_, 0);
                                    v_isSharedCheck_3022_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3014_)) as u8;
                                    if v_isSharedCheck_3022_ == 0 {
                                        v___x_3017_ = v___x_3014_;
                                        v_isShared_3018_ = v_isSharedCheck_3022_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3015_);
                                        crate::leanh::lean_dec(v___x_3014_);
                                        v___x_3017_ = crate::leanh::lean_box(0);
                                        v_isShared_3018_ = v_isSharedCheck_3022_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2995_);
                                v_a_3023_ = crate::leanh::lean_ctor_get(v___x_3012_, 0);
                                v_isSharedCheck_3030_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3012_)) as u8;
                                if v_isSharedCheck_3030_ == 0 {
                                    v___x_3025_ = v___x_3012_;
                                    v_isShared_3026_ = v_isSharedCheck_3030_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3023_);
                                    crate::leanh::lean_dec(v___x_3012_);
                                    v___x_3025_ = crate::leanh::lean_box(0);
                                    v_isShared_3026_ = v_isSharedCheck_3030_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3010_);
                            v___x_3031_ = l_Lean_LocalDecl_type(v_val_3007_);
                            v___x_3032_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3031_, v___y_2987_);
                            if crate::leanh::lean_obj_tag(v___x_3032_) == 0 {
                                v_a_3033_ = crate::leanh::lean_ctor_get(v___x_3032_, 0);
                                crate::leanh::lean_inc(v_a_3033_);
                                crate::leanh::lean_dec_ref_known(v___x_3032_, 1);
                                v___x_3034_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_3033_,
                                    v___y_2983_,
                                    v___y_2984_,
                                    v___y_2985_,
                                    v___y_2986_,
                                    v___y_2987_,
                                    v___y_2988_,
                                    v___y_2989_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3034_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3034_, 1);
                                    v_a_2999_ = v___x_3008_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_2995_);
                                    v_a_3035_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                                    v_isSharedCheck_3042_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3034_)) as u8;
                                    if v_isSharedCheck_3042_ == 0 {
                                        v___x_3037_ = v___x_3034_;
                                        v_isShared_3038_ = v_isSharedCheck_3042_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3035_);
                                        crate::leanh::lean_dec(v___x_3034_);
                                        v___x_3037_ = crate::leanh::lean_box(0);
                                        v_isShared_3038_ = v_isSharedCheck_3042_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2995_);
                                v_a_3043_ = crate::leanh::lean_ctor_get(v___x_3032_, 0);
                                v_isSharedCheck_3050_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3032_)) as u8;
                                if v_isSharedCheck_3050_ == 0 {
                                    v___x_3045_ = v___x_3032_;
                                    v_isShared_3046_ = v_isSharedCheck_3050_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3043_);
                                    crate::leanh::lean_dec(v___x_3032_);
                                    v___x_3045_ = crate::leanh::lean_box(0);
                                    v_isShared_3046_ = v_isSharedCheck_3050_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_2999_ = v___x_3008_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2995_, 1, v_a_2999_);
                    crate::leanh::lean_ctor_set(v___x_2995_, 0, v___x_2997_);
                    v___x_3001_ = v___x_2995_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_a_2999_);
                    v___x_3001_ = v_reuseFailAlloc_3005_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3002_ = 1usize;
                v___x_3003_ = lean_usize_add(v_i_2981_, v___x_3002_);
                v___x_3004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_2979_, v_sz_2980_, v___x_3003_, v___x_3001_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
                return v___x_3004_;
            }
            4 => {
                if v_isShared_3018_ == 0 {
                    v___x_3020_ = v___x_3017_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
                    v___x_3020_ = v_reuseFailAlloc_3021_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3020_;
            }
            6 => {
                if v_isShared_3026_ == 0 {
                    v___x_3028_ = v___x_3025_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
                    v___x_3028_ = v_reuseFailAlloc_3029_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3028_;
            }
            8 => {
                if v_isShared_3038_ == 0 {
                    v___x_3040_ = v___x_3037_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3041_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
                    v___x_3040_ = v_reuseFailAlloc_3041_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3040_;
            }
            10 => {
                if v_isShared_3046_ == 0 {
                    v___x_3048_ = v___x_3045_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
                    v___x_3048_ = v_reuseFailAlloc_3049_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(
    mut v_as_3053_: *mut crate::leanh::LeanObject,
    mut v_sz_3054_: *mut crate::leanh::LeanObject,
    mut v_i_3055_: *mut crate::leanh::LeanObject,
    mut v_b_3056_: *mut crate::leanh::LeanObject,
    mut v___y_3057_: *mut crate::leanh::LeanObject,
    mut v___y_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3065_: usize = 0;
    let mut v_i_boxed_3066_: usize = 0;
    let mut v_res_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3065_ = crate::leanh::lean_unbox_usize(v_sz_3054_);
    crate::leanh::lean_dec(v_sz_3054_);
    v_i_boxed_3066_ = crate::leanh::lean_unbox_usize(v_i_3055_);
    crate::leanh::lean_dec(v_i_3055_);
    v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_3053_, v_sz_boxed_3065_, v_i_boxed_3066_, v_b_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
    crate::leanh::lean_dec(v___y_3063_);
    crate::leanh::lean_dec_ref(v___y_3062_);
    crate::leanh::lean_dec(v___y_3061_);
    crate::leanh::lean_dec_ref(v___y_3060_);
    crate::leanh::lean_dec(v___y_3059_);
    crate::leanh::lean_dec_ref(v___y_3058_);
    crate::leanh::lean_dec(v___y_3057_);
    crate::leanh::lean_dec_ref(v_as_3053_);
    return v_res_3067_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(
    mut v_as_3068_: *mut crate::leanh::LeanObject,
    mut v_sz_3069_: usize,
    mut v_i_3070_: usize,
    mut v_b_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: usize = 0;
    let mut v___x_3092_: usize = 0;
    let mut v_reuseFailAlloc_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_a_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3131_: u8 = 0;
    let mut v_a_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut v_isSharedCheck_3140_: u8 = 0;
    let mut v_unused_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3080_ = lean_usize_dec_lt(v_i_3070_, v_sz_3069_);
                if v___x_3080_ == 0 {
                    v___x_3081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3081_, 0, v_b_3071_);
                    return v___x_3081_;
                } else {
                    v_snd_3082_ = crate::leanh::lean_ctor_get(v_b_3071_, 1);
                    v_isSharedCheck_3140_ = (!crate::leanh::lean_is_exclusive(v_b_3071_)) as u8;
                    if v_isSharedCheck_3140_ == 0 {
                        v_unused_3141_ = crate::leanh::lean_ctor_get(v_b_3071_, 0);
                        crate::leanh::lean_dec(v_unused_3141_);
                        v___x_3084_ = v_b_3071_;
                        v_isShared_3085_ = v_isSharedCheck_3140_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3082_);
                        crate::leanh::lean_dec(v_b_3071_);
                        v___x_3084_ = crate::leanh::lean_box(0);
                        v_isShared_3085_ = v_isSharedCheck_3140_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3086_ = crate::leanh::lean_box(0);
                v_a_3095_ = lean_array_uget_borrowed(v_as_3068_, v_i_3070_);
                if crate::leanh::lean_obj_tag(v_a_3095_) == 0 {
                    v_a_3088_ = v_snd_3082_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3082_);
                    v_val_3096_ = crate::leanh::lean_ctor_get(v_a_3095_, 0);
                    v___x_3097_ = crate::leanh::lean_box(0);
                    v___x_3098_ = l_Lean_LocalDecl_isAuxDecl(v_val_3096_);
                    if v___x_3098_ == 0 {
                        v___x_3099_ = l_Lean_LocalDecl_value_x3f(v_val_3096_, v___x_3098_);
                        if crate::leanh::lean_obj_tag(v___x_3099_) == 1 {
                            v_val_3100_ = crate::leanh::lean_ctor_get(v___x_3099_, 0);
                            crate::leanh::lean_inc(v_val_3100_);
                            crate::leanh::lean_dec_ref_known(v___x_3099_, 1);
                            v___x_3101_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3100_, v___y_3076_);
                            if crate::leanh::lean_obj_tag(v___x_3101_) == 0 {
                                v_a_3102_ = crate::leanh::lean_ctor_get(v___x_3101_, 0);
                                crate::leanh::lean_inc(v_a_3102_);
                                crate::leanh::lean_dec_ref_known(v___x_3101_, 1);
                                v___x_3103_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_3102_,
                                    v___y_3072_,
                                    v___y_3073_,
                                    v___y_3074_,
                                    v___y_3075_,
                                    v___y_3076_,
                                    v___y_3077_,
                                    v___y_3078_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3103_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3103_, 1);
                                    v_a_3088_ = v___x_3097_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_3084_);
                                    v_a_3104_ = crate::leanh::lean_ctor_get(v___x_3103_, 0);
                                    v_isSharedCheck_3111_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3103_)) as u8;
                                    if v_isSharedCheck_3111_ == 0 {
                                        v___x_3106_ = v___x_3103_;
                                        v_isShared_3107_ = v_isSharedCheck_3111_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3104_);
                                        crate::leanh::lean_dec(v___x_3103_);
                                        v___x_3106_ = crate::leanh::lean_box(0);
                                        v_isShared_3107_ = v_isSharedCheck_3111_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_3084_);
                                v_a_3112_ = crate::leanh::lean_ctor_get(v___x_3101_, 0);
                                v_isSharedCheck_3119_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3101_)) as u8;
                                if v_isSharedCheck_3119_ == 0 {
                                    v___x_3114_ = v___x_3101_;
                                    v_isShared_3115_ = v_isSharedCheck_3119_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3112_);
                                    crate::leanh::lean_dec(v___x_3101_);
                                    v___x_3114_ = crate::leanh::lean_box(0);
                                    v_isShared_3115_ = v_isSharedCheck_3119_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3099_);
                            v___x_3120_ = l_Lean_LocalDecl_type(v_val_3096_);
                            v___x_3121_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3120_, v___y_3076_);
                            if crate::leanh::lean_obj_tag(v___x_3121_) == 0 {
                                v_a_3122_ = crate::leanh::lean_ctor_get(v___x_3121_, 0);
                                crate::leanh::lean_inc(v_a_3122_);
                                crate::leanh::lean_dec_ref_known(v___x_3121_, 1);
                                v___x_3123_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_3122_,
                                    v___y_3072_,
                                    v___y_3073_,
                                    v___y_3074_,
                                    v___y_3075_,
                                    v___y_3076_,
                                    v___y_3077_,
                                    v___y_3078_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3123_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3123_, 1);
                                    v_a_3088_ = v___x_3097_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_3084_);
                                    v_a_3124_ = crate::leanh::lean_ctor_get(v___x_3123_, 0);
                                    v_isSharedCheck_3131_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3123_)) as u8;
                                    if v_isSharedCheck_3131_ == 0 {
                                        v___x_3126_ = v___x_3123_;
                                        v_isShared_3127_ = v_isSharedCheck_3131_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3124_);
                                        crate::leanh::lean_dec(v___x_3123_);
                                        v___x_3126_ = crate::leanh::lean_box(0);
                                        v_isShared_3127_ = v_isSharedCheck_3131_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_3084_);
                                v_a_3132_ = crate::leanh::lean_ctor_get(v___x_3121_, 0);
                                v_isSharedCheck_3139_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3121_)) as u8;
                                if v_isSharedCheck_3139_ == 0 {
                                    v___x_3134_ = v___x_3121_;
                                    v_isShared_3135_ = v_isSharedCheck_3139_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3132_);
                                    crate::leanh::lean_dec(v___x_3121_);
                                    v___x_3134_ = crate::leanh::lean_box(0);
                                    v_isShared_3135_ = v_isSharedCheck_3139_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_3088_ = v___x_3097_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3085_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3084_, 1, v_a_3088_);
                    crate::leanh::lean_ctor_set(v___x_3084_, 0, v___x_3086_);
                    v___x_3090_ = v___x_3084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3094_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_3088_);
                    v___x_3090_ = v_reuseFailAlloc_3094_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3091_ = 1usize;
                v___x_3092_ = lean_usize_add(v_i_3070_, v___x_3091_);
                v_i_3070_ = v___x_3092_;
                v_b_3071_ = v___x_3090_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3107_ == 0 {
                    v___x_3109_ = v___x_3106_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
                    v___x_3109_ = v_reuseFailAlloc_3110_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3109_;
            }
            6 => {
                if v_isShared_3115_ == 0 {
                    v___x_3117_ = v___x_3114_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
                    v___x_3117_ = v_reuseFailAlloc_3118_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3117_;
            }
            8 => {
                if v_isShared_3127_ == 0 {
                    v___x_3129_ = v___x_3126_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3130_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
                    v___x_3129_ = v_reuseFailAlloc_3130_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3129_;
            }
            10 => {
                if v_isShared_3135_ == 0 {
                    v___x_3137_ = v___x_3134_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
                    v___x_3137_ = v_reuseFailAlloc_3138_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3137_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(
    mut v_as_3142_: *mut crate::leanh::LeanObject,
    mut v_sz_3143_: *mut crate::leanh::LeanObject,
    mut v_i_3144_: *mut crate::leanh::LeanObject,
    mut v_b_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3154_: usize = 0;
    let mut v_i_boxed_3155_: usize = 0;
    let mut v_res_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3154_ = crate::leanh::lean_unbox_usize(v_sz_3143_);
    crate::leanh::lean_dec(v_sz_3143_);
    v_i_boxed_3155_ = crate::leanh::lean_unbox_usize(v_i_3144_);
    crate::leanh::lean_dec(v_i_3144_);
    v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_3142_, v_sz_boxed_3154_, v_i_boxed_3155_, v_b_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
    crate::leanh::lean_dec(v___y_3152_);
    crate::leanh::lean_dec_ref(v___y_3151_);
    crate::leanh::lean_dec(v___y_3150_);
    crate::leanh::lean_dec_ref(v___y_3149_);
    crate::leanh::lean_dec(v___y_3148_);
    crate::leanh::lean_dec_ref(v___y_3147_);
    crate::leanh::lean_dec(v___y_3146_);
    crate::leanh::lean_dec_ref(v_as_3142_);
    return v_res_3156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(
    mut v_as_3157_: *mut crate::leanh::LeanObject,
    mut v_sz_3158_: usize,
    mut v_i_3159_: usize,
    mut v_b_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: usize = 0;
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v_a_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3224_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v_unused_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3169_ = lean_usize_dec_lt(v_i_3159_, v_sz_3158_);
                if v___x_3169_ == 0 {
                    v___x_3170_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3170_, 0, v_b_3160_);
                    return v___x_3170_;
                } else {
                    v_snd_3171_ = crate::leanh::lean_ctor_get(v_b_3160_, 1);
                    v_isSharedCheck_3229_ = (!crate::leanh::lean_is_exclusive(v_b_3160_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v_unused_3230_ = crate::leanh::lean_ctor_get(v_b_3160_, 0);
                        crate::leanh::lean_dec(v_unused_3230_);
                        v___x_3173_ = v_b_3160_;
                        v_isShared_3174_ = v_isSharedCheck_3229_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3171_);
                        crate::leanh::lean_dec(v_b_3160_);
                        v___x_3173_ = crate::leanh::lean_box(0);
                        v_isShared_3174_ = v_isSharedCheck_3229_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3175_ = crate::leanh::lean_box(0);
                v_a_3184_ = lean_array_uget_borrowed(v_as_3157_, v_i_3159_);
                if crate::leanh::lean_obj_tag(v_a_3184_) == 0 {
                    v_a_3177_ = v_snd_3171_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3171_);
                    v_val_3185_ = crate::leanh::lean_ctor_get(v_a_3184_, 0);
                    v___x_3186_ = crate::leanh::lean_box(0);
                    v___x_3187_ = l_Lean_LocalDecl_isAuxDecl(v_val_3185_);
                    if v___x_3187_ == 0 {
                        v___x_3188_ = l_Lean_LocalDecl_value_x3f(v_val_3185_, v___x_3187_);
                        if crate::leanh::lean_obj_tag(v___x_3188_) == 1 {
                            v_val_3189_ = crate::leanh::lean_ctor_get(v___x_3188_, 0);
                            crate::leanh::lean_inc(v_val_3189_);
                            crate::leanh::lean_dec_ref_known(v___x_3188_, 1);
                            v___x_3190_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3189_, v___y_3165_);
                            if crate::leanh::lean_obj_tag(v___x_3190_) == 0 {
                                v_a_3191_ = crate::leanh::lean_ctor_get(v___x_3190_, 0);
                                crate::leanh::lean_inc(v_a_3191_);
                                crate::leanh::lean_dec_ref_known(v___x_3190_, 1);
                                v___x_3192_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_3191_,
                                    v___y_3161_,
                                    v___y_3162_,
                                    v___y_3163_,
                                    v___y_3164_,
                                    v___y_3165_,
                                    v___y_3166_,
                                    v___y_3167_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3192_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3192_, 1);
                                    v_a_3177_ = v___x_3186_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_3173_);
                                    v_a_3193_ = crate::leanh::lean_ctor_get(v___x_3192_, 0);
                                    v_isSharedCheck_3200_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3192_)) as u8;
                                    if v_isSharedCheck_3200_ == 0 {
                                        v___x_3195_ = v___x_3192_;
                                        v_isShared_3196_ = v_isSharedCheck_3200_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3193_);
                                        crate::leanh::lean_dec(v___x_3192_);
                                        v___x_3195_ = crate::leanh::lean_box(0);
                                        v_isShared_3196_ = v_isSharedCheck_3200_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_3173_);
                                v_a_3201_ = crate::leanh::lean_ctor_get(v___x_3190_, 0);
                                v_isSharedCheck_3208_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3190_)) as u8;
                                if v_isSharedCheck_3208_ == 0 {
                                    v___x_3203_ = v___x_3190_;
                                    v_isShared_3204_ = v_isSharedCheck_3208_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3201_);
                                    crate::leanh::lean_dec(v___x_3190_);
                                    v___x_3203_ = crate::leanh::lean_box(0);
                                    v_isShared_3204_ = v_isSharedCheck_3208_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3188_);
                            v___x_3209_ = l_Lean_LocalDecl_type(v_val_3185_);
                            v___x_3210_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3209_, v___y_3165_);
                            if crate::leanh::lean_obj_tag(v___x_3210_) == 0 {
                                v_a_3211_ = crate::leanh::lean_ctor_get(v___x_3210_, 0);
                                crate::leanh::lean_inc(v_a_3211_);
                                crate::leanh::lean_dec_ref_known(v___x_3210_, 1);
                                v___x_3212_ = l_Lean_Meta_FunInd_Collector_visit(
                                    v_a_3211_,
                                    v___y_3161_,
                                    v___y_3162_,
                                    v___y_3163_,
                                    v___y_3164_,
                                    v___y_3165_,
                                    v___y_3166_,
                                    v___y_3167_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3212_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3212_, 1);
                                    v_a_3177_ = v___x_3186_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_3173_);
                                    v_a_3213_ = crate::leanh::lean_ctor_get(v___x_3212_, 0);
                                    v_isSharedCheck_3220_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3212_)) as u8;
                                    if v_isSharedCheck_3220_ == 0 {
                                        v___x_3215_ = v___x_3212_;
                                        v_isShared_3216_ = v_isSharedCheck_3220_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3213_);
                                        crate::leanh::lean_dec(v___x_3212_);
                                        v___x_3215_ = crate::leanh::lean_box(0);
                                        v_isShared_3216_ = v_isSharedCheck_3220_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_3173_);
                                v_a_3221_ = crate::leanh::lean_ctor_get(v___x_3210_, 0);
                                v_isSharedCheck_3228_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3210_)) as u8;
                                if v_isSharedCheck_3228_ == 0 {
                                    v___x_3223_ = v___x_3210_;
                                    v_isShared_3224_ = v_isSharedCheck_3228_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3221_);
                                    crate::leanh::lean_dec(v___x_3210_);
                                    v___x_3223_ = crate::leanh::lean_box(0);
                                    v_isShared_3224_ = v_isSharedCheck_3228_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_3177_ = v___x_3186_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3174_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3173_, 1, v_a_3177_);
                    crate::leanh::lean_ctor_set(v___x_3173_, 0, v___x_3175_);
                    v___x_3179_ = v___x_3173_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_a_3177_);
                    v___x_3179_ = v_reuseFailAlloc_3183_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3180_ = 1usize;
                v___x_3181_ = lean_usize_add(v_i_3159_, v___x_3180_);
                v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_3157_, v_sz_3158_, v___x_3181_, v___x_3179_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
                return v___x_3182_;
            }
            4 => {
                if v_isShared_3196_ == 0 {
                    v___x_3198_ = v___x_3195_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
                    v___x_3198_ = v_reuseFailAlloc_3199_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3198_;
            }
            6 => {
                if v_isShared_3204_ == 0 {
                    v___x_3206_ = v___x_3203_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3206_;
            }
            8 => {
                if v_isShared_3216_ == 0 {
                    v___x_3218_ = v___x_3215_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
                    v___x_3218_ = v_reuseFailAlloc_3219_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3218_;
            }
            10 => {
                if v_isShared_3224_ == 0 {
                    v___x_3226_ = v___x_3223_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
                    v___x_3226_ = v_reuseFailAlloc_3227_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(
    mut v_as_3231_: *mut crate::leanh::LeanObject,
    mut v_sz_3232_: *mut crate::leanh::LeanObject,
    mut v_i_3233_: *mut crate::leanh::LeanObject,
    mut v_b_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3243_: usize = 0;
    let mut v_i_boxed_3244_: usize = 0;
    let mut v_res_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3243_ = crate::leanh::lean_unbox_usize(v_sz_3232_);
    crate::leanh::lean_dec(v_sz_3232_);
    v_i_boxed_3244_ = crate::leanh::lean_unbox_usize(v_i_3233_);
    crate::leanh::lean_dec(v_i_3233_);
    v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_3231_, v_sz_boxed_3243_, v_i_boxed_3244_, v_b_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
    crate::leanh::lean_dec(v___y_3241_);
    crate::leanh::lean_dec_ref(v___y_3240_);
    crate::leanh::lean_dec(v___y_3239_);
    crate::leanh::lean_dec_ref(v___y_3238_);
    crate::leanh::lean_dec(v___y_3237_);
    crate::leanh::lean_dec_ref(v___y_3236_);
    crate::leanh::lean_dec(v___y_3235_);
    crate::leanh::lean_dec_ref(v_as_3231_);
    return v_res_3245_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(
    mut v_init_3246_: *mut crate::leanh::LeanObject,
    mut v_n_3247_: *mut crate::leanh::LeanObject,
    mut v_b_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3260_: usize = 0;
    let mut v___x_3261_: usize = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3266_: u8 = 0;
    let mut v_fst_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v_a_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_vs_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3289_: usize = 0;
    let mut v___x_3290_: usize = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v_fst_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3306_: u8 = 0;
    let mut v_a_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_3247_) == 0 {
                    v_cs_3257_ = crate::leanh::lean_ctor_get(v_n_3247_, 0);
                    v___x_3258_ = crate::leanh::lean_box(0);
                    v___x_3259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3258_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_b_3248_);
                    v_sz_3260_ = lean_array_size(v_cs_3257_);
                    v___x_3261_ = 0usize;
                    v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_3246_, v_cs_3257_, v_sz_3260_, v___x_3261_, v___x_3259_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
                    if crate::leanh::lean_obj_tag(v___x_3262_) == 0 {
                        v_a_3263_ = crate::leanh::lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3277_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3277_ == 0 {
                            v___x_3265_ = v___x_3262_;
                            v_isShared_3266_ = v_isSharedCheck_3277_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3263_);
                            crate::leanh::lean_dec(v___x_3262_);
                            v___x_3265_ = crate::leanh::lean_box(0);
                            v_isShared_3266_ = v_isSharedCheck_3277_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3278_ = crate::leanh::lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3285_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3280_ = v___x_3262_;
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3278_);
                            crate::leanh::lean_dec(v___x_3262_);
                            v___x_3280_ = crate::leanh::lean_box(0);
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3286_ = crate::leanh::lean_ctor_get(v_n_3247_, 0);
                    v___x_3287_ = crate::leanh::lean_box(0);
                    v___x_3288_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3288_, 0, v___x_3287_);
                    crate::leanh::lean_ctor_set(v___x_3288_, 1, v_b_3248_);
                    v_sz_3289_ = lean_array_size(v_vs_3286_);
                    v___x_3290_ = 0usize;
                    v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_3286_, v_sz_3289_, v___x_3290_, v___x_3288_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
                    if crate::leanh::lean_obj_tag(v___x_3291_) == 0 {
                        v_a_3292_ = crate::leanh::lean_ctor_get(v___x_3291_, 0);
                        v_isSharedCheck_3306_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3291_)) as u8;
                        if v_isSharedCheck_3306_ == 0 {
                            v___x_3294_ = v___x_3291_;
                            v_isShared_3295_ = v_isSharedCheck_3306_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3292_);
                            crate::leanh::lean_dec(v___x_3291_);
                            v___x_3294_ = crate::leanh::lean_box(0);
                            v_isShared_3295_ = v_isSharedCheck_3306_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3307_ = crate::leanh::lean_ctor_get(v___x_3291_, 0);
                        v_isSharedCheck_3314_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3291_)) as u8;
                        if v_isSharedCheck_3314_ == 0 {
                            v___x_3309_ = v___x_3291_;
                            v_isShared_3310_ = v_isSharedCheck_3314_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3307_);
                            crate::leanh::lean_dec(v___x_3291_);
                            v___x_3309_ = crate::leanh::lean_box(0);
                            v_isShared_3310_ = v_isSharedCheck_3314_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3267_ = crate::leanh::lean_ctor_get(v_a_3263_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3267_) == 0 {
                    v_snd_3268_ = crate::leanh::lean_ctor_get(v_a_3263_, 1);
                    crate::leanh::lean_inc(v_snd_3268_);
                    crate::leanh::lean_dec(v_a_3263_);
                    v___x_3269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3269_, 0, v_snd_3268_);
                    if v_isShared_3266_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3265_, 0, v___x_3269_);
                        v___x_3271_ = v___x_3265_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3272_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
                        v___x_3271_ = v_reuseFailAlloc_3272_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3267_);
                    crate::leanh::lean_dec(v_a_3263_);
                    v_val_3273_ = crate::leanh::lean_ctor_get(v_fst_3267_, 0);
                    crate::leanh::lean_inc(v_val_3273_);
                    crate::leanh::lean_dec_ref_known(v_fst_3267_, 1);
                    if v_isShared_3266_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3265_, 0, v_val_3273_);
                        v___x_3275_ = v___x_3265_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_val_3273_);
                        v___x_3275_ = v_reuseFailAlloc_3276_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3271_;
            }
            3 => {
                return v___x_3275_;
            }
            4 => {
                if v_isShared_3281_ == 0 {
                    v___x_3283_ = v___x_3280_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3283_;
            }
            6 => {
                v_fst_3296_ = crate::leanh::lean_ctor_get(v_a_3292_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3296_) == 0 {
                    v_snd_3297_ = crate::leanh::lean_ctor_get(v_a_3292_, 1);
                    crate::leanh::lean_inc(v_snd_3297_);
                    crate::leanh::lean_dec(v_a_3292_);
                    v___x_3298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3298_, 0, v_snd_3297_);
                    if v_isShared_3295_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3298_);
                        v___x_3300_ = v___x_3294_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                        v___x_3300_ = v_reuseFailAlloc_3301_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3296_);
                    crate::leanh::lean_dec(v_a_3292_);
                    v_val_3302_ = crate::leanh::lean_ctor_get(v_fst_3296_, 0);
                    crate::leanh::lean_inc(v_val_3302_);
                    crate::leanh::lean_dec_ref_known(v_fst_3296_, 1);
                    if v_isShared_3295_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3294_, 0, v_val_3302_);
                        v___x_3304_ = v___x_3294_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3305_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_val_3302_);
                        v___x_3304_ = v_reuseFailAlloc_3305_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3300_;
            }
            8 => {
                return v___x_3304_;
            }
            9 => {
                if v_isShared_3310_ == 0 {
                    v___x_3312_ = v___x_3309_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3313_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
                    v___x_3312_ = v_reuseFailAlloc_3313_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(
    mut v_init_3315_: *mut crate::leanh::LeanObject,
    mut v_as_3316_: *mut crate::leanh::LeanObject,
    mut v_sz_3317_: usize,
    mut v_i_3318_: usize,
    mut v_b_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v_a_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: usize = 0;
    let mut v_reuseFailAlloc_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_a_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_unused_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_usize_dec_lt(v_i_3318_, v_sz_3317_);
                if v___x_3328_ == 0 {
                    v___x_3329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3329_, 0, v_b_3319_);
                    return v___x_3329_;
                } else {
                    v_snd_3330_ = crate::leanh::lean_ctor_get(v_b_3319_, 1);
                    v_isSharedCheck_3364_ = (!crate::leanh::lean_is_exclusive(v_b_3319_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v_unused_3365_ = crate::leanh::lean_ctor_get(v_b_3319_, 0);
                        crate::leanh::lean_dec(v_unused_3365_);
                        v___x_3332_ = v_b_3319_;
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3330_);
                        crate::leanh::lean_dec(v_b_3319_);
                        v___x_3332_ = crate::leanh::lean_box(0);
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3334_ = lean_array_uget_borrowed(v_as_3316_, v_i_3318_);
                crate::leanh::lean_inc(v_snd_3330_);
                v___x_3335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3315_, v_a_3334_, v_snd_3330_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
                if crate::leanh::lean_obj_tag(v___x_3335_) == 0 {
                    v_a_3336_ = crate::leanh::lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3355_ = (!crate::leanh::lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3355_ == 0 {
                        v___x_3338_ = v___x_3335_;
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3336_);
                        crate::leanh::lean_dec(v___x_3335_);
                        v___x_3338_ = crate::leanh::lean_box(0);
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3332_);
                    crate::leanh::lean_dec(v_snd_3330_);
                    v_a_3356_ = crate::leanh::lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3363_ = (!crate::leanh::lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3363_ == 0 {
                        v___x_3358_ = v___x_3335_;
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3356_);
                        crate::leanh::lean_dec(v___x_3335_);
                        v___x_3358_ = crate::leanh::lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3336_) == 0 {
                    v___x_3340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3340_, 0, v_a_3336_);
                    if v_isShared_3333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3340_);
                        v___x_3342_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3340_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_snd_3330_);
                        v___x_3342_ = v_reuseFailAlloc_3346_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3338_);
                    crate::leanh::lean_dec(v_snd_3330_);
                    v_a_3347_ = crate::leanh::lean_ctor_get(v_a_3336_, 0);
                    crate::leanh::lean_inc(v_a_3347_);
                    crate::leanh::lean_dec_ref_known(v_a_3336_, 1);
                    v___x_3348_ = crate::leanh::lean_box(0);
                    if v_isShared_3333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3332_, 1, v_a_3347_);
                        crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3348_);
                        v___x_3350_ = v___x_3332_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3348_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3347_);
                        v___x_3350_ = v_reuseFailAlloc_3354_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3338_, 0, v___x_3342_);
                    v___x_3344_ = v___x_3338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
                    v___x_3344_ = v_reuseFailAlloc_3345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3344_;
            }
            5 => {
                v___x_3351_ = 1usize;
                v___x_3352_ = lean_usize_add(v_i_3318_, v___x_3351_);
                v_i_3318_ = v___x_3352_;
                v_b_3319_ = v___x_3350_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3359_ == 0 {
                    v___x_3361_ = v___x_3358_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
                    v___x_3361_ = v_reuseFailAlloc_3362_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(
    mut v_init_3366_: *mut crate::leanh::LeanObject,
    mut v_as_3367_: *mut crate::leanh::LeanObject,
    mut v_sz_3368_: *mut crate::leanh::LeanObject,
    mut v_i_3369_: *mut crate::leanh::LeanObject,
    mut v_b_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
    mut v___y_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
    mut v___y_3378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3379_: usize = 0;
    let mut v_i_boxed_3380_: usize = 0;
    let mut v_res_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3379_ = crate::leanh::lean_unbox_usize(v_sz_3368_);
    crate::leanh::lean_dec(v_sz_3368_);
    v_i_boxed_3380_ = crate::leanh::lean_unbox_usize(v_i_3369_);
    crate::leanh::lean_dec(v_i_3369_);
    v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_3366_, v_as_3367_, v_sz_boxed_3379_, v_i_boxed_3380_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
    crate::leanh::lean_dec(v___y_3377_);
    crate::leanh::lean_dec_ref(v___y_3376_);
    crate::leanh::lean_dec(v___y_3375_);
    crate::leanh::lean_dec_ref(v___y_3374_);
    crate::leanh::lean_dec(v___y_3373_);
    crate::leanh::lean_dec_ref(v___y_3372_);
    crate::leanh::lean_dec(v___y_3371_);
    crate::leanh::lean_dec_ref(v_as_3367_);
    return v_res_3381_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(
    mut v_init_3382_: *mut crate::leanh::LeanObject,
    mut v_n_3383_: *mut crate::leanh::LeanObject,
    mut v_b_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3382_, v_n_3383_, v_b_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    crate::leanh::lean_dec(v___y_3391_);
    crate::leanh::lean_dec_ref(v___y_3390_);
    crate::leanh::lean_dec(v___y_3389_);
    crate::leanh::lean_dec_ref(v___y_3388_);
    crate::leanh::lean_dec(v___y_3387_);
    crate::leanh::lean_dec_ref(v___y_3386_);
    crate::leanh::lean_dec(v___y_3385_);
    crate::leanh::lean_dec_ref(v_n_3383_);
    return v_res_3393_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(
    mut v_t_3394_: *mut crate::leanh::LeanObject,
    mut v_init_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v_a_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3418_: usize = 0;
    let mut v___x_3419_: usize = 0;
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v_fst_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3434_: u8 = 0;
    let mut v_a_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v_a_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3404_ = crate::leanh::lean_ctor_get(v_t_3394_, 0);
                v_tail_3405_ = crate::leanh::lean_ctor_get(v_t_3394_, 1);
                v___x_3406_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3395_, v_root_3404_, v_init_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
                if crate::leanh::lean_obj_tag(v___x_3406_) == 0 {
                    v_a_3407_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3443_ = (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v___x_3409_ = v___x_3406_;
                        v_isShared_3410_ = v_isSharedCheck_3443_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3407_);
                        crate::leanh::lean_dec(v___x_3406_);
                        v___x_3409_ = crate::leanh::lean_box(0);
                        v_isShared_3410_ = v_isSharedCheck_3443_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3444_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3451_ = (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v___x_3446_ = v___x_3406_;
                        v_isShared_3447_ = v_isSharedCheck_3451_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3444_);
                        crate::leanh::lean_dec(v___x_3406_);
                        v___x_3446_ = crate::leanh::lean_box(0);
                        v_isShared_3447_ = v_isSharedCheck_3451_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3407_) == 0 {
                    v_a_3411_ = crate::leanh::lean_ctor_get(v_a_3407_, 0);
                    crate::leanh::lean_inc(v_a_3411_);
                    crate::leanh::lean_dec_ref_known(v_a_3407_, 1);
                    if v_isShared_3410_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3409_, 0, v_a_3411_);
                        v___x_3413_ = v___x_3409_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3411_);
                        v___x_3413_ = v_reuseFailAlloc_3414_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3409_);
                    v_a_3415_ = crate::leanh::lean_ctor_get(v_a_3407_, 0);
                    crate::leanh::lean_inc(v_a_3415_);
                    crate::leanh::lean_dec_ref_known(v_a_3407_, 1);
                    v___x_3416_ = crate::leanh::lean_box(0);
                    v___x_3417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3416_);
                    crate::leanh::lean_ctor_set(v___x_3417_, 1, v_a_3415_);
                    v_sz_3418_ = lean_array_size(v_tail_3405_);
                    v___x_3419_ = 0usize;
                    v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_3405_, v_sz_3418_, v___x_3419_, v___x_3417_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
                    if crate::leanh::lean_obj_tag(v___x_3420_) == 0 {
                        v_a_3421_ = crate::leanh::lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3434_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3434_ == 0 {
                            v___x_3423_ = v___x_3420_;
                            v_isShared_3424_ = v_isSharedCheck_3434_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3421_);
                            crate::leanh::lean_dec(v___x_3420_);
                            v___x_3423_ = crate::leanh::lean_box(0);
                            v_isShared_3424_ = v_isSharedCheck_3434_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3435_ = crate::leanh::lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3442_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3442_ == 0 {
                            v___x_3437_ = v___x_3420_;
                            v_isShared_3438_ = v_isSharedCheck_3442_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3435_);
                            crate::leanh::lean_dec(v___x_3420_);
                            v___x_3437_ = crate::leanh::lean_box(0);
                            v_isShared_3438_ = v_isSharedCheck_3442_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3413_;
            }
            3 => {
                v_fst_3425_ = crate::leanh::lean_ctor_get(v_a_3421_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3425_) == 0 {
                    v_snd_3426_ = crate::leanh::lean_ctor_get(v_a_3421_, 1);
                    crate::leanh::lean_inc(v_snd_3426_);
                    crate::leanh::lean_dec(v_a_3421_);
                    if v_isShared_3424_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3423_, 0, v_snd_3426_);
                        v___x_3428_ = v___x_3423_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_snd_3426_);
                        v___x_3428_ = v_reuseFailAlloc_3429_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3425_);
                    crate::leanh::lean_dec(v_a_3421_);
                    v_val_3430_ = crate::leanh::lean_ctor_get(v_fst_3425_, 0);
                    crate::leanh::lean_inc(v_val_3430_);
                    crate::leanh::lean_dec_ref_known(v_fst_3425_, 1);
                    if v_isShared_3424_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3423_, 0, v_val_3430_);
                        v___x_3432_ = v___x_3423_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_val_3430_);
                        v___x_3432_ = v_reuseFailAlloc_3433_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3428_;
            }
            5 => {
                return v___x_3432_;
            }
            6 => {
                if v_isShared_3438_ == 0 {
                    v___x_3440_ = v___x_3437_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
                    v___x_3440_ = v_reuseFailAlloc_3441_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3440_;
            }
            8 => {
                if v_isShared_3447_ == 0 {
                    v___x_3449_ = v___x_3446_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
                    v___x_3449_ = v_reuseFailAlloc_3450_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(
    mut v_t_3452_: *mut crate::leanh::LeanObject,
    mut v_init_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
    mut v___y_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
    mut v___y_3461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_3452_, v_init_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
    crate::leanh::lean_dec(v___y_3460_);
    crate::leanh::lean_dec_ref(v___y_3459_);
    crate::leanh::lean_dec(v___y_3458_);
    crate::leanh::lean_dec_ref(v___y_3457_);
    crate::leanh::lean_dec(v___y_3456_);
    crate::leanh::lean_dec_ref(v___y_3455_);
    crate::leanh::lean_dec(v___y_3454_);
    crate::leanh::lean_dec_ref(v_t_3452_);
    return v_res_3462_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(
    mut v_mvarId_3463_: *mut crate::leanh::LeanObject,
    mut v_a_3464_: *mut crate::leanh::LeanObject,
    mut v_a_3465_: *mut crate::leanh::LeanObject,
    mut v_a_3466_: *mut crate::leanh::LeanObject,
    mut v_a_3467_: *mut crate::leanh::LeanObject,
    mut v_a_3468_: *mut crate::leanh::LeanObject,
    mut v_a_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_a_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3472_ = crate::leanh::lean_ctor_get(v_a_3467_, 2);
                v_decls_3473_ = crate::leanh::lean_ctor_get(v_lctx_3472_, 1);
                v___x_3474_ = crate::leanh::lean_box(0);
                v___x_3475_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_3473_, v___x_3474_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
                if crate::leanh::lean_obj_tag(v___x_3475_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3475_, 1);
                    v___x_3476_ = l_Lean_MVarId_getType(
                        v_mvarId_3463_,
                        v_a_3467_,
                        v_a_3468_,
                        v_a_3469_,
                        v_a_3470_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3476_) == 0 {
                        v_a_3477_ = crate::leanh::lean_ctor_get(v___x_3476_, 0);
                        crate::leanh::lean_inc(v_a_3477_);
                        crate::leanh::lean_dec_ref_known(v___x_3476_, 1);
                        v___x_3478_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_3477_, v_a_3468_);
                        if crate::leanh::lean_obj_tag(v___x_3478_) == 0 {
                            v_a_3479_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                            crate::leanh::lean_inc(v_a_3479_);
                            crate::leanh::lean_dec_ref_known(v___x_3478_, 1);
                            v___x_3480_ = l_Lean_Meta_FunInd_Collector_visit(
                                v_a_3479_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_,
                                v_a_3469_, v_a_3470_,
                            );
                            return v___x_3480_;
                        } else {
                            v_a_3481_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                            v_isSharedCheck_3488_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3478_)) as u8;
                            if v_isSharedCheck_3488_ == 0 {
                                v___x_3483_ = v___x_3478_;
                                v_isShared_3484_ = v_isSharedCheck_3488_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3481_);
                                crate::leanh::lean_dec(v___x_3478_);
                                v___x_3483_ = crate::leanh::lean_box(0);
                                v_isShared_3484_ = v_isSharedCheck_3488_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3489_ = crate::leanh::lean_ctor_get(v___x_3476_, 0);
                        v_isSharedCheck_3496_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3476_)) as u8;
                        if v_isSharedCheck_3496_ == 0 {
                            v___x_3491_ = v___x_3476_;
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3489_);
                            crate::leanh::lean_dec(v___x_3476_);
                            v___x_3491_ = crate::leanh::lean_box(0);
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3463_);
                    return v___x_3475_;
                }
            }
            1 => {
                if v_isShared_3484_ == 0 {
                    v___x_3486_ = v___x_3483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
                    v___x_3486_ = v_reuseFailAlloc_3487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3486_;
            }
            3 => {
                if v_isShared_3492_ == 0 {
                    v___x_3494_ = v___x_3491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
                    v___x_3494_ = v_reuseFailAlloc_3495_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(
    mut v_mvarId_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_a_3500_: *mut crate::leanh::LeanObject,
    mut v_a_3501_: *mut crate::leanh::LeanObject,
    mut v_a_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v_a_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(
        v_mvarId_3497_,
        v_a_3498_,
        v_a_3499_,
        v_a_3500_,
        v_a_3501_,
        v_a_3502_,
        v_a_3503_,
        v_a_3504_,
    );
    crate::leanh::lean_dec(v_a_3504_);
    crate::leanh::lean_dec_ref(v_a_3503_);
    crate::leanh::lean_dec(v_a_3502_);
    crate::leanh::lean_dec_ref(v_a_3501_);
    crate::leanh::lean_dec(v_a_3500_);
    crate::leanh::lean_dec_ref(v_a_3499_);
    crate::leanh::lean_dec(v_a_3498_);
    return v_res_3506_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
    mut v_mvarId_3507_: *mut crate::leanh::LeanObject,
    mut v_x_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_a_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_3507_,
                    v_x_3508_,
                    v___y_3509_,
                    v___y_3510_,
                    v___y_3511_,
                    v___y_3512_,
                );
                if crate::leanh::lean_obj_tag(v___x_3514_) == 0 {
                    v_a_3515_ = crate::leanh::lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3522_ = (!crate::leanh::lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3522_ == 0 {
                        v___x_3517_ = v___x_3514_;
                        v_isShared_3518_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3515_);
                        crate::leanh::lean_dec(v___x_3514_);
                        v___x_3517_ = crate::leanh::lean_box(0);
                        v_isShared_3518_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3523_ = crate::leanh::lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3530_ = (!crate::leanh::lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3530_ == 0 {
                        v___x_3525_ = v___x_3514_;
                        v_isShared_3526_ = v_isSharedCheck_3530_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3523_);
                        crate::leanh::lean_dec(v___x_3514_);
                        v___x_3525_ = crate::leanh::lean_box(0);
                        v_isShared_3526_ = v_isSharedCheck_3530_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3518_ == 0 {
                    v___x_3520_ = v___x_3517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
                    v___x_3520_ = v_reuseFailAlloc_3521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3520_;
            }
            3 => {
                if v_isShared_3526_ == 0 {
                    v___x_3528_ = v___x_3525_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
                    v___x_3528_ = v_reuseFailAlloc_3529_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(
    mut v_mvarId_3531_: *mut crate::leanh::LeanObject,
    mut v_x_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
    mut v___y_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
            v_mvarId_3531_,
            v_x_3532_,
            v___y_3533_,
            v___y_3534_,
            v___y_3535_,
            v___y_3536_,
        );
    crate::leanh::lean_dec(v___y_3536_);
    crate::leanh::lean_dec_ref(v___y_3535_);
    crate::leanh::lean_dec(v___y_3534_);
    crate::leanh::lean_dec_ref(v___y_3533_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(
    mut v_00_u03b1_3539_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3540_: *mut crate::leanh::LeanObject,
    mut v_x_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
    mut v___y_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
    mut v___y_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3547_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
            v_mvarId_3540_,
            v_x_3541_,
            v___y_3542_,
            v___y_3543_,
            v___y_3544_,
            v___y_3545_,
        );
    return v___x_3547_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(
    mut v_00_u03b1_3548_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3549_: *mut crate::leanh::LeanObject,
    mut v_x_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
    mut v___y_3552_: *mut crate::leanh::LeanObject,
    mut v___y_3553_: *mut crate::leanh::LeanObject,
    mut v___y_3554_: *mut crate::leanh::LeanObject,
    mut v___y_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(
        v_00_u03b1_3548_,
        v_mvarId_3549_,
        v_x_3550_,
        v___y_3551_,
        v___y_3552_,
        v___y_3553_,
        v___y_3554_,
    );
    crate::leanh::lean_dec(v___y_3554_);
    crate::leanh::lean_dec_ref(v___y_3553_);
    crate::leanh::lean_dec(v___y_3552_);
    crate::leanh::lean_dec_ref(v___y_3551_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main___lam__0(
    mut v___x_3557_: *mut crate::leanh::LeanObject,
    mut v___x_3558_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3559_: *mut crate::leanh::LeanObject,
    mut v_needle_3560_: *mut crate::leanh::LeanObject,
    mut v___y_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
    mut v___y_3564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_calls_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut v_unused_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3566_ = lean_st_mk_ref(v___x_3557_);
                v___x_3567_ = lean_st_mk_ref(v___x_3558_);
                v___x_3568_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_3559_, v___x_3567_, v_needle_3560_, v___x_3566_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
                if crate::leanh::lean_obj_tag(v___x_3568_) == 0 {
                    v_isSharedCheck_3578_ = (!crate::leanh::lean_is_exclusive(v___x_3568_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v_unused_3579_ = crate::leanh::lean_ctor_get(v___x_3568_, 0);
                        crate::leanh::lean_dec(v_unused_3579_);
                        v___x_3570_ = v___x_3568_;
                        v_isShared_3571_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3568_);
                        v___x_3570_ = crate::leanh::lean_box(0);
                        v_isShared_3571_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3567_);
                    crate::leanh::lean_dec(v___x_3566_);
                    v_a_3580_ = crate::leanh::lean_ctor_get(v___x_3568_, 0);
                    v_isSharedCheck_3587_ = (!crate::leanh::lean_is_exclusive(v___x_3568_)) as u8;
                    if v_isSharedCheck_3587_ == 0 {
                        v___x_3582_ = v___x_3568_;
                        v_isShared_3583_ = v_isSharedCheck_3587_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3580_);
                        crate::leanh::lean_dec(v___x_3568_);
                        v___x_3582_ = crate::leanh::lean_box(0);
                        v_isShared_3583_ = v_isSharedCheck_3587_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3572_ = lean_st_ref_get(v___x_3567_);
                crate::leanh::lean_dec(v___x_3567_);
                crate::leanh::lean_dec(v___x_3572_);
                v___x_3573_ = lean_st_ref_get(v___x_3566_);
                crate::leanh::lean_dec(v___x_3566_);
                v_calls_3574_ = crate::leanh::lean_ctor_get(v___x_3573_, 0);
                crate::leanh::lean_inc_ref(v_calls_3574_);
                crate::leanh::lean_dec(v___x_3573_);
                if v_isShared_3571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3570_, 0, v_calls_3574_);
                    v___x_3576_ = v___x_3570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_calls_3574_);
                    v___x_3576_ = v_reuseFailAlloc_3577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3576_;
            }
            3 => {
                if v_isShared_3583_ == 0 {
                    v___x_3585_ = v___x_3582_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
                    v___x_3585_ = v_reuseFailAlloc_3586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(
    mut v___x_3588_: *mut crate::leanh::LeanObject,
    mut v___x_3589_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3590_: *mut crate::leanh::LeanObject,
    mut v_needle_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l_Lean_Meta_FunInd_Collector_main___lam__0(
        v___x_3588_,
        v___x_3589_,
        v_mvarId_3590_,
        v_needle_3591_,
        v___y_3592_,
        v___y_3593_,
        v___y_3594_,
        v___y_3595_,
    );
    crate::leanh::lean_dec(v___y_3595_);
    crate::leanh::lean_dec_ref(v___y_3594_);
    crate::leanh::lean_dec(v___y_3593_);
    crate::leanh::lean_dec_ref(v___y_3592_);
    crate::leanh::lean_dec_ref(v_needle_3591_);
    return v_res_3597_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_Collector_main___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_3599_ = l_Lean_mkPtrSet___redArg(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main(
    mut v_needle_3600_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3601_: *mut crate::leanh::LeanObject,
    mut v_a_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3607_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_Collector_main___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_Collector_main___closed__0_once),
        _init_l_Lean_Meta_FunInd_Collector_main___closed__0,
    );
    v___x_3608_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3,
    );
    crate::leanh::lean_inc(v_mvarId_3601_);
    v___f_3609_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_FunInd_Collector_main___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3609_, 0, v___x_3608_);
    crate::leanh::lean_closure_set(v___f_3609_, 1, v___x_3607_);
    crate::leanh::lean_closure_set(v___f_3609_, 2, v_mvarId_3601_);
    crate::leanh::lean_closure_set(v___f_3609_, 3, v_needle_3600_);
    v___x_3610_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
            v_mvarId_3601_,
            v___f_3609_,
            v_a_3602_,
            v_a_3603_,
            v_a_3604_,
            v_a_3605_,
        );
    return v___x_3610_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main___boxed(
    mut v_needle_3611_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3612_: *mut crate::leanh::LeanObject,
    mut v_a_3613_: *mut crate::leanh::LeanObject,
    mut v_a_3614_: *mut crate::leanh::LeanObject,
    mut v_a_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
    mut v_a_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Lean_Meta_FunInd_Collector_main(
        v_needle_3611_,
        v_mvarId_3612_,
        v_a_3613_,
        v_a_3614_,
        v_a_3615_,
        v_a_3616_,
    );
    crate::leanh::lean_dec(v_a_3616_);
    crate::leanh::lean_dec_ref(v_a_3615_);
    crate::leanh::lean_dec(v_a_3614_);
    crate::leanh::lean_dec_ref(v_a_3613_);
    return v_res_3618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(
    mut v_needle_3619_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3620_: *mut crate::leanh::LeanObject,
    mut v_a_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
    mut v_a_3623_: *mut crate::leanh::LeanObject,
    mut v_a_3624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3626_ = l_Lean_Meta_FunInd_Collector_main(
        v_needle_3619_,
        v_mvarId_3620_,
        v_a_3621_,
        v_a_3622_,
        v_a_3623_,
        v_a_3624_,
    );
    return v___x_3626_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(
    mut v_needle_3627_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3634_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(
        v_needle_3627_,
        v_mvarId_3628_,
        v_a_3629_,
        v_a_3630_,
        v_a_3631_,
        v_a_3632_,
    );
    crate::leanh::lean_dec(v_a_3632_);
    crate::leanh::lean_dec_ref(v_a_3631_);
    crate::leanh::lean_dec(v_a_3630_);
    crate::leanh::lean_dec_ref(v_a_3629_);
    return v_res_3634_;
}
pub unsafe fn l_Lean_Meta_FunInd_collect(
    mut v_needle_3635_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3636_: *mut crate::leanh::LeanObject,
    mut v_a_3637_: *mut crate::leanh::LeanObject,
    mut v_a_3638_: *mut crate::leanh::LeanObject,
    mut v_a_3639_: *mut crate::leanh::LeanObject,
    mut v_a_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3642_ = l_Lean_Meta_FunInd_Collector_main(
        v_needle_3635_,
        v_mvarId_3636_,
        v_a_3637_,
        v_a_3638_,
        v_a_3639_,
        v_a_3640_,
    );
    return v___x_3642_;
}
pub unsafe fn l_Lean_Meta_FunInd_collect___boxed(
    mut v_needle_3643_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3644_: *mut crate::leanh::LeanObject,
    mut v_a_3645_: *mut crate::leanh::LeanObject,
    mut v_a_3646_: *mut crate::leanh::LeanObject,
    mut v_a_3647_: *mut crate::leanh::LeanObject,
    mut v_a_3648_: *mut crate::leanh::LeanObject,
    mut v_a_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ = l_Lean_Meta_FunInd_collect(
        v_needle_3643_,
        v_mvarId_3644_,
        v_a_3645_,
        v_a_3646_,
        v_a_3647_,
        v_a_3648_,
    );
    crate::leanh::lean_dec(v_a_3648_);
    crate::leanh::lean_dec_ref(v_a_3647_);
    crate::leanh::lean_dec(v_a_3646_);
    crate::leanh::lean_dec_ref(v_a_3645_);
    return v_res_3650_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_FunIndCollect(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls =
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_FunIndCollect(
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
pub unsafe fn initialize_Lean_Meta_Tactic_FunIndCollect(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
}

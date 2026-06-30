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
pub static l_Lean_Meta_FunInd_instHashableCall___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_FunInd_instHashableCall_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_FunInd_instHashableCall___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instHashableCall___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_FunInd_instHashableCall: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instHashableCall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_FunInd_instBEqCall___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_FunInd_instBEqCall_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_FunInd_instBEqCall___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instBEqCall___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_FunInd_instBEqCall: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instBEqCall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value:
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
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0: u64 = 0;
static mut l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_Collector_visit___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_Collector_visit___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_Collector_main___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_Collector_main___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_FunInd_instHashableCall_hash(
    mut v_x_1826_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_expr_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u64 = 0;
    let mut v___x_1830_: u64 = 0;
    let mut v___x_1831_: u64 = 0;
    let mut v___x_1832_: u64 = 0;
    let mut v___x_1833_: u64 = 0;
    v_expr_1827_ = leanh::lean_ctor_get(v_x_1826_, 0);
    v_relevantArgs_1828_ = leanh::lean_ctor_get(v_x_1826_, 1);
    v___x_1829_ = 0u64;
    v___x_1830_ = l_Lean_Expr_hash(v_expr_1827_);
    v___x_1831_ = lean_uint64_mix_hash(v___x_1829_, v___x_1830_);
    v___x_1832_ = l_Lean_Expr_hash(v_relevantArgs_1828_);
    v___x_1833_ = lean_uint64_mix_hash(v___x_1831_, v___x_1832_);
    return v___x_1833_;
}
pub unsafe fn l_Lean_Meta_FunInd_instHashableCall_hash___boxed(
    mut v_x_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1835_: u64 = 0;
    let mut v_r_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lean_Meta_FunInd_instHashableCall_hash(v_x_1834_);
    leanh::lean_dec_ref(v_x_1834_);
    v_r_1836_ = leanh::lean_box_uint64(v_res_1835_);
    return v_r_1836_;
}
pub unsafe fn l_Lean_Meta_FunInd_instBEqCall_beq(
    mut v_x_1839_: *mut leanh::LeanObject,
    mut v_x_1840_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_expr_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    v_expr_1841_ = leanh::lean_ctor_get(v_x_1839_, 0);
    v_relevantArgs_1842_ = leanh::lean_ctor_get(v_x_1839_, 1);
    v_expr_1843_ = leanh::lean_ctor_get(v_x_1840_, 0);
    v_relevantArgs_1844_ = leanh::lean_ctor_get(v_x_1840_, 1);
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
    mut v_x_1847_: *mut leanh::LeanObject,
    mut v_x_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1849_: u8 = 0;
    let mut v_r_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_Meta_FunInd_instBEqCall_beq(v_x_1847_, v_x_1848_);
    leanh::lean_dec_ref(v_x_1848_);
    leanh::lean_dec_ref(v_x_1847_);
    v_r_1850_ = leanh::lean_box((v_res_1849_) as usize);
    return v_r_1850_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = leanh::lean_box(0);
    v___x_1856_ = leanh::lean_unsigned_to_nat(16);
    v___x_1857_ = lean_mk_array(v___x_1856_, v___x_1855_);
    return v___x_1857_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1,
    );
    v___x_1859_ = leanh::lean_unsigned_to_nat(0);
    v___x_1860_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    leanh::lean_ctor_set(v___x_1860_, 1, v___x_1858_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2,
    );
    v___x_1862_ = l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0;
    v___x_1863_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    leanh::lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls()
-> *mut leanh::LeanObject {
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3,
    );
    return v___x_1864_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_isEmpty(
    mut v_sc_1865_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_calls_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    v_calls_1866_ = leanh::lean_ctor_get(v_sc_1865_, 0);
    v___x_1867_ = lean_array_get_size(v_calls_1866_);
    v___x_1868_ = leanh::lean_unsigned_to_nat(0);
    v___x_1869_ = lean_nat_dec_eq(v___x_1867_, v___x_1868_);
    return v___x_1869_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(
    mut v_sc_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1871_: u8 = 0;
    let mut v_r_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_Meta_FunInd_SeenCalls_isEmpty(v_sc_1870_);
    leanh::lean_dec_ref(v_sc_1870_);
    v_r_1872_ = leanh::lean_box((v_res_1871_) as usize);
    return v_r_1872_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(
    mut v_xs_1873_: *mut leanh::LeanObject,
    mut v_ys_1874_: *mut leanh::LeanObject,
    mut v_x_1875_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1877_: u8 = 0;
    let mut v_one_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1876_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1877_ = lean_nat_dec_eq(v_x_1875_, v_zero_1876_);
                if v_isZero_1877_ == 1 {
                    leanh::lean_dec(v_x_1875_);
                    return v_isZero_1877_;
                } else {
                    v_one_1878_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1879_ = lean_nat_sub(v_x_1875_, v_one_1878_);
                    leanh::lean_dec(v_x_1875_);
                    v___x_1880_ = lean_array_fget_borrowed(v_xs_1873_, v_n_1879_);
                    v___x_1881_ = lean_array_fget_borrowed(v_ys_1874_, v_n_1879_);
                    v___x_1882_ = lean_expr_eqv(v___x_1880_, v___x_1881_);
                    if v___x_1882_ == 0 {
                        leanh::lean_dec(v_n_1879_);
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
    mut v_xs_1884_: *mut leanh::LeanObject,
    mut v_ys_1885_: *mut leanh::LeanObject,
    mut v_x_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1887_: u8 = 0;
    let mut v_r_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_1884_, v_ys_1885_, v_x_1886_);
    leanh::lean_dec_ref(v_ys_1885_);
    leanh::lean_dec_ref(v_xs_1884_);
    v_r_1888_ = leanh::lean_box((v_res_1887_) as usize);
    return v_r_1888_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(
    mut v_a_1889_: *mut leanh::LeanObject,
    mut v_x_1890_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1891_: u8 = 0;
    let mut v_key_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: u8 = 0;
    let mut v_fst_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1890_) == 0 {
                    v___x_1891_ = 0;
                    return v___x_1891_;
                } else {
                    v_key_1892_ = leanh::lean_ctor_get(v_x_1890_, 0);
                    v_tail_1893_ = leanh::lean_ctor_get(v_x_1890_, 2);
                    v_fst_1897_ = leanh::lean_ctor_get(v_key_1892_, 0);
                    v_snd_1898_ = leanh::lean_ctor_get(v_key_1892_, 1);
                    v_fst_1899_ = leanh::lean_ctor_get(v_a_1889_, 0);
                    v_snd_1900_ = leanh::lean_ctor_get(v_a_1889_, 1);
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
    mut v_a_1907_: *mut leanh::LeanObject,
    mut v_x_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1909_: u8 = 0;
    let mut v_r_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_1907_, v_x_1908_);
    leanh::lean_dec(v_x_1908_);
    leanh::lean_dec_ref(v_a_1907_);
    v_r_1910_ = leanh::lean_box((v_res_1909_) as usize);
    return v_r_1910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(
    mut v_as_1911_: *mut leanh::LeanObject,
    mut v_i_1912_: usize,
    mut v_stop_1913_: usize,
    mut v_b_1914_: u64,
) -> u64 {
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_as_1922_: *mut leanh::LeanObject,
    mut v_i_1923_: *mut leanh::LeanObject,
    mut v_stop_1924_: *mut leanh::LeanObject,
    mut v_b_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1926_: usize = 0;
    let mut v_stop_boxed_1927_: usize = 0;
    let mut v_b_boxed_1928_: u64 = 0;
    let mut v_res_1929_: u64 = 0;
    let mut v_r_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1926_ = leanh::lean_unbox_usize(v_i_1923_);
    leanh::lean_dec(v_i_1923_);
    v_stop_boxed_1927_ = leanh::lean_unbox_usize(v_stop_1924_);
    leanh::lean_dec(v_stop_1924_);
    v_b_boxed_1928_ = leanh::lean_unbox_uint64(v_b_1925_);
    leanh::lean_dec_ref(v_b_1925_);
    v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_as_1922_, v_i_boxed_1926_, v_stop_boxed_1927_, v_b_boxed_1928_);
    leanh::lean_dec_ref(v_as_1922_);
    v_r_1930_ = leanh::lean_box_uint64(v_res_1929_);
    return v_r_1930_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u64 = 0;
    v___x_1931_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1932_ = lean_uint64_of_nat(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(
    mut v_x_1933_: *mut leanh::LeanObject,
    mut v_x_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v_fst_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1966_: u64 = 0;
    let mut v___x_1967_: u64 = 0;
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v_x_1934_) == 0 {
                    return v_x_1933_;
                } else {
                    v_key_1935_ = leanh::lean_ctor_get(v_x_1934_, 0);
                    v_value_1936_ = leanh::lean_ctor_get(v_x_1934_, 1);
                    v_tail_1937_ = leanh::lean_ctor_get(v_x_1934_, 2);
                    v_isSharedCheck_1980_ = (!leanh::lean_is_exclusive(v_x_1934_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v___x_1939_ = v_x_1934_;
                        v_isShared_1940_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1937_);
                        leanh::lean_inc(v_value_1936_);
                        leanh::lean_inc(v_key_1935_);
                        leanh::lean_dec(v_x_1934_);
                        v___x_1939_ = leanh::lean_box(0);
                        v_isShared_1940_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1941_ = leanh::lean_ctor_get(v_key_1935_, 0);
                v_snd_1942_ = leanh::lean_ctor_get(v_key_1935_, 1);
                v___x_1943_ = lean_array_get_size(v_x_1933_);
                if leanh::lean_obj_tag(v_fst_1941_) == 0 {
                    v___x_1978_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_1966_ = v___x_1978_;
                    state = 4;
                    continue;
                } else {
                    v_hash_1979_ = leanh::lean_ctor_get_uint64(
                        v_fst_1941_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                leanh::lean_inc(v___x_1959_);
                if v_isShared_1940_ == 0 {
                    leanh::lean_ctor_set(v___x_1939_, 2, v___x_1959_);
                    v___x_1961_ = v___x_1939_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_key_1935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_value_1936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 2, v___x_1959_);
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
                v___x_1968_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_i_1981_: *mut leanh::LeanObject,
    mut v_source_1982_: *mut leanh::LeanObject,
    mut v_target_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v_es_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1984_ = lean_array_get_size(v_source_1982_);
                v___x_1985_ = lean_nat_dec_lt(v_i_1981_, v___x_1984_);
                if v___x_1985_ == 0 {
                    leanh::lean_dec_ref(v_source_1982_);
                    leanh::lean_dec(v_i_1981_);
                    return v_target_1983_;
                } else {
                    v_es_1986_ = lean_array_fget(v_source_1982_, v_i_1981_);
                    v___x_1987_ = leanh::lean_box(0);
                    v_source_1988_ = lean_array_fset(v_source_1982_, v_i_1981_, v___x_1987_);
                    v_target_1989_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_target_1983_, v_es_1986_);
                    v___x_1990_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1991_ = lean_nat_add(v_i_1981_, v___x_1990_);
                    leanh::lean_dec(v_i_1981_);
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
    mut v_data_1993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = lean_array_get_size(v_data_1993_);
    v___x_1995_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1996_ = lean_nat_mul(v___x_1994_, v___x_1995_);
    v___x_1997_ = leanh::lean_unsigned_to_nat(0);
    v___x_1998_ = leanh::lean_box(0);
    v___x_1999_ = lean_mk_array(v_nbuckets_1996_, v___x_1998_);
    v___x_2000_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_1997_, v_data_1993_, v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(
    mut v_m_2001_: *mut leanh::LeanObject,
    mut v_a_2002_: *mut leanh::LeanObject,
    mut v_b_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: u8 = 0;
    let mut v_val_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_unused_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2050_: u64 = 0;
    let mut v___x_2051_: u64 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v_size_2004_ = leanh::lean_ctor_get(v_m_2001_, 0);
                v_buckets_2005_ = leanh::lean_ctor_get(v_m_2001_, 1);
                v_fst_2006_ = leanh::lean_ctor_get(v_a_2002_, 0);
                v_snd_2007_ = leanh::lean_ctor_get(v_a_2002_, 1);
                v___x_2008_ = lean_array_get_size(v_buckets_2005_);
                if leanh::lean_obj_tag(v_fst_2006_) == 0 {
                    v___x_2062_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_2050_ = v___x_2062_;
                    state = 5;
                    continue;
                } else {
                    v_hash_2063_ = leanh::lean_ctor_get_uint64(
                        v_fst_2006_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    leanh::lean_inc_ref(v_buckets_2005_);
                    leanh::lean_inc(v_size_2004_);
                    v_isSharedCheck_2046_ = (!leanh::lean_is_exclusive(v_m_2001_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v_unused_2047_ = leanh::lean_ctor_get(v_m_2001_, 1);
                        leanh::lean_dec(v_unused_2047_);
                        v_unused_2048_ = leanh::lean_ctor_get(v_m_2001_, 0);
                        leanh::lean_dec(v_unused_2048_);
                        v___x_2027_ = v_m_2001_;
                        v_isShared_2028_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2001_);
                        v___x_2027_ = leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2003_);
                    leanh::lean_dec_ref(v_a_2002_);
                    return v_m_2001_;
                }
            }
            2 => {
                v___x_2029_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2030_ = lean_nat_add(v_size_2004_, v___x_2029_);
                leanh::lean_dec(v_size_2004_);
                leanh::lean_inc(v_bkt_2024_);
                v___x_2031_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2031_, 0, v_a_2002_);
                leanh::lean_ctor_set(v___x_2031_, 1, v_b_2003_);
                leanh::lean_ctor_set(v___x_2031_, 2, v_bkt_2024_);
                v_buckets_x27_2032_ = lean_array_uset(v_buckets_2005_, v___x_2023_, v___x_2031_);
                v___x_2033_ = leanh::lean_unsigned_to_nat(4);
                v___x_2034_ = lean_nat_mul(v_size_x27_2030_, v___x_2033_);
                v___x_2035_ = leanh::lean_unsigned_to_nat(3);
                v___x_2036_ = lean_nat_div(v___x_2034_, v___x_2035_);
                leanh::lean_dec(v___x_2034_);
                v___x_2037_ = lean_array_get_size(v_buckets_x27_2032_);
                v___x_2038_ = lean_nat_dec_le(v___x_2036_, v___x_2037_);
                leanh::lean_dec(v___x_2036_);
                if v___x_2038_ == 0 {
                    v_val_2039_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_2032_);
                    if v_isShared_2028_ == 0 {
                        leanh::lean_ctor_set(v___x_2027_, 1, v_val_2039_);
                        leanh::lean_ctor_set(v___x_2027_, 0, v_size_x27_2030_);
                        v___x_2041_ = v___x_2027_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2042_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_size_x27_2030_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_val_2039_);
                        v___x_2041_ = v_reuseFailAlloc_2042_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2028_ == 0 {
                        leanh::lean_ctor_set(v___x_2027_, 1, v_buckets_x27_2032_);
                        leanh::lean_ctor_set(v___x_2027_, 0, v_size_x27_2030_);
                        v___x_2044_ = v___x_2027_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2045_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_size_x27_2030_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_buckets_x27_2032_);
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
                v___x_2052_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_m_2064_: *mut leanh::LeanObject,
    mut v_a_2065_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    let mut v___y_2088_: u64 = 0;
    let mut v___x_2089_: u64 = 0;
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v_buckets_2066_ = leanh::lean_ctor_get(v_m_2064_, 1);
                v_fst_2067_ = leanh::lean_ctor_get(v_a_2065_, 0);
                v_snd_2068_ = leanh::lean_ctor_get(v_a_2065_, 1);
                v___x_2069_ = lean_array_get_size(v_buckets_2066_);
                if leanh::lean_obj_tag(v_fst_2067_) == 0 {
                    v___x_2100_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_2088_ = v___x_2100_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2101_ = leanh::lean_ctor_get_uint64(
                        v_fst_2067_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                v___x_2090_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_m_2102_: *mut leanh::LeanObject,
    mut v_a_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2104_: u8 = 0;
    let mut v_r_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_2102_, v_a_2103_);
    leanh::lean_dec_ref(v_a_2103_);
    leanh::lean_dec_ref(v_m_2102_);
    v_r_2105_ = leanh::lean_box((v_res_2104_) as usize);
    return v_r_2105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(
    mut v_calls_2106_: *mut leanh::LeanObject,
    mut v_as_2107_: *mut leanh::LeanObject,
    mut v_sz_2108_: usize,
    mut v_i_2109_: usize,
    mut v_b_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v_snd_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2127_: u8 = 0;
    let mut v_array_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v_a_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2171_: u8 = 0;
    let mut v_unused_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v_unused_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2117_ = lean_usize_dec_lt(v_i_2109_, v_sz_2108_);
                if v___x_2117_ == 0 {
                    leanh::lean_dec_ref(v_calls_2106_);
                    v___x_2118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2118_, 0, v_b_2110_);
                    return v___x_2118_;
                } else {
                    v_snd_2119_ = leanh::lean_ctor_get(v_b_2110_, 1);
                    v_isSharedCheck_2176_ = (!leanh::lean_is_exclusive(v_b_2110_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v_unused_2177_ = leanh::lean_ctor_get(v_b_2110_, 0);
                        leanh::lean_dec(v_unused_2177_);
                        v___x_2121_ = v_b_2110_;
                        v_isShared_2122_ = v_isSharedCheck_2176_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2119_);
                        leanh::lean_dec(v_b_2110_);
                        v___x_2121_ = leanh::lean_box(0);
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
                v_snd_2123_ = leanh::lean_ctor_get(v_snd_2119_, 1);
                v_fst_2124_ = leanh::lean_ctor_get(v_snd_2119_, 0);
                v_isSharedCheck_2175_ = (!leanh::lean_is_exclusive(v_snd_2119_)) as u8;
                if v_isSharedCheck_2175_ == 0 {
                    v___x_2126_ = v_snd_2119_;
                    v_isShared_2127_ = v_isSharedCheck_2175_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2123_);
                    leanh::lean_inc(v_fst_2124_);
                    leanh::lean_dec(v_snd_2119_);
                    v___x_2126_ = leanh::lean_box(0);
                    v_isShared_2127_ = v_isSharedCheck_2175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_2128_ = leanh::lean_ctor_get(v_snd_2123_, 0);
                v_start_2129_ = leanh::lean_ctor_get(v_snd_2123_, 1);
                v_stop_2130_ = leanh::lean_ctor_get(v_snd_2123_, 2);
                v___x_2131_ = leanh::lean_box(0);
                v___x_2132_ = lean_nat_dec_lt(v_start_2129_, v_stop_2130_);
                if v___x_2132_ == 0 {
                    leanh::lean_dec_ref(v_calls_2106_);
                    if v_isShared_2127_ == 0 {
                        v___x_2134_ = v___x_2126_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_fst_2124_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_snd_2123_);
                        v___x_2134_ = v_reuseFailAlloc_2139_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_2130_);
                    leanh::lean_inc(v_start_2129_);
                    leanh::lean_inc_ref(v_array_2128_);
                    v_isSharedCheck_2171_ = (!leanh::lean_is_exclusive(v_snd_2123_)) as u8;
                    if v_isSharedCheck_2171_ == 0 {
                        v_unused_2172_ = leanh::lean_ctor_get(v_snd_2123_, 2);
                        leanh::lean_dec(v_unused_2172_);
                        v_unused_2173_ = leanh::lean_ctor_get(v_snd_2123_, 1);
                        leanh::lean_dec(v_unused_2173_);
                        v_unused_2174_ = leanh::lean_ctor_get(v_snd_2123_, 0);
                        leanh::lean_dec(v_unused_2174_);
                        v___x_2141_ = v_snd_2123_;
                        v_isShared_2142_ = v_isSharedCheck_2171_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_2123_);
                        v___x_2141_ = leanh::lean_box(0);
                        v_isShared_2142_ = v_isSharedCheck_2171_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2122_ == 0 {
                    leanh::lean_ctor_set(v___x_2121_, 1, v___x_2134_);
                    leanh::lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2136_ = v___x_2121_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2131_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2134_);
                    v___x_2136_ = v_reuseFailAlloc_2138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2137_, 0, v___x_2136_);
                return v___x_2137_;
            }
            6 => {
                v_a_2143_ = lean_array_uget_borrowed(v_as_2107_, v_i_2109_);
                v___x_2144_ = lean_array_fget(v_array_2128_, v_start_2129_);
                v___x_2145_ = leanh::lean_unsigned_to_nat(1);
                v___x_2146_ = lean_nat_add(v_start_2129_, v___x_2145_);
                leanh::lean_dec(v_start_2129_);
                if v_isShared_2142_ == 0 {
                    leanh::lean_ctor_set(v___x_2141_, 1, v___x_2146_);
                    v___x_2148_ = v___x_2141_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2170_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_array_2128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_stop_2130_);
                    v___x_2148_ = v_reuseFailAlloc_2170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2164_ = (leanh::lean_unbox(v___x_2144_) as u8);
                if v___x_2164_ == 2 {
                    v___x_2165_ = l_Lean_Expr_isFVar(v_a_2143_);
                    if v___x_2165_ == 0 {
                        leanh::lean_dec(v___x_2144_);
                        leanh::lean_del_object(v___x_2126_);
                        leanh::lean_del_object(v___x_2121_);
                        v___x_2166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2166_, 0, v_calls_2106_);
                        v___x_2167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2167_, 0, v_fst_2124_);
                        leanh::lean_ctor_set(v___x_2167_, 1, v___x_2148_);
                        v___x_2168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2168_, 0, v___x_2166_);
                        leanh::lean_ctor_set(v___x_2168_, 1, v___x_2167_);
                        v___x_2169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2169_, 0, v___x_2168_);
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
                v___x_2150_ = (leanh::lean_unbox(v___x_2144_) as u8);
                leanh::lean_dec(v___x_2144_);
                if v___x_2150_ == 0 {
                    if v_isShared_2127_ == 0 {
                        leanh::lean_ctor_set(v___x_2126_, 1, v___x_2148_);
                        v___x_2152_ = v___x_2126_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_fst_2124_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2148_);
                        v___x_2152_ = v_reuseFailAlloc_2156_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_a_2143_);
                    v___x_2157_ = lean_array_push(v_fst_2124_, v_a_2143_);
                    if v_isShared_2127_ == 0 {
                        leanh::lean_ctor_set(v___x_2126_, 1, v___x_2148_);
                        leanh::lean_ctor_set(v___x_2126_, 0, v___x_2157_);
                        v___x_2159_ = v___x_2126_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2148_);
                        v___x_2159_ = v_reuseFailAlloc_2163_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2122_ == 0 {
                    leanh::lean_ctor_set(v___x_2121_, 1, v___x_2152_);
                    leanh::lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2154_ = v___x_2121_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2131_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2152_);
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
                    leanh::lean_ctor_set(v___x_2121_, 1, v___x_2159_);
                    leanh::lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2161_ = v___x_2121_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2162_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2131_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
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
    mut v_calls_2178_: *mut leanh::LeanObject,
    mut v_as_2179_: *mut leanh::LeanObject,
    mut v_sz_2180_: *mut leanh::LeanObject,
    mut v_i_2181_: *mut leanh::LeanObject,
    mut v_b_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2184_: usize = 0;
    let mut v_i_boxed_2185_: usize = 0;
    let mut v_res_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2184_ = leanh::lean_unbox_usize(v_sz_2180_);
    leanh::lean_dec(v_sz_2180_);
    v_i_boxed_2185_ = leanh::lean_unbox_usize(v_i_2181_);
    leanh::lean_dec(v_i_2181_);
    v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2178_, v_as_2179_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2182_);
    leanh::lean_dec_ref(v_as_2179_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_push(
    mut v_e_2187_: *mut leanh::LeanObject,
    mut v_funIndInfo_2188_: *mut leanh::LeanObject,
    mut v_args_2189_: *mut leanh::LeanObject,
    mut v_calls_2190_: *mut leanh::LeanObject,
    mut v_a_2191_: *mut leanh::LeanObject,
    mut v_a_2192_: *mut leanh::LeanObject,
    mut v_a_2193_: *mut leanh::LeanObject,
    mut v_a_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_funName_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2208_: usize = 0;
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v_fst_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v_calls_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_unused_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_unused_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_a_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_funName_2196_ = leanh::lean_ctor_get(v_funIndInfo_2188_, 0);
                leanh::lean_inc(v_funName_2196_);
                v_params_2197_ = leanh::lean_ctor_get(v_funIndInfo_2188_, 3);
                leanh::lean_inc_ref(v_params_2197_);
                leanh::lean_dec_ref(v_funIndInfo_2188_);
                v___x_2198_ = lean_array_get_size(v_params_2197_);
                v___x_2199_ = lean_array_get_size(v_args_2189_);
                v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
                if v___x_2200_ == 0 {
                    leanh::lean_dec_ref(v_params_2197_);
                    leanh::lean_dec(v_funName_2196_);
                    leanh::lean_dec_ref(v_e_2187_);
                    v___x_2201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2201_, 0, v_calls_2190_);
                    return v___x_2201_;
                } else {
                    v___x_2202_ = leanh::lean_unsigned_to_nat(0);
                    v_keys_2203_ = l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0;
                    v___x_2204_ =
                        l_Array_toSubarray___redArg(v_params_2197_, v___x_2202_, v___x_2198_);
                    v___x_2205_ = leanh::lean_box(0);
                    v___x_2206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2206_, 0, v_keys_2203_);
                    leanh::lean_ctor_set(v___x_2206_, 1, v___x_2204_);
                    v___x_2207_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2207_, 0, v___x_2205_);
                    leanh::lean_ctor_set(v___x_2207_, 1, v___x_2206_);
                    v_sz_2208_ = lean_array_size(v_args_2189_);
                    v___x_2209_ = 0usize;
                    leanh::lean_inc_ref(v_calls_2190_);
                    v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2190_, v_args_2189_, v_sz_2208_, v___x_2209_, v___x_2207_);
                    if leanh::lean_obj_tag(v___x_2210_) == 0 {
                        v_a_2211_ = leanh::lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2251_ =
                            (!leanh::lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2251_ == 0 {
                            v___x_2213_ = v___x_2210_;
                            v_isShared_2214_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2211_);
                            leanh::lean_dec(v___x_2210_);
                            v___x_2213_ = leanh::lean_box(0);
                            v_isShared_2214_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_funName_2196_);
                        leanh::lean_dec_ref(v_calls_2190_);
                        leanh::lean_dec_ref(v_e_2187_);
                        v_a_2252_ = leanh::lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2259_ =
                            (!leanh::lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2259_ == 0 {
                            v___x_2254_ = v___x_2210_;
                            v_isShared_2255_ = v_isSharedCheck_2259_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2252_);
                            leanh::lean_dec(v___x_2210_);
                            v___x_2254_ = leanh::lean_box(0);
                            v_isShared_2255_ = v_isSharedCheck_2259_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2215_ = leanh::lean_ctor_get(v_a_2211_, 0);
                if leanh::lean_obj_tag(v_fst_2215_) == 0 {
                    v_snd_2216_ = leanh::lean_ctor_get(v_a_2211_, 1);
                    leanh::lean_inc(v_snd_2216_);
                    leanh::lean_dec(v_a_2211_);
                    v_fst_2217_ = leanh::lean_ctor_get(v_snd_2216_, 0);
                    v_isSharedCheck_2245_ = (!leanh::lean_is_exclusive(v_snd_2216_)) as u8;
                    if v_isSharedCheck_2245_ == 0 {
                        v_unused_2246_ = leanh::lean_ctor_get(v_snd_2216_, 1);
                        leanh::lean_dec(v_unused_2246_);
                        v___x_2219_ = v_snd_2216_;
                        v_isShared_2220_ = v_isSharedCheck_2245_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2217_);
                        leanh::lean_dec(v_snd_2216_);
                        v___x_2219_ = leanh::lean_box(0);
                        v_isShared_2220_ = v_isSharedCheck_2245_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2215_);
                    leanh::lean_dec(v_a_2211_);
                    leanh::lean_dec(v_funName_2196_);
                    leanh::lean_dec_ref(v_calls_2190_);
                    leanh::lean_dec_ref(v_e_2187_);
                    v_val_2247_ = leanh::lean_ctor_get(v_fst_2215_, 0);
                    leanh::lean_inc(v_val_2247_);
                    leanh::lean_dec_ref_known(v_fst_2215_, 1);
                    if v_isShared_2214_ == 0 {
                        leanh::lean_ctor_set(v___x_2213_, 0, v_val_2247_);
                        v___x_2249_ = v___x_2213_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2250_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_val_2247_);
                        v___x_2249_ = v_reuseFailAlloc_2250_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_calls_2221_ = leanh::lean_ctor_get(v_calls_2190_, 0);
                v_seen_2222_ = leanh::lean_ctor_get(v_calls_2190_, 1);
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 1, v_fst_2217_);
                    leanh::lean_ctor_set(v___x_2219_, 0, v_funName_2196_);
                    v___x_2224_ = v___x_2219_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_funName_2196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_fst_2217_);
                    v___x_2224_ = v_reuseFailAlloc_2244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2225_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_2222_, v___x_2224_);
                if v___x_2225_ == 0 {
                    leanh::lean_inc_ref(v_seen_2222_);
                    leanh::lean_inc_ref(v_calls_2221_);
                    v_isSharedCheck_2238_ = (!leanh::lean_is_exclusive(v_calls_2190_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v_unused_2239_ = leanh::lean_ctor_get(v_calls_2190_, 1);
                        leanh::lean_dec(v_unused_2239_);
                        v_unused_2240_ = leanh::lean_ctor_get(v_calls_2190_, 0);
                        leanh::lean_dec(v_unused_2240_);
                        v___x_2227_ = v_calls_2190_;
                        v_isShared_2228_ = v_isSharedCheck_2238_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_calls_2190_);
                        v___x_2227_ = leanh::lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2238_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2224_);
                    leanh::lean_dec_ref(v_e_2187_);
                    if v_isShared_2214_ == 0 {
                        leanh::lean_ctor_set(v___x_2213_, 0, v_calls_2190_);
                        v___x_2242_ = v___x_2213_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_calls_2190_);
                        v___x_2242_ = v_reuseFailAlloc_2243_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2229_ = lean_array_push(v_calls_2221_, v_e_2187_);
                v___x_2230_ = leanh::lean_box(0);
                v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_2222_, v___x_2224_, v___x_2230_);
                if v_isShared_2228_ == 0 {
                    leanh::lean_ctor_set(v___x_2227_, 1, v___x_2231_);
                    leanh::lean_ctor_set(v___x_2227_, 0, v___x_2229_);
                    v___x_2233_ = v___x_2227_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2231_);
                    v___x_2233_ = v_reuseFailAlloc_2237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2214_ == 0 {
                    leanh::lean_ctor_set(v___x_2213_, 0, v___x_2233_);
                    v___x_2235_ = v___x_2213_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
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
                    v_reuseFailAlloc_2258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
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
    mut v_e_2260_: *mut leanh::LeanObject,
    mut v_funIndInfo_2261_: *mut leanh::LeanObject,
    mut v_args_2262_: *mut leanh::LeanObject,
    mut v_calls_2263_: *mut leanh::LeanObject,
    mut v_a_2264_: *mut leanh::LeanObject,
    mut v_a_2265_: *mut leanh::LeanObject,
    mut v_a_2266_: *mut leanh::LeanObject,
    mut v_a_2267_: *mut leanh::LeanObject,
    mut v_a_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2267_);
    leanh::lean_dec_ref(v_a_2266_);
    leanh::lean_dec(v_a_2265_);
    leanh::lean_dec_ref(v_a_2264_);
    leanh::lean_dec_ref(v_args_2262_);
    return v_res_2269_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(
    mut v_calls_2270_: *mut leanh::LeanObject,
    mut v_as_2271_: *mut leanh::LeanObject,
    mut v_sz_2272_: usize,
    mut v_i_2273_: usize,
    mut v_b_2274_: *mut leanh::LeanObject,
    mut v___y_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2270_, v_as_2271_, v_sz_2272_, v_i_2273_, v_b_2274_);
    return v___x_2280_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(
    mut v_calls_2281_: *mut leanh::LeanObject,
    mut v_as_2282_: *mut leanh::LeanObject,
    mut v_sz_2283_: *mut leanh::LeanObject,
    mut v_i_2284_: *mut leanh::LeanObject,
    mut v_b_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
    mut v___y_2290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2291_: usize = 0;
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_res_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2291_ = leanh::lean_unbox_usize(v_sz_2283_);
    leanh::lean_dec(v_sz_2283_);
    v_i_boxed_2292_ = leanh::lean_unbox_usize(v_i_2284_);
    leanh::lean_dec(v_i_2284_);
    v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_2281_, v_as_2282_, v_sz_boxed_2291_, v_i_boxed_2292_, v_b_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
    leanh::lean_dec(v___y_2289_);
    leanh::lean_dec_ref(v___y_2288_);
    leanh::lean_dec(v___y_2287_);
    leanh::lean_dec_ref(v___y_2286_);
    leanh::lean_dec_ref(v_as_2282_);
    return v_res_2293_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(
    mut v_00_u03b2_2294_: *mut leanh::LeanObject,
    mut v_m_2295_: *mut leanh::LeanObject,
    mut v_a_2296_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2297_: u8 = 0;
    v___x_2297_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_2295_, v_a_2296_);
    return v___x_2297_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(
    mut v_00_u03b2_2298_: *mut leanh::LeanObject,
    mut v_m_2299_: *mut leanh::LeanObject,
    mut v_a_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2301_: u8 = 0;
    let mut v_r_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(
            v_00_u03b2_2298_,
            v_m_2299_,
            v_a_2300_,
        );
    leanh::lean_dec_ref(v_a_2300_);
    leanh::lean_dec_ref(v_m_2299_);
    v_r_2302_ = leanh::lean_box((v_res_2301_) as usize);
    return v_r_2302_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(
    mut v_00_u03b2_2303_: *mut leanh::LeanObject,
    mut v_m_2304_: *mut leanh::LeanObject,
    mut v_a_2305_: *mut leanh::LeanObject,
    mut v_b_2306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_2304_, v_a_2305_, v_b_2306_);
    return v___x_2307_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(
    mut v_00_u03b2_2308_: *mut leanh::LeanObject,
    mut v_a_2309_: *mut leanh::LeanObject,
    mut v_x_2310_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2311_: u8 = 0;
    v___x_2311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_2309_, v_x_2310_);
    return v___x_2311_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(
    mut v_00_u03b2_2312_: *mut leanh::LeanObject,
    mut v_a_2313_: *mut leanh::LeanObject,
    mut v_x_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2315_: u8 = 0;
    let mut v_r_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_2312_, v_a_2313_, v_x_2314_);
    leanh::lean_dec(v_x_2314_);
    leanh::lean_dec_ref(v_a_2313_);
    v_r_2316_ = leanh::lean_box((v_res_2315_) as usize);
    return v_r_2316_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(
    mut v_00_u03b2_2317_: *mut leanh::LeanObject,
    mut v_data_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_2318_);
    return v___x_2319_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(
    mut v_xs_2320_: *mut leanh::LeanObject,
    mut v_ys_2321_: *mut leanh::LeanObject,
    mut v_hsz_2322_: *mut leanh::LeanObject,
    mut v_x_2323_: *mut leanh::LeanObject,
    mut v_x_2324_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2325_: u8 = 0;
    v___x_2325_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_2320_, v_ys_2321_, v_x_2323_);
    return v___x_2325_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(
    mut v_xs_2326_: *mut leanh::LeanObject,
    mut v_ys_2327_: *mut leanh::LeanObject,
    mut v_hsz_2328_: *mut leanh::LeanObject,
    mut v_x_2329_: *mut leanh::LeanObject,
    mut v_x_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2331_: u8 = 0;
    let mut v_r_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_2326_, v_ys_2327_, v_hsz_2328_, v_x_2329_, v_x_2330_);
    leanh::lean_dec_ref(v_ys_2327_);
    leanh::lean_dec_ref(v_xs_2326_);
    v_r_2332_ = leanh::lean_box((v_res_2331_) as usize);
    return v_r_2332_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(
    mut v_00_u03b2_2333_: *mut leanh::LeanObject,
    mut v_i_2334_: *mut leanh::LeanObject,
    mut v_source_2335_: *mut leanh::LeanObject,
    mut v_target_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_2334_, v_source_2335_, v_target_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(
    mut v_00_u03b2_2338_: *mut leanh::LeanObject,
    mut v_x_2339_: *mut leanh::LeanObject,
    mut v_x_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_2339_, v_x_2340_);
    return v___x_2341_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(
    mut v_snd_2342_: *mut leanh::LeanObject,
    mut v_x_2343_: *mut leanh::LeanObject,
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
    mut v_snd_2347_: *mut leanh::LeanObject,
    mut v_x_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2349_: u8 = 0;
    let mut v_r_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_2347_, v_x_2348_);
    leanh::lean_dec(v_x_2348_);
    leanh::lean_dec(v_snd_2347_);
    v_r_2350_ = leanh::lean_box((v_res_2349_) as usize);
    return v_r_2350_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(
    mut v_a_2351_: *mut leanh::LeanObject,
    mut v_a_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2351_) == 0 {
                    v___x_2353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2353_, 0, v_a_2352_);
                    return v___x_2353_;
                } else {
                    v_key_2354_ = leanh::lean_ctor_get(v_a_2351_, 0);
                    leanh::lean_inc(v_key_2354_);
                    v_tail_2355_ = leanh::lean_ctor_get(v_a_2351_, 2);
                    leanh::lean_inc(v_tail_2355_);
                    leanh::lean_dec_ref_known(v_a_2351_, 3);
                    v_fst_2356_ = leanh::lean_ctor_get(v_key_2354_, 0);
                    leanh::lean_inc(v_fst_2356_);
                    leanh::lean_dec(v_key_2354_);
                    v_fst_2357_ = leanh::lean_ctor_get(v_a_2352_, 0);
                    v_snd_2358_ = leanh::lean_ctor_get(v_a_2352_, 1);
                    v_isSharedCheck_2378_ = (!leanh::lean_is_exclusive(v_a_2352_)) as u8;
                    if v_isSharedCheck_2378_ == 0 {
                        v___x_2360_ = v_a_2352_;
                        v_isShared_2361_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2358_);
                        leanh::lean_inc(v_fst_2357_);
                        leanh::lean_dec(v_a_2352_);
                        v___x_2360_ = leanh::lean_box(0);
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
                            leanh::lean_ctor_set(v___x_2360_, 0, v___x_2364_);
                            v___x_2366_ = v___x_2360_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2368_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2364_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_snd_2358_);
                            v___x_2366_ = v_reuseFailAlloc_2368_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2369_ = l_Lean_NameSet_insert(v_snd_2358_, v_fst_2356_);
                        if v_isShared_2361_ == 0 {
                            leanh::lean_ctor_set(v___x_2360_, 1, v___x_2369_);
                            v___x_2371_ = v___x_2360_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2373_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_fst_2357_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2369_);
                            v___x_2371_ = v_reuseFailAlloc_2373_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_2356_);
                    if v_isShared_2361_ == 0 {
                        v___x_2375_ = v___x_2360_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_fst_2357_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_snd_2358_);
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
    mut v_as_2379_: *mut leanh::LeanObject,
    mut v_sz_2380_: usize,
    mut v_i_2381_: usize,
    mut v_b_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2383_: u8 = 0;
    let mut v_a_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_inc(v_a_2384_);
                    v___x_2385_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_2384_, v_b_2382_);
                    if leanh::lean_obj_tag(v___x_2385_) == 0 {
                        v_a_2386_ = leanh::lean_ctor_get(v___x_2385_, 0);
                        leanh::lean_inc(v_a_2386_);
                        leanh::lean_dec_ref_known(v___x_2385_, 1);
                        return v_a_2386_;
                    } else {
                        v_a_2387_ = leanh::lean_ctor_get(v___x_2385_, 0);
                        leanh::lean_inc(v_a_2387_);
                        leanh::lean_dec_ref_known(v___x_2385_, 1);
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
    mut v_as_2391_: *mut leanh::LeanObject,
    mut v_sz_2392_: *mut leanh::LeanObject,
    mut v_i_2393_: *mut leanh::LeanObject,
    mut v_b_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2395_: usize = 0;
    let mut v_i_boxed_2396_: usize = 0;
    let mut v_res_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2395_ = leanh::lean_unbox_usize(v_sz_2392_);
    leanh::lean_dec(v_sz_2392_);
    v_i_boxed_2396_ = leanh::lean_unbox_usize(v_i_2393_);
    leanh::lean_dec(v_i_2393_);
    v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_2391_, v_sz_boxed_2395_, v_i_boxed_2396_, v_b_2394_);
    leanh::lean_dec_ref(v_as_2391_);
    return v_res_2397_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0()
-> *mut leanh::LeanObject {
    let mut v_seen_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_seen_2398_ = l_Lean_NameSet_empty;
    v___x_2399_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2399_, 0, v_seen_2398_);
    leanh::lean_ctor_set(v___x_2399_, 1, v_seen_2398_);
    return v___x_2399_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques(
    mut v_calls_2400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_seen_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2404_: usize = 0;
    let mut v___x_2405_: usize = 0;
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_seen_2401_ = leanh::lean_ctor_get(v_calls_2400_, 1);
    v___x_2402_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once),
        _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0,
    );
    v_buckets_2403_ = leanh::lean_ctor_get(v_seen_2401_, 1);
    v_sz_2404_ = lean_array_size(v_buckets_2403_);
    v___x_2405_ = 0usize;
    v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_2403_, v_sz_2404_, v___x_2405_, v___x_2402_);
    v_fst_2407_ = leanh::lean_ctor_get(v___x_2406_, 0);
    leanh::lean_inc(v_fst_2407_);
    v_snd_2408_ = leanh::lean_ctor_get(v___x_2406_, 1);
    leanh::lean_inc(v_snd_2408_);
    leanh::lean_dec_ref(v___x_2406_);
    v___f_2409_ = leanh::lean_alloc_closure(
        l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2409_, 0, v_snd_2408_);
    v___x_2410_ = l_Lean_NameSet_filter(v___f_2409_, v_fst_2407_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(
    mut v_calls_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_2411_);
    leanh::lean_dec_ref(v_calls_2411_);
    return v_res_2412_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
    mut v_e_2413_: *mut leanh::LeanObject,
    mut v_funIndInfo_2414_: *mut leanh::LeanObject,
    mut v_args_2415_: *mut leanh::LeanObject,
    mut v_a_2416_: *mut leanh::LeanObject,
    mut v_a_2417_: *mut leanh::LeanObject,
    mut v_a_2418_: *mut leanh::LeanObject,
    mut v_a_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut v_a_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2423_) == 0 {
                    v_a_2424_ = leanh::lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2432_ = (!leanh::lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2432_ == 0 {
                        v___x_2426_ = v___x_2423_;
                        v_isShared_2427_ = v_isSharedCheck_2432_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2424_);
                        leanh::lean_dec(v___x_2423_);
                        v___x_2426_ = leanh::lean_box(0);
                        v_isShared_2427_ = v_isSharedCheck_2432_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2433_ = leanh::lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2440_ = (!leanh::lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2440_ == 0 {
                        v___x_2435_ = v___x_2423_;
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2433_);
                        leanh::lean_dec(v___x_2423_);
                        v___x_2435_ = leanh::lean_box(0);
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2428_ = lean_st_ref_set(v_a_2416_, v_a_2424_);
                if v_isShared_2427_ == 0 {
                    leanh::lean_ctor_set(v___x_2426_, 0, v___x_2428_);
                    v___x_2430_ = v___x_2426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
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
                    v_reuseFailAlloc_2439_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
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
    mut v_e_2441_: *mut leanh::LeanObject,
    mut v_funIndInfo_2442_: *mut leanh::LeanObject,
    mut v_args_2443_: *mut leanh::LeanObject,
    mut v_a_2444_: *mut leanh::LeanObject,
    mut v_a_2445_: *mut leanh::LeanObject,
    mut v_a_2446_: *mut leanh::LeanObject,
    mut v_a_2447_: *mut leanh::LeanObject,
    mut v_a_2448_: *mut leanh::LeanObject,
    mut v_a_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2448_);
    leanh::lean_dec_ref(v_a_2447_);
    leanh::lean_dec(v_a_2446_);
    leanh::lean_dec_ref(v_a_2445_);
    leanh::lean_dec(v_a_2444_);
    leanh::lean_dec_ref(v_args_2443_);
    return v_res_2450_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd(
    mut v_e_2451_: *mut leanh::LeanObject,
    mut v_funIndInfo_2452_: *mut leanh::LeanObject,
    mut v_args_2453_: *mut leanh::LeanObject,
    mut v_a_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_a_2456_: *mut leanh::LeanObject,
    mut v_a_2457_: *mut leanh::LeanObject,
    mut v_a_2458_: *mut leanh::LeanObject,
    mut v_a_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_2462_: *mut leanh::LeanObject,
    mut v_funIndInfo_2463_: *mut leanh::LeanObject,
    mut v_args_2464_: *mut leanh::LeanObject,
    mut v_a_2465_: *mut leanh::LeanObject,
    mut v_a_2466_: *mut leanh::LeanObject,
    mut v_a_2467_: *mut leanh::LeanObject,
    mut v_a_2468_: *mut leanh::LeanObject,
    mut v_a_2469_: *mut leanh::LeanObject,
    mut v_a_2470_: *mut leanh::LeanObject,
    mut v_a_2471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2470_);
    leanh::lean_dec_ref(v_a_2469_);
    leanh::lean_dec(v_a_2468_);
    leanh::lean_dec_ref(v_a_2467_);
    leanh::lean_dec(v_a_2466_);
    leanh::lean_dec_ref(v_a_2465_);
    leanh::lean_dec_ref(v_args_2464_);
    return v_res_2472_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp___redArg(
    mut v_e_2473_: *mut leanh::LeanObject,
    mut v_funIndInfo_2474_: *mut leanh::LeanObject,
    mut v_args_2475_: *mut leanh::LeanObject,
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_a_2477_: *mut leanh::LeanObject,
    mut v_a_2478_: *mut leanh::LeanObject,
    mut v_a_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_2483_: *mut leanh::LeanObject,
    mut v_funIndInfo_2484_: *mut leanh::LeanObject,
    mut v_args_2485_: *mut leanh::LeanObject,
    mut v_a_2486_: *mut leanh::LeanObject,
    mut v_a_2487_: *mut leanh::LeanObject,
    mut v_a_2488_: *mut leanh::LeanObject,
    mut v_a_2489_: *mut leanh::LeanObject,
    mut v_a_2490_: *mut leanh::LeanObject,
    mut v_a_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2490_);
    leanh::lean_dec_ref(v_a_2489_);
    leanh::lean_dec(v_a_2488_);
    leanh::lean_dec_ref(v_a_2487_);
    leanh::lean_dec(v_a_2486_);
    leanh::lean_dec_ref(v_args_2485_);
    return v_res_2492_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp(
    mut v_e_2493_: *mut leanh::LeanObject,
    mut v_funIndInfo_2494_: *mut leanh::LeanObject,
    mut v_args_2495_: *mut leanh::LeanObject,
    mut v_a_2496_: *mut leanh::LeanObject,
    mut v_a_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
    mut v_a_2501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_2504_: *mut leanh::LeanObject,
    mut v_funIndInfo_2505_: *mut leanh::LeanObject,
    mut v_args_2506_: *mut leanh::LeanObject,
    mut v_a_2507_: *mut leanh::LeanObject,
    mut v_a_2508_: *mut leanh::LeanObject,
    mut v_a_2509_: *mut leanh::LeanObject,
    mut v_a_2510_: *mut leanh::LeanObject,
    mut v_a_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2512_);
    leanh::lean_dec_ref(v_a_2511_);
    leanh::lean_dec(v_a_2510_);
    leanh::lean_dec_ref(v_a_2509_);
    leanh::lean_dec(v_a_2508_);
    leanh::lean_dec_ref(v_a_2507_);
    leanh::lean_dec_ref(v_args_2506_);
    return v_res_2514_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_2515_: *mut leanh::LeanObject,
    mut v_x_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2516_) == 0 {
                    return v_x_2515_;
                } else {
                    v_key_2517_ = leanh::lean_ctor_get(v_x_2516_, 0);
                    v_value_2518_ = leanh::lean_ctor_get(v_x_2516_, 1);
                    v_tail_2519_ = leanh::lean_ctor_get(v_x_2516_, 2);
                    v_isSharedCheck_2545_ = (!leanh::lean_is_exclusive(v_x_2516_)) as u8;
                    if v_isSharedCheck_2545_ == 0 {
                        v___x_2521_ = v_x_2516_;
                        v_isShared_2522_ = v_isSharedCheck_2545_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2519_);
                        leanh::lean_inc(v_value_2518_);
                        leanh::lean_inc(v_key_2517_);
                        leanh::lean_dec(v_x_2516_);
                        v___x_2521_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_2539_);
                if v_isShared_2522_ == 0 {
                    leanh::lean_ctor_set(v___x_2521_, 2, v___x_2539_);
                    v___x_2541_ = v___x_2521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_key_2517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_value_2518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 2, v___x_2539_);
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
    mut v_i_2546_: *mut leanh::LeanObject,
    mut v_source_2547_: *mut leanh::LeanObject,
    mut v_target_2548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u8 = 0;
    let mut v_es_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2549_ = lean_array_get_size(v_source_2547_);
                v___x_2550_ = lean_nat_dec_lt(v_i_2546_, v___x_2549_);
                if v___x_2550_ == 0 {
                    leanh::lean_dec_ref(v_source_2547_);
                    leanh::lean_dec(v_i_2546_);
                    return v_target_2548_;
                } else {
                    v_es_2551_ = lean_array_fget(v_source_2547_, v_i_2546_);
                    v___x_2552_ = leanh::lean_box(0);
                    v_source_2553_ = lean_array_fset(v_source_2547_, v_i_2546_, v___x_2552_);
                    v_target_2554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_2548_, v_es_2551_);
                    v___x_2555_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2556_ = lean_nat_add(v_i_2546_, v___x_2555_);
                    leanh::lean_dec(v_i_2546_);
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
    mut v_data_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2559_ = lean_array_get_size(v_data_2558_);
    v___x_2560_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2561_ = lean_nat_mul(v___x_2559_, v___x_2560_);
    v___x_2562_ = leanh::lean_unsigned_to_nat(0);
    v___x_2563_ = leanh::lean_box(0);
    v___x_2564_ = lean_mk_array(v_nbuckets_2561_, v___x_2563_);
    v___x_2565_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_2562_, v_data_2558_, v___x_2564_);
    return v___x_2565_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(
    mut v_a_2566_: *mut leanh::LeanObject,
    mut v_x_2567_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2568_: u8 = 0;
    let mut v_key_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2567_) == 0 {
                    v___x_2568_ = 0;
                    return v___x_2568_;
                } else {
                    v_key_2569_ = leanh::lean_ctor_get(v_x_2567_, 0);
                    v_tail_2570_ = leanh::lean_ctor_get(v_x_2567_, 2);
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
    mut v_a_2575_: *mut leanh::LeanObject,
    mut v_x_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2577_: u8 = 0;
    let mut v_r_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2575_, v_x_2576_);
    leanh::lean_dec(v_x_2576_);
    leanh::lean_dec_ref(v_a_2575_);
    v_r_2578_ = leanh::lean_box((v_res_2577_) as usize);
    return v_r_2578_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(
    mut v_m_2579_: *mut leanh::LeanObject,
    mut v_a_2580_: *mut leanh::LeanObject,
    mut v_b_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v_val_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2622_: u8 = 0;
    let mut v_unused_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2582_ = leanh::lean_ctor_get(v_m_2579_, 0);
                v_buckets_2583_ = leanh::lean_ctor_get(v_m_2579_, 1);
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
                    leanh::lean_inc_ref(v_buckets_2583_);
                    leanh::lean_inc(v_size_2582_);
                    v_isSharedCheck_2622_ = (!leanh::lean_is_exclusive(v_m_2579_)) as u8;
                    if v_isSharedCheck_2622_ == 0 {
                        v_unused_2623_ = leanh::lean_ctor_get(v_m_2579_, 1);
                        leanh::lean_dec(v_unused_2623_);
                        v_unused_2624_ = leanh::lean_ctor_get(v_m_2579_, 0);
                        leanh::lean_dec(v_unused_2624_);
                        v___x_2603_ = v_m_2579_;
                        v_isShared_2604_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2579_);
                        v___x_2603_ = leanh::lean_box(0);
                        v_isShared_2604_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2581_);
                    leanh::lean_dec_ref(v_a_2580_);
                    return v_m_2579_;
                }
            }
            1 => {
                v___x_2605_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2606_ = lean_nat_add(v_size_2582_, v___x_2605_);
                leanh::lean_dec(v_size_2582_);
                leanh::lean_inc(v_bkt_2600_);
                v___x_2607_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2607_, 0, v_a_2580_);
                leanh::lean_ctor_set(v___x_2607_, 1, v_b_2581_);
                leanh::lean_ctor_set(v___x_2607_, 2, v_bkt_2600_);
                v_buckets_x27_2608_ = lean_array_uset(v_buckets_2583_, v___x_2599_, v___x_2607_);
                v___x_2609_ = leanh::lean_unsigned_to_nat(4);
                v___x_2610_ = lean_nat_mul(v_size_x27_2606_, v___x_2609_);
                v___x_2611_ = leanh::lean_unsigned_to_nat(3);
                v___x_2612_ = lean_nat_div(v___x_2610_, v___x_2611_);
                leanh::lean_dec(v___x_2610_);
                v___x_2613_ = lean_array_get_size(v_buckets_x27_2608_);
                v___x_2614_ = lean_nat_dec_le(v___x_2612_, v___x_2613_);
                leanh::lean_dec(v___x_2612_);
                if v___x_2614_ == 0 {
                    v_val_2615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_2608_);
                    if v_isShared_2604_ == 0 {
                        leanh::lean_ctor_set(v___x_2603_, 1, v_val_2615_);
                        leanh::lean_ctor_set(v___x_2603_, 0, v_size_x27_2606_);
                        v___x_2617_ = v___x_2603_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2618_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_size_x27_2606_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_val_2615_);
                        v___x_2617_ = v_reuseFailAlloc_2618_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2604_ == 0 {
                        leanh::lean_ctor_set(v___x_2603_, 1, v_buckets_x27_2608_);
                        leanh::lean_ctor_set(v___x_2603_, 0, v_size_x27_2606_);
                        v___x_2620_ = v___x_2603_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2621_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_size_x27_2606_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_buckets_x27_2608_);
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
    mut v_m_2625_: *mut leanh::LeanObject,
    mut v_a_2626_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    v_buckets_2627_ = leanh::lean_ctor_get(v_m_2625_, 1);
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
    mut v_m_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2648_: u8 = 0;
    let mut v_r_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_2646_, v_a_2647_);
    leanh::lean_dec_ref(v_a_2647_);
    leanh::lean_dec_ref(v_m_2646_);
    v_r_2649_ = leanh::lean_box((v_res_2648_) as usize);
    return v_r_2649_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_Collector_visit___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = leanh::lean_box(0);
    v_dummy_2651_ = l_Lean_Expr_sort___override(v___x_2650_);
    return v_dummy_2651_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(
    mut v_e_2652_: *mut leanh::LeanObject,
    mut v_x_2653_: *mut leanh::LeanObject,
    mut v_x_2654_: *mut leanh::LeanObject,
    mut v_x_2655_: *mut leanh::LeanObject,
    mut v___y_2656_: *mut leanh::LeanObject,
    mut v___y_2657_: *mut leanh::LeanObject,
    mut v___y_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
    mut v___y_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: u8 = 0;
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: usize = 0;
    let mut v___x_2680_: usize = 0;
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: usize = 0;
    let mut v___x_2683_: usize = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u8 = 0;
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2653_) == 5 {
                    v_fn_2685_ = leanh::lean_ctor_get(v_x_2653_, 0);
                    leanh::lean_inc_ref(v_fn_2685_);
                    v_arg_2686_ = leanh::lean_ctor_get(v_x_2653_, 1);
                    leanh::lean_inc_ref(v_arg_2686_);
                    leanh::lean_dec_ref_known(v_x_2653_, 2);
                    v___x_2687_ = lean_array_set(v_x_2654_, v_x_2655_, v_arg_2686_);
                    v___x_2688_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2689_ = lean_nat_sub(v_x_2655_, v___x_2688_);
                    leanh::lean_dec(v_x_2655_);
                    v_x_2653_ = v_fn_2685_;
                    v_x_2654_ = v___x_2687_;
                    v_x_2655_ = v___x_2689_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_2655_);
                    if leanh::lean_obj_tag(v_x_2653_) == 4 {
                        v_declName_2691_ = leanh::lean_ctor_get(v_x_2653_, 0);
                        leanh::lean_inc(v_declName_2691_);
                        leanh::lean_dec_ref_known(v_x_2653_, 2);
                        v_funName_2692_ = leanh::lean_ctor_get(v___y_2657_, 0);
                        v___x_2693_ = lean_name_eq(v_declName_2691_, v_funName_2692_);
                        leanh::lean_dec(v_declName_2691_);
                        if v___x_2693_ == 0 {
                            leanh::lean_dec_ref(v_e_2652_);
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
                                leanh::lean_inc_ref(v___y_2657_);
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
                                if leanh::lean_obj_tag(v___x_2695_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2695_, 1);
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
                                    leanh::lean_dec_ref(v_x_2654_);
                                    return v___x_2695_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_e_2652_);
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
                        leanh::lean_dec_ref(v_e_2652_);
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
                        if leanh::lean_obj_tag(v___x_2696_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2696_, 1);
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
                            leanh::lean_dec_ref(v_x_2654_);
                            return v___x_2696_;
                        }
                    }
                }
            }
            1 => {
                v___x_2672_ = leanh::lean_unsigned_to_nat(0);
                v___x_2673_ = lean_array_get_size(v_x_2654_);
                v___x_2674_ = leanh::lean_box(0);
                v___x_2675_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
                if v___x_2675_ == 0 {
                    leanh::lean_dec_ref(v_x_2654_);
                    v___x_2676_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2676_, 0, v___x_2674_);
                    return v___x_2676_;
                } else {
                    v___x_2677_ = lean_nat_dec_le(v___x_2673_, v___x_2673_);
                    if v___x_2677_ == 0 {
                        if v___x_2675_ == 0 {
                            leanh::lean_dec_ref(v_x_2654_);
                            v___x_2678_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2678_, 0, v___x_2674_);
                            return v___x_2678_;
                        } else {
                            v___x_2679_ = 0usize;
                            v___x_2680_ = lean_usize_of_nat(v___x_2673_);
                            v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_2654_, v___x_2679_, v___x_2680_, v___x_2674_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
                            leanh::lean_dec_ref(v_x_2654_);
                            return v___x_2681_;
                        }
                    } else {
                        v___x_2682_ = 0usize;
                        v___x_2683_ = lean_usize_of_nat(v___x_2673_);
                        v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_2654_, v___x_2682_, v___x_2683_, v___x_2674_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
                        leanh::lean_dec_ref(v_x_2654_);
                        return v___x_2684_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visit(
    mut v_e_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
    mut v_a_2699_: *mut leanh::LeanObject,
    mut v_a_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
    mut v_a_2703_: *mut leanh::LeanObject,
    mut v_a_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2706_ = lean_st_ref_get(v_a_2698_);
                v___x_2707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_2706_, v_e_2697_);
                leanh::lean_dec(v___x_2706_);
                if v___x_2707_ == 0 {
                    v___x_2708_ = lean_st_ref_take(v_a_2698_);
                    v___x_2709_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_e_2697_);
                    v___x_2710_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_2708_, v_e_2697_, v___x_2709_);
                    v___x_2711_ = lean_st_ref_set(v_a_2698_, v___x_2710_);
                    match leanh::lean_obj_tag(v_e_2697_) {
                        4 => {
                            leanh::lean_dec_ref_known(v_e_2697_, 2);
                            v___x_2724_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2724_, 0, v___x_2709_);
                            return v___x_2724_;
                        }
                        7 => {
                            v_binderType_2725_ = leanh::lean_ctor_get(v_e_2697_, 1);
                            leanh::lean_inc_ref(v_binderType_2725_);
                            v_body_2726_ = leanh::lean_ctor_get(v_e_2697_, 2);
                            leanh::lean_inc_ref(v_body_2726_);
                            leanh::lean_dec_ref_known(v_e_2697_, 3);
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
                            v_binderType_2727_ = leanh::lean_ctor_get(v_e_2697_, 1);
                            leanh::lean_inc_ref(v_binderType_2727_);
                            v_body_2728_ = leanh::lean_ctor_get(v_e_2697_, 2);
                            leanh::lean_inc_ref(v_body_2728_);
                            leanh::lean_dec_ref_known(v_e_2697_, 3);
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
                            v_expr_2729_ = leanh::lean_ctor_get(v_e_2697_, 1);
                            leanh::lean_inc_ref(v_expr_2729_);
                            leanh::lean_dec_ref_known(v_e_2697_, 2);
                            v_e_2697_ = v_expr_2729_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_2731_ = leanh::lean_ctor_get(v_e_2697_, 1);
                            leanh::lean_inc_ref(v_type_2731_);
                            v_value_2732_ = leanh::lean_ctor_get(v_e_2697_, 2);
                            leanh::lean_inc_ref(v_value_2732_);
                            v_body_2733_ = leanh::lean_ctor_get(v_e_2697_, 3);
                            leanh::lean_inc_ref(v_body_2733_);
                            leanh::lean_dec_ref_known(v_e_2697_, 4);
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
                            if leanh::lean_obj_tag(v___x_2734_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2734_, 1);
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
                                if leanh::lean_obj_tag(v___x_2735_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2735_, 1);
                                    v_e_2697_ = v_body_2733_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_body_2733_);
                                    return v___x_2735_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_2733_);
                                leanh::lean_dec_ref(v_value_2732_);
                                return v___x_2734_;
                            }
                        }
                        5 => {
                            v_dummy_2737_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_FunInd_Collector_visit___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_FunInd_Collector_visit___closed__0_once
                                ),
                                _init_l_Lean_Meta_FunInd_Collector_visit___closed__0,
                            );
                            v_nargs_2738_ = l_Lean_Expr_getAppNumArgs(v_e_2697_);
                            leanh::lean_inc(v_nargs_2738_);
                            v___x_2739_ = lean_mk_array(v_nargs_2738_, v_dummy_2737_);
                            v___x_2740_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2741_ = lean_nat_sub(v_nargs_2738_, v___x_2740_);
                            leanh::lean_dec(v_nargs_2738_);
                            leanh::lean_inc_ref(v_e_2697_);
                            v___x_2742_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_2697_, v_e_2697_, v___x_2739_, v___x_2741_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
                            return v___x_2742_;
                        }
                        11 => {
                            v_struct_2743_ = leanh::lean_ctor_get(v_e_2697_, 2);
                            leanh::lean_inc_ref(v_struct_2743_);
                            leanh::lean_dec_ref_known(v_e_2697_, 3);
                            v_e_2697_ = v_struct_2743_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_e_2697_);
                            v___x_2745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2745_, 0, v___x_2709_);
                            return v___x_2745_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2697_);
                    v___x_2746_ = leanh::lean_box(0);
                    v___x_2747_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2747_, 0, v___x_2746_);
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
                if leanh::lean_obj_tag(v___x_2722_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2722_, 1);
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
                    leanh::lean_dec_ref(v_b_2714_);
                    return v___x_2722_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(
    mut v_as_2748_: *mut leanh::LeanObject,
    mut v_i_2749_: usize,
    mut v_stop_2750_: usize,
    mut v_b_2751_: *mut leanh::LeanObject,
    mut v___y_2752_: *mut leanh::LeanObject,
    mut v___y_2753_: *mut leanh::LeanObject,
    mut v___y_2754_: *mut leanh::LeanObject,
    mut v___y_2755_: *mut leanh::LeanObject,
    mut v___y_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2760_ = lean_usize_dec_eq(v_i_2749_, v_stop_2750_);
                if v___x_2760_ == 0 {
                    v___x_2761_ = lean_array_uget_borrowed(v_as_2748_, v_i_2749_);
                    leanh::lean_inc(v___x_2761_);
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
                    if leanh::lean_obj_tag(v___x_2762_) == 0 {
                        v_a_2763_ = leanh::lean_ctor_get(v___x_2762_, 0);
                        leanh::lean_inc(v_a_2763_);
                        leanh::lean_dec_ref_known(v___x_2762_, 1);
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
                    v___x_2767_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2767_, 0, v_b_2751_);
                    return v___x_2767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(
    mut v_as_2768_: *mut leanh::LeanObject,
    mut v_i_2769_: *mut leanh::LeanObject,
    mut v_stop_2770_: *mut leanh::LeanObject,
    mut v_b_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
    mut v___y_2774_: *mut leanh::LeanObject,
    mut v___y_2775_: *mut leanh::LeanObject,
    mut v___y_2776_: *mut leanh::LeanObject,
    mut v___y_2777_: *mut leanh::LeanObject,
    mut v___y_2778_: *mut leanh::LeanObject,
    mut v___y_2779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2780_: usize = 0;
    let mut v_stop_boxed_2781_: usize = 0;
    let mut v_res_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2780_ = leanh::lean_unbox_usize(v_i_2769_);
    leanh::lean_dec(v_i_2769_);
    v_stop_boxed_2781_ = leanh::lean_unbox_usize(v_stop_2770_);
    leanh::lean_dec(v_stop_2770_);
    v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_2768_, v_i_boxed_2780_, v_stop_boxed_2781_, v_b_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
    leanh::lean_dec(v___y_2778_);
    leanh::lean_dec_ref(v___y_2777_);
    leanh::lean_dec(v___y_2776_);
    leanh::lean_dec_ref(v___y_2775_);
    leanh::lean_dec(v___y_2774_);
    leanh::lean_dec_ref(v___y_2773_);
    leanh::lean_dec(v___y_2772_);
    leanh::lean_dec_ref(v_as_2768_);
    return v_res_2782_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visit___boxed(
    mut v_e_2783_: *mut leanh::LeanObject,
    mut v_a_2784_: *mut leanh::LeanObject,
    mut v_a_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
    mut v_a_2789_: *mut leanh::LeanObject,
    mut v_a_2790_: *mut leanh::LeanObject,
    mut v_a_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_Meta_FunInd_Collector_visit(
        v_e_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_,
    );
    leanh::lean_dec(v_a_2790_);
    leanh::lean_dec_ref(v_a_2789_);
    leanh::lean_dec(v_a_2788_);
    leanh::lean_dec_ref(v_a_2787_);
    leanh::lean_dec(v_a_2786_);
    leanh::lean_dec_ref(v_a_2785_);
    leanh::lean_dec(v_a_2784_);
    return v_res_2792_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(
    mut v_e_2793_: *mut leanh::LeanObject,
    mut v_x_2794_: *mut leanh::LeanObject,
    mut v_x_2795_: *mut leanh::LeanObject,
    mut v_x_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
    mut v___y_2799_: *mut leanh::LeanObject,
    mut v___y_2800_: *mut leanh::LeanObject,
    mut v___y_2801_: *mut leanh::LeanObject,
    mut v___y_2802_: *mut leanh::LeanObject,
    mut v___y_2803_: *mut leanh::LeanObject,
    mut v___y_2804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2803_);
    leanh::lean_dec_ref(v___y_2802_);
    leanh::lean_dec(v___y_2801_);
    leanh::lean_dec_ref(v___y_2800_);
    leanh::lean_dec(v___y_2799_);
    leanh::lean_dec_ref(v___y_2798_);
    leanh::lean_dec(v___y_2797_);
    return v_res_2805_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(
    mut v_00_u03b2_2806_: *mut leanh::LeanObject,
    mut v_m_2807_: *mut leanh::LeanObject,
    mut v_a_2808_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2809_: u8 = 0;
    v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_2807_, v_a_2808_);
    return v___x_2809_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(
    mut v_00_u03b2_2810_: *mut leanh::LeanObject,
    mut v_m_2811_: *mut leanh::LeanObject,
    mut v_a_2812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2813_: u8 = 0;
    let mut v_r_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2813_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_2810_, v_m_2811_, v_a_2812_);
    leanh::lean_dec_ref(v_a_2812_);
    leanh::lean_dec_ref(v_m_2811_);
    v_r_2814_ = leanh::lean_box((v_res_2813_) as usize);
    return v_r_2814_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(
    mut v_00_u03b2_2815_: *mut leanh::LeanObject,
    mut v_m_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
    mut v_b_2818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_2816_, v_a_2817_, v_b_2818_);
    return v___x_2819_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(
    mut v_00_u03b2_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
    mut v_x_2822_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2823_: u8 = 0;
    v___x_2823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2821_, v_x_2822_);
    return v___x_2823_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(
    mut v_00_u03b2_2824_: *mut leanh::LeanObject,
    mut v_a_2825_: *mut leanh::LeanObject,
    mut v_x_2826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2827_: u8 = 0;
    let mut v_r_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_2824_, v_a_2825_, v_x_2826_);
    leanh::lean_dec(v_x_2826_);
    leanh::lean_dec_ref(v_a_2825_);
    v_r_2828_ = leanh::lean_box((v_res_2827_) as usize);
    return v_r_2828_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(
    mut v_00_u03b2_2829_: *mut leanh::LeanObject,
    mut v_data_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_2830_);
    return v___x_2831_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2832_: *mut leanh::LeanObject,
    mut v_i_2833_: *mut leanh::LeanObject,
    mut v_source_2834_: *mut leanh::LeanObject,
    mut v_target_2835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2836_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_2833_, v_source_2834_, v_target_2835_);
    return v___x_2836_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_2837_: *mut leanh::LeanObject,
    mut v_x_2838_: *mut leanh::LeanObject,
    mut v_x_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_2838_, v_x_2839_);
    return v___x_2840_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(
    mut v_e_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2864_: u8 = 0;
    let mut v_unused_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2844_ = l_Lean_Expr_hasMVar(v_e_2841_);
                if v___x_2844_ == 0 {
                    v___x_2845_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2845_, 0, v_e_2841_);
                    return v___x_2845_;
                } else {
                    v___x_2846_ = lean_st_ref_get(v___y_2842_);
                    v_mctx_2847_ = leanh::lean_ctor_get(v___x_2846_, 0);
                    leanh::lean_inc_ref(v_mctx_2847_);
                    leanh::lean_dec(v___x_2846_);
                    v___x_2848_ = l_Lean_instantiateMVarsCore(v_mctx_2847_, v_e_2841_);
                    v_fst_2849_ = leanh::lean_ctor_get(v___x_2848_, 0);
                    leanh::lean_inc(v_fst_2849_);
                    v_snd_2850_ = leanh::lean_ctor_get(v___x_2848_, 1);
                    leanh::lean_inc(v_snd_2850_);
                    leanh::lean_dec_ref(v___x_2848_);
                    v___x_2851_ = lean_st_ref_take(v___y_2842_);
                    v_cache_2852_ = leanh::lean_ctor_get(v___x_2851_, 1);
                    v_zetaDeltaFVarIds_2853_ = leanh::lean_ctor_get(v___x_2851_, 2);
                    v_postponed_2854_ = leanh::lean_ctor_get(v___x_2851_, 3);
                    v_diag_2855_ = leanh::lean_ctor_get(v___x_2851_, 4);
                    v_isSharedCheck_2864_ = (!leanh::lean_is_exclusive(v___x_2851_)) as u8;
                    if v_isSharedCheck_2864_ == 0 {
                        v_unused_2865_ = leanh::lean_ctor_get(v___x_2851_, 0);
                        leanh::lean_dec(v_unused_2865_);
                        v___x_2857_ = v___x_2851_;
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2855_);
                        leanh::lean_inc(v_postponed_2854_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2853_);
                        leanh::lean_inc(v_cache_2852_);
                        leanh::lean_dec(v___x_2851_);
                        v___x_2857_ = leanh::lean_box(0);
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2858_ == 0 {
                    leanh::lean_ctor_set(v___x_2857_, 0, v_snd_2850_);
                    v___x_2860_ = v___x_2857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2863_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_snd_2850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_cache_2852_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2863_,
                        2,
                        v_zetaDeltaFVarIds_2853_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_postponed_2854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_diag_2855_);
                    v___x_2860_ = v_reuseFailAlloc_2863_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2861_ = lean_st_ref_set(v___y_2842_, v___x_2860_);
                v___x_2862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2862_, 0, v_fst_2849_);
                return v___x_2862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(
    mut v_e_2866_: *mut leanh::LeanObject,
    mut v___y_2867_: *mut leanh::LeanObject,
    mut v___y_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_2866_, v___y_2867_);
    leanh::lean_dec(v___y_2867_);
    return v_res_2869_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(
    mut v_e_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2879_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_2870_, v___y_2875_);
    return v___x_2879_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(
    mut v_e_2880_: *mut leanh::LeanObject,
    mut v___y_2881_: *mut leanh::LeanObject,
    mut v___y_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    leanh::lean_dec(v___y_2887_);
    leanh::lean_dec_ref(v___y_2886_);
    leanh::lean_dec(v___y_2885_);
    leanh::lean_dec_ref(v___y_2884_);
    leanh::lean_dec(v___y_2883_);
    leanh::lean_dec_ref(v___y_2882_);
    leanh::lean_dec(v___y_2881_);
    return v_res_2889_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(
    mut v_as_2890_: *mut leanh::LeanObject,
    mut v_sz_2891_: usize,
    mut v_i_2892_: usize,
    mut v_b_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: usize = 0;
    let mut v___x_2914_: usize = 0;
    let mut v_reuseFailAlloc_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_a_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2953_: u8 = 0;
    let mut v_a_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_unused_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2902_ = lean_usize_dec_lt(v_i_2892_, v_sz_2891_);
                if v___x_2902_ == 0 {
                    v___x_2903_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2903_, 0, v_b_2893_);
                    return v___x_2903_;
                } else {
                    v_snd_2904_ = leanh::lean_ctor_get(v_b_2893_, 1);
                    v_isSharedCheck_2962_ = (!leanh::lean_is_exclusive(v_b_2893_)) as u8;
                    if v_isSharedCheck_2962_ == 0 {
                        v_unused_2963_ = leanh::lean_ctor_get(v_b_2893_, 0);
                        leanh::lean_dec(v_unused_2963_);
                        v___x_2906_ = v_b_2893_;
                        v_isShared_2907_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2904_);
                        leanh::lean_dec(v_b_2893_);
                        v___x_2906_ = leanh::lean_box(0);
                        v_isShared_2907_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2908_ = leanh::lean_box(0);
                v_a_2917_ = lean_array_uget_borrowed(v_as_2890_, v_i_2892_);
                if leanh::lean_obj_tag(v_a_2917_) == 0 {
                    v_a_2910_ = v_snd_2904_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2904_);
                    v_val_2918_ = leanh::lean_ctor_get(v_a_2917_, 0);
                    v___x_2919_ = leanh::lean_box(0);
                    v___x_2920_ = l_Lean_LocalDecl_isAuxDecl(v_val_2918_);
                    if v___x_2920_ == 0 {
                        v___x_2921_ = l_Lean_LocalDecl_value_x3f(v_val_2918_, v___x_2920_);
                        if leanh::lean_obj_tag(v___x_2921_) == 1 {
                            v_val_2922_ = leanh::lean_ctor_get(v___x_2921_, 0);
                            leanh::lean_inc(v_val_2922_);
                            leanh::lean_dec_ref_known(v___x_2921_, 1);
                            v___x_2923_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_2922_, v___y_2898_);
                            if leanh::lean_obj_tag(v___x_2923_) == 0 {
                                v_a_2924_ = leanh::lean_ctor_get(v___x_2923_, 0);
                                leanh::lean_inc(v_a_2924_);
                                leanh::lean_dec_ref_known(v___x_2923_, 1);
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
                                if leanh::lean_obj_tag(v___x_2925_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2925_, 1);
                                    v_a_2910_ = v___x_2919_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_2906_);
                                    v_a_2926_ = leanh::lean_ctor_get(v___x_2925_, 0);
                                    v_isSharedCheck_2933_ =
                                        (!leanh::lean_is_exclusive(v___x_2925_)) as u8;
                                    if v_isSharedCheck_2933_ == 0 {
                                        v___x_2928_ = v___x_2925_;
                                        v_isShared_2929_ = v_isSharedCheck_2933_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2926_);
                                        leanh::lean_dec(v___x_2925_);
                                        v___x_2928_ = leanh::lean_box(0);
                                        v_isShared_2929_ = v_isSharedCheck_2933_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_2906_);
                                v_a_2934_ = leanh::lean_ctor_get(v___x_2923_, 0);
                                v_isSharedCheck_2941_ =
                                    (!leanh::lean_is_exclusive(v___x_2923_)) as u8;
                                if v_isSharedCheck_2941_ == 0 {
                                    v___x_2936_ = v___x_2923_;
                                    v_isShared_2937_ = v_isSharedCheck_2941_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2934_);
                                    leanh::lean_dec(v___x_2923_);
                                    v___x_2936_ = leanh::lean_box(0);
                                    v_isShared_2937_ = v_isSharedCheck_2941_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2921_);
                            v___x_2942_ = l_Lean_LocalDecl_type(v_val_2918_);
                            v___x_2943_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_2942_, v___y_2898_);
                            if leanh::lean_obj_tag(v___x_2943_) == 0 {
                                v_a_2944_ = leanh::lean_ctor_get(v___x_2943_, 0);
                                leanh::lean_inc(v_a_2944_);
                                leanh::lean_dec_ref_known(v___x_2943_, 1);
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
                                if leanh::lean_obj_tag(v___x_2945_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2945_, 1);
                                    v_a_2910_ = v___x_2919_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_2906_);
                                    v_a_2946_ = leanh::lean_ctor_get(v___x_2945_, 0);
                                    v_isSharedCheck_2953_ =
                                        (!leanh::lean_is_exclusive(v___x_2945_)) as u8;
                                    if v_isSharedCheck_2953_ == 0 {
                                        v___x_2948_ = v___x_2945_;
                                        v_isShared_2949_ = v_isSharedCheck_2953_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2946_);
                                        leanh::lean_dec(v___x_2945_);
                                        v___x_2948_ = leanh::lean_box(0);
                                        v_isShared_2949_ = v_isSharedCheck_2953_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_2906_);
                                v_a_2954_ = leanh::lean_ctor_get(v___x_2943_, 0);
                                v_isSharedCheck_2961_ =
                                    (!leanh::lean_is_exclusive(v___x_2943_)) as u8;
                                if v_isSharedCheck_2961_ == 0 {
                                    v___x_2956_ = v___x_2943_;
                                    v_isShared_2957_ = v_isSharedCheck_2961_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2954_);
                                    leanh::lean_dec(v___x_2943_);
                                    v___x_2956_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2906_, 1, v_a_2910_);
                    leanh::lean_ctor_set(v___x_2906_, 0, v___x_2908_);
                    v___x_2912_ = v___x_2906_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_a_2910_);
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
                    v_reuseFailAlloc_2932_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
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
                    v_reuseFailAlloc_2940_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
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
                    v_reuseFailAlloc_2952_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
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
                    v_reuseFailAlloc_2960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
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
    mut v_as_2964_: *mut leanh::LeanObject,
    mut v_sz_2965_: *mut leanh::LeanObject,
    mut v_i_2966_: *mut leanh::LeanObject,
    mut v_b_2967_: *mut leanh::LeanObject,
    mut v___y_2968_: *mut leanh::LeanObject,
    mut v___y_2969_: *mut leanh::LeanObject,
    mut v___y_2970_: *mut leanh::LeanObject,
    mut v___y_2971_: *mut leanh::LeanObject,
    mut v___y_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
    mut v___y_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2976_: usize = 0;
    let mut v_i_boxed_2977_: usize = 0;
    let mut v_res_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2976_ = leanh::lean_unbox_usize(v_sz_2965_);
    leanh::lean_dec(v_sz_2965_);
    v_i_boxed_2977_ = leanh::lean_unbox_usize(v_i_2966_);
    leanh::lean_dec(v_i_2966_);
    v_res_2978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_2964_, v_sz_boxed_2976_, v_i_boxed_2977_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
    leanh::lean_dec(v___y_2974_);
    leanh::lean_dec_ref(v___y_2973_);
    leanh::lean_dec(v___y_2972_);
    leanh::lean_dec_ref(v___y_2971_);
    leanh::lean_dec(v___y_2970_);
    leanh::lean_dec_ref(v___y_2969_);
    leanh::lean_dec(v___y_2968_);
    leanh::lean_dec_ref(v_as_2964_);
    return v_res_2978_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(
    mut v_as_2979_: *mut leanh::LeanObject,
    mut v_sz_2980_: usize,
    mut v_i_2981_: usize,
    mut v_b_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
    mut v___y_2984_: *mut leanh::LeanObject,
    mut v___y_2985_: *mut leanh::LeanObject,
    mut v___y_2986_: *mut leanh::LeanObject,
    mut v___y_2987_: *mut leanh::LeanObject,
    mut v___y_2988_: *mut leanh::LeanObject,
    mut v___y_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: usize = 0;
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_a_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v_a_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_unused_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_usize_dec_lt(v_i_2981_, v_sz_2980_);
                if v___x_2991_ == 0 {
                    v___x_2992_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2992_, 0, v_b_2982_);
                    return v___x_2992_;
                } else {
                    v_snd_2993_ = leanh::lean_ctor_get(v_b_2982_, 1);
                    v_isSharedCheck_3051_ = (!leanh::lean_is_exclusive(v_b_2982_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v_unused_3052_ = leanh::lean_ctor_get(v_b_2982_, 0);
                        leanh::lean_dec(v_unused_3052_);
                        v___x_2995_ = v_b_2982_;
                        v_isShared_2996_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2993_);
                        leanh::lean_dec(v_b_2982_);
                        v___x_2995_ = leanh::lean_box(0);
                        v_isShared_2996_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2997_ = leanh::lean_box(0);
                v_a_3006_ = lean_array_uget_borrowed(v_as_2979_, v_i_2981_);
                if leanh::lean_obj_tag(v_a_3006_) == 0 {
                    v_a_2999_ = v_snd_2993_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2993_);
                    v_val_3007_ = leanh::lean_ctor_get(v_a_3006_, 0);
                    v___x_3008_ = leanh::lean_box(0);
                    v___x_3009_ = l_Lean_LocalDecl_isAuxDecl(v_val_3007_);
                    if v___x_3009_ == 0 {
                        v___x_3010_ = l_Lean_LocalDecl_value_x3f(v_val_3007_, v___x_3009_);
                        if leanh::lean_obj_tag(v___x_3010_) == 1 {
                            v_val_3011_ = leanh::lean_ctor_get(v___x_3010_, 0);
                            leanh::lean_inc(v_val_3011_);
                            leanh::lean_dec_ref_known(v___x_3010_, 1);
                            v___x_3012_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3011_, v___y_2987_);
                            if leanh::lean_obj_tag(v___x_3012_) == 0 {
                                v_a_3013_ = leanh::lean_ctor_get(v___x_3012_, 0);
                                leanh::lean_inc(v_a_3013_);
                                leanh::lean_dec_ref_known(v___x_3012_, 1);
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
                                if leanh::lean_obj_tag(v___x_3014_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3014_, 1);
                                    v_a_2999_ = v___x_3008_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_2995_);
                                    v_a_3015_ = leanh::lean_ctor_get(v___x_3014_, 0);
                                    v_isSharedCheck_3022_ =
                                        (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                                    if v_isSharedCheck_3022_ == 0 {
                                        v___x_3017_ = v___x_3014_;
                                        v_isShared_3018_ = v_isSharedCheck_3022_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3015_);
                                        leanh::lean_dec(v___x_3014_);
                                        v___x_3017_ = leanh::lean_box(0);
                                        v_isShared_3018_ = v_isSharedCheck_3022_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_2995_);
                                v_a_3023_ = leanh::lean_ctor_get(v___x_3012_, 0);
                                v_isSharedCheck_3030_ =
                                    (!leanh::lean_is_exclusive(v___x_3012_)) as u8;
                                if v_isSharedCheck_3030_ == 0 {
                                    v___x_3025_ = v___x_3012_;
                                    v_isShared_3026_ = v_isSharedCheck_3030_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3023_);
                                    leanh::lean_dec(v___x_3012_);
                                    v___x_3025_ = leanh::lean_box(0);
                                    v_isShared_3026_ = v_isSharedCheck_3030_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_3010_);
                            v___x_3031_ = l_Lean_LocalDecl_type(v_val_3007_);
                            v___x_3032_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3031_, v___y_2987_);
                            if leanh::lean_obj_tag(v___x_3032_) == 0 {
                                v_a_3033_ = leanh::lean_ctor_get(v___x_3032_, 0);
                                leanh::lean_inc(v_a_3033_);
                                leanh::lean_dec_ref_known(v___x_3032_, 1);
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
                                if leanh::lean_obj_tag(v___x_3034_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3034_, 1);
                                    v_a_2999_ = v___x_3008_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_2995_);
                                    v_a_3035_ = leanh::lean_ctor_get(v___x_3034_, 0);
                                    v_isSharedCheck_3042_ =
                                        (!leanh::lean_is_exclusive(v___x_3034_)) as u8;
                                    if v_isSharedCheck_3042_ == 0 {
                                        v___x_3037_ = v___x_3034_;
                                        v_isShared_3038_ = v_isSharedCheck_3042_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3035_);
                                        leanh::lean_dec(v___x_3034_);
                                        v___x_3037_ = leanh::lean_box(0);
                                        v_isShared_3038_ = v_isSharedCheck_3042_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_2995_);
                                v_a_3043_ = leanh::lean_ctor_get(v___x_3032_, 0);
                                v_isSharedCheck_3050_ =
                                    (!leanh::lean_is_exclusive(v___x_3032_)) as u8;
                                if v_isSharedCheck_3050_ == 0 {
                                    v___x_3045_ = v___x_3032_;
                                    v_isShared_3046_ = v_isSharedCheck_3050_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3043_);
                                    leanh::lean_dec(v___x_3032_);
                                    v___x_3045_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2995_, 1, v_a_2999_);
                    leanh::lean_ctor_set(v___x_2995_, 0, v___x_2997_);
                    v___x_3001_ = v___x_2995_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_a_2999_);
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
                    v_reuseFailAlloc_3021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
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
                    v_reuseFailAlloc_3029_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
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
                    v_reuseFailAlloc_3041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
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
                    v_reuseFailAlloc_3049_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
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
    mut v_as_3053_: *mut leanh::LeanObject,
    mut v_sz_3054_: *mut leanh::LeanObject,
    mut v_i_3055_: *mut leanh::LeanObject,
    mut v_b_3056_: *mut leanh::LeanObject,
    mut v___y_3057_: *mut leanh::LeanObject,
    mut v___y_3058_: *mut leanh::LeanObject,
    mut v___y_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
    mut v___y_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
    mut v___y_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3065_: usize = 0;
    let mut v_i_boxed_3066_: usize = 0;
    let mut v_res_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3065_ = leanh::lean_unbox_usize(v_sz_3054_);
    leanh::lean_dec(v_sz_3054_);
    v_i_boxed_3066_ = leanh::lean_unbox_usize(v_i_3055_);
    leanh::lean_dec(v_i_3055_);
    v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_3053_, v_sz_boxed_3065_, v_i_boxed_3066_, v_b_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
    leanh::lean_dec(v___y_3063_);
    leanh::lean_dec_ref(v___y_3062_);
    leanh::lean_dec(v___y_3061_);
    leanh::lean_dec_ref(v___y_3060_);
    leanh::lean_dec(v___y_3059_);
    leanh::lean_dec_ref(v___y_3058_);
    leanh::lean_dec(v___y_3057_);
    leanh::lean_dec_ref(v_as_3053_);
    return v_res_3067_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(
    mut v_as_3068_: *mut leanh::LeanObject,
    mut v_sz_3069_: usize,
    mut v_i_3070_: usize,
    mut v_b_3071_: *mut leanh::LeanObject,
    mut v___y_3072_: *mut leanh::LeanObject,
    mut v___y_3073_: *mut leanh::LeanObject,
    mut v___y_3074_: *mut leanh::LeanObject,
    mut v___y_3075_: *mut leanh::LeanObject,
    mut v___y_3076_: *mut leanh::LeanObject,
    mut v___y_3077_: *mut leanh::LeanObject,
    mut v___y_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: usize = 0;
    let mut v___x_3092_: usize = 0;
    let mut v_reuseFailAlloc_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_a_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3131_: u8 = 0;
    let mut v_a_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut v_isSharedCheck_3140_: u8 = 0;
    let mut v_unused_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3080_ = lean_usize_dec_lt(v_i_3070_, v_sz_3069_);
                if v___x_3080_ == 0 {
                    v___x_3081_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3081_, 0, v_b_3071_);
                    return v___x_3081_;
                } else {
                    v_snd_3082_ = leanh::lean_ctor_get(v_b_3071_, 1);
                    v_isSharedCheck_3140_ = (!leanh::lean_is_exclusive(v_b_3071_)) as u8;
                    if v_isSharedCheck_3140_ == 0 {
                        v_unused_3141_ = leanh::lean_ctor_get(v_b_3071_, 0);
                        leanh::lean_dec(v_unused_3141_);
                        v___x_3084_ = v_b_3071_;
                        v_isShared_3085_ = v_isSharedCheck_3140_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3082_);
                        leanh::lean_dec(v_b_3071_);
                        v___x_3084_ = leanh::lean_box(0);
                        v_isShared_3085_ = v_isSharedCheck_3140_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3086_ = leanh::lean_box(0);
                v_a_3095_ = lean_array_uget_borrowed(v_as_3068_, v_i_3070_);
                if leanh::lean_obj_tag(v_a_3095_) == 0 {
                    v_a_3088_ = v_snd_3082_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_3082_);
                    v_val_3096_ = leanh::lean_ctor_get(v_a_3095_, 0);
                    v___x_3097_ = leanh::lean_box(0);
                    v___x_3098_ = l_Lean_LocalDecl_isAuxDecl(v_val_3096_);
                    if v___x_3098_ == 0 {
                        v___x_3099_ = l_Lean_LocalDecl_value_x3f(v_val_3096_, v___x_3098_);
                        if leanh::lean_obj_tag(v___x_3099_) == 1 {
                            v_val_3100_ = leanh::lean_ctor_get(v___x_3099_, 0);
                            leanh::lean_inc(v_val_3100_);
                            leanh::lean_dec_ref_known(v___x_3099_, 1);
                            v___x_3101_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3100_, v___y_3076_);
                            if leanh::lean_obj_tag(v___x_3101_) == 0 {
                                v_a_3102_ = leanh::lean_ctor_get(v___x_3101_, 0);
                                leanh::lean_inc(v_a_3102_);
                                leanh::lean_dec_ref_known(v___x_3101_, 1);
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
                                if leanh::lean_obj_tag(v___x_3103_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3103_, 1);
                                    v_a_3088_ = v___x_3097_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_3084_);
                                    v_a_3104_ = leanh::lean_ctor_get(v___x_3103_, 0);
                                    v_isSharedCheck_3111_ =
                                        (!leanh::lean_is_exclusive(v___x_3103_)) as u8;
                                    if v_isSharedCheck_3111_ == 0 {
                                        v___x_3106_ = v___x_3103_;
                                        v_isShared_3107_ = v_isSharedCheck_3111_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3104_);
                                        leanh::lean_dec(v___x_3103_);
                                        v___x_3106_ = leanh::lean_box(0);
                                        v_isShared_3107_ = v_isSharedCheck_3111_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_3084_);
                                v_a_3112_ = leanh::lean_ctor_get(v___x_3101_, 0);
                                v_isSharedCheck_3119_ =
                                    (!leanh::lean_is_exclusive(v___x_3101_)) as u8;
                                if v_isSharedCheck_3119_ == 0 {
                                    v___x_3114_ = v___x_3101_;
                                    v_isShared_3115_ = v_isSharedCheck_3119_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3112_);
                                    leanh::lean_dec(v___x_3101_);
                                    v___x_3114_ = leanh::lean_box(0);
                                    v_isShared_3115_ = v_isSharedCheck_3119_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_3099_);
                            v___x_3120_ = l_Lean_LocalDecl_type(v_val_3096_);
                            v___x_3121_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3120_, v___y_3076_);
                            if leanh::lean_obj_tag(v___x_3121_) == 0 {
                                v_a_3122_ = leanh::lean_ctor_get(v___x_3121_, 0);
                                leanh::lean_inc(v_a_3122_);
                                leanh::lean_dec_ref_known(v___x_3121_, 1);
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
                                if leanh::lean_obj_tag(v___x_3123_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3123_, 1);
                                    v_a_3088_ = v___x_3097_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_3084_);
                                    v_a_3124_ = leanh::lean_ctor_get(v___x_3123_, 0);
                                    v_isSharedCheck_3131_ =
                                        (!leanh::lean_is_exclusive(v___x_3123_)) as u8;
                                    if v_isSharedCheck_3131_ == 0 {
                                        v___x_3126_ = v___x_3123_;
                                        v_isShared_3127_ = v_isSharedCheck_3131_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3124_);
                                        leanh::lean_dec(v___x_3123_);
                                        v___x_3126_ = leanh::lean_box(0);
                                        v_isShared_3127_ = v_isSharedCheck_3131_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_3084_);
                                v_a_3132_ = leanh::lean_ctor_get(v___x_3121_, 0);
                                v_isSharedCheck_3139_ =
                                    (!leanh::lean_is_exclusive(v___x_3121_)) as u8;
                                if v_isSharedCheck_3139_ == 0 {
                                    v___x_3134_ = v___x_3121_;
                                    v_isShared_3135_ = v_isSharedCheck_3139_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3132_);
                                    leanh::lean_dec(v___x_3121_);
                                    v___x_3134_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3084_, 1, v_a_3088_);
                    leanh::lean_ctor_set(v___x_3084_, 0, v___x_3086_);
                    v___x_3090_ = v___x_3084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3094_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_3088_);
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
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
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
                    v_reuseFailAlloc_3118_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
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
                    v_reuseFailAlloc_3130_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
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
                    v_reuseFailAlloc_3138_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
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
    mut v_as_3142_: *mut leanh::LeanObject,
    mut v_sz_3143_: *mut leanh::LeanObject,
    mut v_i_3144_: *mut leanh::LeanObject,
    mut v_b_3145_: *mut leanh::LeanObject,
    mut v___y_3146_: *mut leanh::LeanObject,
    mut v___y_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3154_: usize = 0;
    let mut v_i_boxed_3155_: usize = 0;
    let mut v_res_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3154_ = leanh::lean_unbox_usize(v_sz_3143_);
    leanh::lean_dec(v_sz_3143_);
    v_i_boxed_3155_ = leanh::lean_unbox_usize(v_i_3144_);
    leanh::lean_dec(v_i_3144_);
    v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_3142_, v_sz_boxed_3154_, v_i_boxed_3155_, v_b_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
    leanh::lean_dec(v___y_3152_);
    leanh::lean_dec_ref(v___y_3151_);
    leanh::lean_dec(v___y_3150_);
    leanh::lean_dec_ref(v___y_3149_);
    leanh::lean_dec(v___y_3148_);
    leanh::lean_dec_ref(v___y_3147_);
    leanh::lean_dec(v___y_3146_);
    leanh::lean_dec_ref(v_as_3142_);
    return v_res_3156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(
    mut v_as_3157_: *mut leanh::LeanObject,
    mut v_sz_3158_: usize,
    mut v_i_3159_: usize,
    mut v_b_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
    mut v___y_3163_: *mut leanh::LeanObject,
    mut v___y_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: usize = 0;
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v_a_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3224_: u8 = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v_unused_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3169_ = lean_usize_dec_lt(v_i_3159_, v_sz_3158_);
                if v___x_3169_ == 0 {
                    v___x_3170_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3170_, 0, v_b_3160_);
                    return v___x_3170_;
                } else {
                    v_snd_3171_ = leanh::lean_ctor_get(v_b_3160_, 1);
                    v_isSharedCheck_3229_ = (!leanh::lean_is_exclusive(v_b_3160_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v_unused_3230_ = leanh::lean_ctor_get(v_b_3160_, 0);
                        leanh::lean_dec(v_unused_3230_);
                        v___x_3173_ = v_b_3160_;
                        v_isShared_3174_ = v_isSharedCheck_3229_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3171_);
                        leanh::lean_dec(v_b_3160_);
                        v___x_3173_ = leanh::lean_box(0);
                        v_isShared_3174_ = v_isSharedCheck_3229_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3175_ = leanh::lean_box(0);
                v_a_3184_ = lean_array_uget_borrowed(v_as_3157_, v_i_3159_);
                if leanh::lean_obj_tag(v_a_3184_) == 0 {
                    v_a_3177_ = v_snd_3171_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_3171_);
                    v_val_3185_ = leanh::lean_ctor_get(v_a_3184_, 0);
                    v___x_3186_ = leanh::lean_box(0);
                    v___x_3187_ = l_Lean_LocalDecl_isAuxDecl(v_val_3185_);
                    if v___x_3187_ == 0 {
                        v___x_3188_ = l_Lean_LocalDecl_value_x3f(v_val_3185_, v___x_3187_);
                        if leanh::lean_obj_tag(v___x_3188_) == 1 {
                            v_val_3189_ = leanh::lean_ctor_get(v___x_3188_, 0);
                            leanh::lean_inc(v_val_3189_);
                            leanh::lean_dec_ref_known(v___x_3188_, 1);
                            v___x_3190_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3189_, v___y_3165_);
                            if leanh::lean_obj_tag(v___x_3190_) == 0 {
                                v_a_3191_ = leanh::lean_ctor_get(v___x_3190_, 0);
                                leanh::lean_inc(v_a_3191_);
                                leanh::lean_dec_ref_known(v___x_3190_, 1);
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
                                if leanh::lean_obj_tag(v___x_3192_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3192_, 1);
                                    v_a_3177_ = v___x_3186_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_3173_);
                                    v_a_3193_ = leanh::lean_ctor_get(v___x_3192_, 0);
                                    v_isSharedCheck_3200_ =
                                        (!leanh::lean_is_exclusive(v___x_3192_)) as u8;
                                    if v_isSharedCheck_3200_ == 0 {
                                        v___x_3195_ = v___x_3192_;
                                        v_isShared_3196_ = v_isSharedCheck_3200_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3193_);
                                        leanh::lean_dec(v___x_3192_);
                                        v___x_3195_ = leanh::lean_box(0);
                                        v_isShared_3196_ = v_isSharedCheck_3200_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_3173_);
                                v_a_3201_ = leanh::lean_ctor_get(v___x_3190_, 0);
                                v_isSharedCheck_3208_ =
                                    (!leanh::lean_is_exclusive(v___x_3190_)) as u8;
                                if v_isSharedCheck_3208_ == 0 {
                                    v___x_3203_ = v___x_3190_;
                                    v_isShared_3204_ = v_isSharedCheck_3208_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3201_);
                                    leanh::lean_dec(v___x_3190_);
                                    v___x_3203_ = leanh::lean_box(0);
                                    v_isShared_3204_ = v_isSharedCheck_3208_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_3188_);
                            v___x_3209_ = l_Lean_LocalDecl_type(v_val_3185_);
                            v___x_3210_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3209_, v___y_3165_);
                            if leanh::lean_obj_tag(v___x_3210_) == 0 {
                                v_a_3211_ = leanh::lean_ctor_get(v___x_3210_, 0);
                                leanh::lean_inc(v_a_3211_);
                                leanh::lean_dec_ref_known(v___x_3210_, 1);
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
                                if leanh::lean_obj_tag(v___x_3212_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3212_, 1);
                                    v_a_3177_ = v___x_3186_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_3173_);
                                    v_a_3213_ = leanh::lean_ctor_get(v___x_3212_, 0);
                                    v_isSharedCheck_3220_ =
                                        (!leanh::lean_is_exclusive(v___x_3212_)) as u8;
                                    if v_isSharedCheck_3220_ == 0 {
                                        v___x_3215_ = v___x_3212_;
                                        v_isShared_3216_ = v_isSharedCheck_3220_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3213_);
                                        leanh::lean_dec(v___x_3212_);
                                        v___x_3215_ = leanh::lean_box(0);
                                        v_isShared_3216_ = v_isSharedCheck_3220_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_3173_);
                                v_a_3221_ = leanh::lean_ctor_get(v___x_3210_, 0);
                                v_isSharedCheck_3228_ =
                                    (!leanh::lean_is_exclusive(v___x_3210_)) as u8;
                                if v_isSharedCheck_3228_ == 0 {
                                    v___x_3223_ = v___x_3210_;
                                    v_isShared_3224_ = v_isSharedCheck_3228_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3221_);
                                    leanh::lean_dec(v___x_3210_);
                                    v___x_3223_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3173_, 1, v_a_3177_);
                    leanh::lean_ctor_set(v___x_3173_, 0, v___x_3175_);
                    v___x_3179_ = v___x_3173_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_a_3177_);
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
                    v_reuseFailAlloc_3199_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
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
                    v_reuseFailAlloc_3207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
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
                    v_reuseFailAlloc_3219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
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
                    v_reuseFailAlloc_3227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
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
    mut v_as_3231_: *mut leanh::LeanObject,
    mut v_sz_3232_: *mut leanh::LeanObject,
    mut v_i_3233_: *mut leanh::LeanObject,
    mut v_b_3234_: *mut leanh::LeanObject,
    mut v___y_3235_: *mut leanh::LeanObject,
    mut v___y_3236_: *mut leanh::LeanObject,
    mut v___y_3237_: *mut leanh::LeanObject,
    mut v___y_3238_: *mut leanh::LeanObject,
    mut v___y_3239_: *mut leanh::LeanObject,
    mut v___y_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
    mut v___y_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3243_: usize = 0;
    let mut v_i_boxed_3244_: usize = 0;
    let mut v_res_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3243_ = leanh::lean_unbox_usize(v_sz_3232_);
    leanh::lean_dec(v_sz_3232_);
    v_i_boxed_3244_ = leanh::lean_unbox_usize(v_i_3233_);
    leanh::lean_dec(v_i_3233_);
    v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_3231_, v_sz_boxed_3243_, v_i_boxed_3244_, v_b_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
    leanh::lean_dec(v___y_3241_);
    leanh::lean_dec_ref(v___y_3240_);
    leanh::lean_dec(v___y_3239_);
    leanh::lean_dec_ref(v___y_3238_);
    leanh::lean_dec(v___y_3237_);
    leanh::lean_dec_ref(v___y_3236_);
    leanh::lean_dec(v___y_3235_);
    leanh::lean_dec_ref(v_as_3231_);
    return v_res_3245_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(
    mut v_init_3246_: *mut leanh::LeanObject,
    mut v_n_3247_: *mut leanh::LeanObject,
    mut v_b_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
    mut v___y_3250_: *mut leanh::LeanObject,
    mut v___y_3251_: *mut leanh::LeanObject,
    mut v___y_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3260_: usize = 0;
    let mut v___x_3261_: usize = 0;
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3266_: u8 = 0;
    let mut v_fst_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v_a_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_vs_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3289_: usize = 0;
    let mut v___x_3290_: usize = 0;
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v_fst_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3306_: u8 = 0;
    let mut v_a_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_3247_) == 0 {
                    v_cs_3257_ = leanh::lean_ctor_get(v_n_3247_, 0);
                    v___x_3258_ = leanh::lean_box(0);
                    v___x_3259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3259_, 0, v___x_3258_);
                    leanh::lean_ctor_set(v___x_3259_, 1, v_b_3248_);
                    v_sz_3260_ = lean_array_size(v_cs_3257_);
                    v___x_3261_ = 0usize;
                    v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_3246_, v_cs_3257_, v_sz_3260_, v___x_3261_, v___x_3259_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
                    if leanh::lean_obj_tag(v___x_3262_) == 0 {
                        v_a_3263_ = leanh::lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3277_ =
                            (!leanh::lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3277_ == 0 {
                            v___x_3265_ = v___x_3262_;
                            v_isShared_3266_ = v_isSharedCheck_3277_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3263_);
                            leanh::lean_dec(v___x_3262_);
                            v___x_3265_ = leanh::lean_box(0);
                            v_isShared_3266_ = v_isSharedCheck_3277_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3278_ = leanh::lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3285_ =
                            (!leanh::lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3280_ = v___x_3262_;
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3278_);
                            leanh::lean_dec(v___x_3262_);
                            v___x_3280_ = leanh::lean_box(0);
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3286_ = leanh::lean_ctor_get(v_n_3247_, 0);
                    v___x_3287_ = leanh::lean_box(0);
                    v___x_3288_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3288_, 0, v___x_3287_);
                    leanh::lean_ctor_set(v___x_3288_, 1, v_b_3248_);
                    v_sz_3289_ = lean_array_size(v_vs_3286_);
                    v___x_3290_ = 0usize;
                    v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_3286_, v_sz_3289_, v___x_3290_, v___x_3288_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
                    if leanh::lean_obj_tag(v___x_3291_) == 0 {
                        v_a_3292_ = leanh::lean_ctor_get(v___x_3291_, 0);
                        v_isSharedCheck_3306_ =
                            (!leanh::lean_is_exclusive(v___x_3291_)) as u8;
                        if v_isSharedCheck_3306_ == 0 {
                            v___x_3294_ = v___x_3291_;
                            v_isShared_3295_ = v_isSharedCheck_3306_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3292_);
                            leanh::lean_dec(v___x_3291_);
                            v___x_3294_ = leanh::lean_box(0);
                            v_isShared_3295_ = v_isSharedCheck_3306_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3307_ = leanh::lean_ctor_get(v___x_3291_, 0);
                        v_isSharedCheck_3314_ =
                            (!leanh::lean_is_exclusive(v___x_3291_)) as u8;
                        if v_isSharedCheck_3314_ == 0 {
                            v___x_3309_ = v___x_3291_;
                            v_isShared_3310_ = v_isSharedCheck_3314_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3307_);
                            leanh::lean_dec(v___x_3291_);
                            v___x_3309_ = leanh::lean_box(0);
                            v_isShared_3310_ = v_isSharedCheck_3314_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3267_ = leanh::lean_ctor_get(v_a_3263_, 0);
                if leanh::lean_obj_tag(v_fst_3267_) == 0 {
                    v_snd_3268_ = leanh::lean_ctor_get(v_a_3263_, 1);
                    leanh::lean_inc(v_snd_3268_);
                    leanh::lean_dec(v_a_3263_);
                    v___x_3269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3269_, 0, v_snd_3268_);
                    if v_isShared_3266_ == 0 {
                        leanh::lean_ctor_set(v___x_3265_, 0, v___x_3269_);
                        v___x_3271_ = v___x_3265_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
                        v___x_3271_ = v_reuseFailAlloc_3272_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3267_);
                    leanh::lean_dec(v_a_3263_);
                    v_val_3273_ = leanh::lean_ctor_get(v_fst_3267_, 0);
                    leanh::lean_inc(v_val_3273_);
                    leanh::lean_dec_ref_known(v_fst_3267_, 1);
                    if v_isShared_3266_ == 0 {
                        leanh::lean_ctor_set(v___x_3265_, 0, v_val_3273_);
                        v___x_3275_ = v___x_3265_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3276_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_val_3273_);
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
                    v_reuseFailAlloc_3284_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3283_;
            }
            6 => {
                v_fst_3296_ = leanh::lean_ctor_get(v_a_3292_, 0);
                if leanh::lean_obj_tag(v_fst_3296_) == 0 {
                    v_snd_3297_ = leanh::lean_ctor_get(v_a_3292_, 1);
                    leanh::lean_inc(v_snd_3297_);
                    leanh::lean_dec(v_a_3292_);
                    v___x_3298_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3298_, 0, v_snd_3297_);
                    if v_isShared_3295_ == 0 {
                        leanh::lean_ctor_set(v___x_3294_, 0, v___x_3298_);
                        v___x_3300_ = v___x_3294_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                        v___x_3300_ = v_reuseFailAlloc_3301_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3296_);
                    leanh::lean_dec(v_a_3292_);
                    v_val_3302_ = leanh::lean_ctor_get(v_fst_3296_, 0);
                    leanh::lean_inc(v_val_3302_);
                    leanh::lean_dec_ref_known(v_fst_3296_, 1);
                    if v_isShared_3295_ == 0 {
                        leanh::lean_ctor_set(v___x_3294_, 0, v_val_3302_);
                        v___x_3304_ = v___x_3294_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3305_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_val_3302_);
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
                    v_reuseFailAlloc_3313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
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
    mut v_init_3315_: *mut leanh::LeanObject,
    mut v_as_3316_: *mut leanh::LeanObject,
    mut v_sz_3317_: usize,
    mut v_i_3318_: usize,
    mut v_b_3319_: *mut leanh::LeanObject,
    mut v___y_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
    mut v___y_3323_: *mut leanh::LeanObject,
    mut v___y_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
    mut v___y_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v_a_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: usize = 0;
    let mut v_reuseFailAlloc_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_a_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_unused_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_usize_dec_lt(v_i_3318_, v_sz_3317_);
                if v___x_3328_ == 0 {
                    v___x_3329_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3329_, 0, v_b_3319_);
                    return v___x_3329_;
                } else {
                    v_snd_3330_ = leanh::lean_ctor_get(v_b_3319_, 1);
                    v_isSharedCheck_3364_ = (!leanh::lean_is_exclusive(v_b_3319_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v_unused_3365_ = leanh::lean_ctor_get(v_b_3319_, 0);
                        leanh::lean_dec(v_unused_3365_);
                        v___x_3332_ = v_b_3319_;
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3330_);
                        leanh::lean_dec(v_b_3319_);
                        v___x_3332_ = leanh::lean_box(0);
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3334_ = lean_array_uget_borrowed(v_as_3316_, v_i_3318_);
                leanh::lean_inc(v_snd_3330_);
                v___x_3335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3315_, v_a_3334_, v_snd_3330_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
                if leanh::lean_obj_tag(v___x_3335_) == 0 {
                    v_a_3336_ = leanh::lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3355_ = (!leanh::lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3355_ == 0 {
                        v___x_3338_ = v___x_3335_;
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3336_);
                        leanh::lean_dec(v___x_3335_);
                        v___x_3338_ = leanh::lean_box(0);
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3332_);
                    leanh::lean_dec(v_snd_3330_);
                    v_a_3356_ = leanh::lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3363_ = (!leanh::lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3363_ == 0 {
                        v___x_3358_ = v___x_3335_;
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3356_);
                        leanh::lean_dec(v___x_3335_);
                        v___x_3358_ = leanh::lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3336_) == 0 {
                    v___x_3340_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3340_, 0, v_a_3336_);
                    if v_isShared_3333_ == 0 {
                        leanh::lean_ctor_set(v___x_3332_, 0, v___x_3340_);
                        v___x_3342_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3346_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3340_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_snd_3330_);
                        v___x_3342_ = v_reuseFailAlloc_3346_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3338_);
                    leanh::lean_dec(v_snd_3330_);
                    v_a_3347_ = leanh::lean_ctor_get(v_a_3336_, 0);
                    leanh::lean_inc(v_a_3347_);
                    leanh::lean_dec_ref_known(v_a_3336_, 1);
                    v___x_3348_ = leanh::lean_box(0);
                    if v_isShared_3333_ == 0 {
                        leanh::lean_ctor_set(v___x_3332_, 1, v_a_3347_);
                        leanh::lean_ctor_set(v___x_3332_, 0, v___x_3348_);
                        v___x_3350_ = v___x_3332_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3354_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3348_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3347_);
                        v___x_3350_ = v_reuseFailAlloc_3354_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3339_ == 0 {
                    leanh::lean_ctor_set(v___x_3338_, 0, v___x_3342_);
                    v___x_3344_ = v___x_3338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
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
                    v_reuseFailAlloc_3362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
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
    mut v_init_3366_: *mut leanh::LeanObject,
    mut v_as_3367_: *mut leanh::LeanObject,
    mut v_sz_3368_: *mut leanh::LeanObject,
    mut v_i_3369_: *mut leanh::LeanObject,
    mut v_b_3370_: *mut leanh::LeanObject,
    mut v___y_3371_: *mut leanh::LeanObject,
    mut v___y_3372_: *mut leanh::LeanObject,
    mut v___y_3373_: *mut leanh::LeanObject,
    mut v___y_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3379_: usize = 0;
    let mut v_i_boxed_3380_: usize = 0;
    let mut v_res_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3379_ = leanh::lean_unbox_usize(v_sz_3368_);
    leanh::lean_dec(v_sz_3368_);
    v_i_boxed_3380_ = leanh::lean_unbox_usize(v_i_3369_);
    leanh::lean_dec(v_i_3369_);
    v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_3366_, v_as_3367_, v_sz_boxed_3379_, v_i_boxed_3380_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
    leanh::lean_dec(v___y_3377_);
    leanh::lean_dec_ref(v___y_3376_);
    leanh::lean_dec(v___y_3375_);
    leanh::lean_dec_ref(v___y_3374_);
    leanh::lean_dec(v___y_3373_);
    leanh::lean_dec_ref(v___y_3372_);
    leanh::lean_dec(v___y_3371_);
    leanh::lean_dec_ref(v_as_3367_);
    return v_res_3381_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(
    mut v_init_3382_: *mut leanh::LeanObject,
    mut v_n_3383_: *mut leanh::LeanObject,
    mut v_b_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
    mut v___y_3387_: *mut leanh::LeanObject,
    mut v___y_3388_: *mut leanh::LeanObject,
    mut v___y_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3382_, v_n_3383_, v_b_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    leanh::lean_dec(v___y_3391_);
    leanh::lean_dec_ref(v___y_3390_);
    leanh::lean_dec(v___y_3389_);
    leanh::lean_dec_ref(v___y_3388_);
    leanh::lean_dec(v___y_3387_);
    leanh::lean_dec_ref(v___y_3386_);
    leanh::lean_dec(v___y_3385_);
    leanh::lean_dec_ref(v_n_3383_);
    return v_res_3393_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(
    mut v_t_3394_: *mut leanh::LeanObject,
    mut v_init_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v_a_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3418_: usize = 0;
    let mut v___x_3419_: usize = 0;
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v_fst_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3434_: u8 = 0;
    let mut v_a_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v_a_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3404_ = leanh::lean_ctor_get(v_t_3394_, 0);
                v_tail_3405_ = leanh::lean_ctor_get(v_t_3394_, 1);
                v___x_3406_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3395_, v_root_3404_, v_init_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
                if leanh::lean_obj_tag(v___x_3406_) == 0 {
                    v_a_3407_ = leanh::lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3443_ = (!leanh::lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v___x_3409_ = v___x_3406_;
                        v_isShared_3410_ = v_isSharedCheck_3443_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3407_);
                        leanh::lean_dec(v___x_3406_);
                        v___x_3409_ = leanh::lean_box(0);
                        v_isShared_3410_ = v_isSharedCheck_3443_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3444_ = leanh::lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3451_ = (!leanh::lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v___x_3446_ = v___x_3406_;
                        v_isShared_3447_ = v_isSharedCheck_3451_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3444_);
                        leanh::lean_dec(v___x_3406_);
                        v___x_3446_ = leanh::lean_box(0);
                        v_isShared_3447_ = v_isSharedCheck_3451_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3407_) == 0 {
                    v_a_3411_ = leanh::lean_ctor_get(v_a_3407_, 0);
                    leanh::lean_inc(v_a_3411_);
                    leanh::lean_dec_ref_known(v_a_3407_, 1);
                    if v_isShared_3410_ == 0 {
                        leanh::lean_ctor_set(v___x_3409_, 0, v_a_3411_);
                        v___x_3413_ = v___x_3409_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3411_);
                        v___x_3413_ = v_reuseFailAlloc_3414_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3409_);
                    v_a_3415_ = leanh::lean_ctor_get(v_a_3407_, 0);
                    leanh::lean_inc(v_a_3415_);
                    leanh::lean_dec_ref_known(v_a_3407_, 1);
                    v___x_3416_ = leanh::lean_box(0);
                    v___x_3417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3417_, 0, v___x_3416_);
                    leanh::lean_ctor_set(v___x_3417_, 1, v_a_3415_);
                    v_sz_3418_ = lean_array_size(v_tail_3405_);
                    v___x_3419_ = 0usize;
                    v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_3405_, v_sz_3418_, v___x_3419_, v___x_3417_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
                    if leanh::lean_obj_tag(v___x_3420_) == 0 {
                        v_a_3421_ = leanh::lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3434_ =
                            (!leanh::lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3434_ == 0 {
                            v___x_3423_ = v___x_3420_;
                            v_isShared_3424_ = v_isSharedCheck_3434_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3421_);
                            leanh::lean_dec(v___x_3420_);
                            v___x_3423_ = leanh::lean_box(0);
                            v_isShared_3424_ = v_isSharedCheck_3434_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3435_ = leanh::lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3442_ =
                            (!leanh::lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3442_ == 0 {
                            v___x_3437_ = v___x_3420_;
                            v_isShared_3438_ = v_isSharedCheck_3442_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3435_);
                            leanh::lean_dec(v___x_3420_);
                            v___x_3437_ = leanh::lean_box(0);
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
                v_fst_3425_ = leanh::lean_ctor_get(v_a_3421_, 0);
                if leanh::lean_obj_tag(v_fst_3425_) == 0 {
                    v_snd_3426_ = leanh::lean_ctor_get(v_a_3421_, 1);
                    leanh::lean_inc(v_snd_3426_);
                    leanh::lean_dec(v_a_3421_);
                    if v_isShared_3424_ == 0 {
                        leanh::lean_ctor_set(v___x_3423_, 0, v_snd_3426_);
                        v___x_3428_ = v___x_3423_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_snd_3426_);
                        v___x_3428_ = v_reuseFailAlloc_3429_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3425_);
                    leanh::lean_dec(v_a_3421_);
                    v_val_3430_ = leanh::lean_ctor_get(v_fst_3425_, 0);
                    leanh::lean_inc(v_val_3430_);
                    leanh::lean_dec_ref_known(v_fst_3425_, 1);
                    if v_isShared_3424_ == 0 {
                        leanh::lean_ctor_set(v___x_3423_, 0, v_val_3430_);
                        v___x_3432_ = v___x_3423_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_val_3430_);
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
                    v_reuseFailAlloc_3441_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
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
                    v_reuseFailAlloc_3450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
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
    mut v_t_3452_: *mut leanh::LeanObject,
    mut v_init_3453_: *mut leanh::LeanObject,
    mut v___y_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
    mut v___y_3460_: *mut leanh::LeanObject,
    mut v___y_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_3452_, v_init_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
    leanh::lean_dec(v___y_3460_);
    leanh::lean_dec_ref(v___y_3459_);
    leanh::lean_dec(v___y_3458_);
    leanh::lean_dec_ref(v___y_3457_);
    leanh::lean_dec(v___y_3456_);
    leanh::lean_dec_ref(v___y_3455_);
    leanh::lean_dec(v___y_3454_);
    leanh::lean_dec_ref(v_t_3452_);
    return v_res_3462_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(
    mut v_mvarId_3463_: *mut leanh::LeanObject,
    mut v_a_3464_: *mut leanh::LeanObject,
    mut v_a_3465_: *mut leanh::LeanObject,
    mut v_a_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
    mut v_a_3468_: *mut leanh::LeanObject,
    mut v_a_3469_: *mut leanh::LeanObject,
    mut v_a_3470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_a_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3472_ = leanh::lean_ctor_get(v_a_3467_, 2);
                v_decls_3473_ = leanh::lean_ctor_get(v_lctx_3472_, 1);
                v___x_3474_ = leanh::lean_box(0);
                v___x_3475_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_3473_, v___x_3474_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
                if leanh::lean_obj_tag(v___x_3475_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3475_, 1);
                    v___x_3476_ = l_Lean_MVarId_getType(
                        v_mvarId_3463_,
                        v_a_3467_,
                        v_a_3468_,
                        v_a_3469_,
                        v_a_3470_,
                    );
                    if leanh::lean_obj_tag(v___x_3476_) == 0 {
                        v_a_3477_ = leanh::lean_ctor_get(v___x_3476_, 0);
                        leanh::lean_inc(v_a_3477_);
                        leanh::lean_dec_ref_known(v___x_3476_, 1);
                        v___x_3478_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_3477_, v_a_3468_);
                        if leanh::lean_obj_tag(v___x_3478_) == 0 {
                            v_a_3479_ = leanh::lean_ctor_get(v___x_3478_, 0);
                            leanh::lean_inc(v_a_3479_);
                            leanh::lean_dec_ref_known(v___x_3478_, 1);
                            v___x_3480_ = l_Lean_Meta_FunInd_Collector_visit(
                                v_a_3479_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_,
                                v_a_3469_, v_a_3470_,
                            );
                            return v___x_3480_;
                        } else {
                            v_a_3481_ = leanh::lean_ctor_get(v___x_3478_, 0);
                            v_isSharedCheck_3488_ =
                                (!leanh::lean_is_exclusive(v___x_3478_)) as u8;
                            if v_isSharedCheck_3488_ == 0 {
                                v___x_3483_ = v___x_3478_;
                                v_isShared_3484_ = v_isSharedCheck_3488_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3481_);
                                leanh::lean_dec(v___x_3478_);
                                v___x_3483_ = leanh::lean_box(0);
                                v_isShared_3484_ = v_isSharedCheck_3488_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3489_ = leanh::lean_ctor_get(v___x_3476_, 0);
                        v_isSharedCheck_3496_ =
                            (!leanh::lean_is_exclusive(v___x_3476_)) as u8;
                        if v_isSharedCheck_3496_ == 0 {
                            v___x_3491_ = v___x_3476_;
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3489_);
                            leanh::lean_dec(v___x_3476_);
                            v___x_3491_ = leanh::lean_box(0);
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_3463_);
                    return v___x_3475_;
                }
            }
            1 => {
                if v_isShared_3484_ == 0 {
                    v___x_3486_ = v___x_3483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
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
                    v_reuseFailAlloc_3495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
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
    mut v_mvarId_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
    mut v_a_3499_: *mut leanh::LeanObject,
    mut v_a_3500_: *mut leanh::LeanObject,
    mut v_a_3501_: *mut leanh::LeanObject,
    mut v_a_3502_: *mut leanh::LeanObject,
    mut v_a_3503_: *mut leanh::LeanObject,
    mut v_a_3504_: *mut leanh::LeanObject,
    mut v_a_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3504_);
    leanh::lean_dec_ref(v_a_3503_);
    leanh::lean_dec(v_a_3502_);
    leanh::lean_dec_ref(v_a_3501_);
    leanh::lean_dec(v_a_3500_);
    leanh::lean_dec_ref(v_a_3499_);
    leanh::lean_dec(v_a_3498_);
    return v_res_3506_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
    mut v_mvarId_3507_: *mut leanh::LeanObject,
    mut v_x_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_a_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_3507_,
                    v_x_3508_,
                    v___y_3509_,
                    v___y_3510_,
                    v___y_3511_,
                    v___y_3512_,
                );
                if leanh::lean_obj_tag(v___x_3514_) == 0 {
                    v_a_3515_ = leanh::lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3522_ = (!leanh::lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3522_ == 0 {
                        v___x_3517_ = v___x_3514_;
                        v_isShared_3518_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3515_);
                        leanh::lean_dec(v___x_3514_);
                        v___x_3517_ = leanh::lean_box(0);
                        v_isShared_3518_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3523_ = leanh::lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3530_ = (!leanh::lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3530_ == 0 {
                        v___x_3525_ = v___x_3514_;
                        v_isShared_3526_ = v_isSharedCheck_3530_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3523_);
                        leanh::lean_dec(v___x_3514_);
                        v___x_3525_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3521_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
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
                    v_reuseFailAlloc_3529_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
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
    mut v_mvarId_3531_: *mut leanh::LeanObject,
    mut v_x_3532_: *mut leanh::LeanObject,
    mut v___y_3533_: *mut leanh::LeanObject,
    mut v___y_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
            v_mvarId_3531_,
            v_x_3532_,
            v___y_3533_,
            v___y_3534_,
            v___y_3535_,
            v___y_3536_,
        );
    leanh::lean_dec(v___y_3536_);
    leanh::lean_dec_ref(v___y_3535_);
    leanh::lean_dec(v___y_3534_);
    leanh::lean_dec_ref(v___y_3533_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(
    mut v_00_u03b1_3539_: *mut leanh::LeanObject,
    mut v_mvarId_3540_: *mut leanh::LeanObject,
    mut v_x_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3548_: *mut leanh::LeanObject,
    mut v_mvarId_3549_: *mut leanh::LeanObject,
    mut v_x_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(
        v_00_u03b1_3548_,
        v_mvarId_3549_,
        v_x_3550_,
        v___y_3551_,
        v___y_3552_,
        v___y_3553_,
        v___y_3554_,
    );
    leanh::lean_dec(v___y_3554_);
    leanh::lean_dec_ref(v___y_3553_);
    leanh::lean_dec(v___y_3552_);
    leanh::lean_dec_ref(v___y_3551_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main___lam__0(
    mut v___x_3557_: *mut leanh::LeanObject,
    mut v___x_3558_: *mut leanh::LeanObject,
    mut v_mvarId_3559_: *mut leanh::LeanObject,
    mut v_needle_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
    mut v___y_3563_: *mut leanh::LeanObject,
    mut v___y_3564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_calls_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut v_unused_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3566_ = lean_st_mk_ref(v___x_3557_);
                v___x_3567_ = lean_st_mk_ref(v___x_3558_);
                v___x_3568_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_3559_, v___x_3567_, v_needle_3560_, v___x_3566_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
                if leanh::lean_obj_tag(v___x_3568_) == 0 {
                    v_isSharedCheck_3578_ = (!leanh::lean_is_exclusive(v___x_3568_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v_unused_3579_ = leanh::lean_ctor_get(v___x_3568_, 0);
                        leanh::lean_dec(v_unused_3579_);
                        v___x_3570_ = v___x_3568_;
                        v_isShared_3571_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3568_);
                        v___x_3570_ = leanh::lean_box(0);
                        v_isShared_3571_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3567_);
                    leanh::lean_dec(v___x_3566_);
                    v_a_3580_ = leanh::lean_ctor_get(v___x_3568_, 0);
                    v_isSharedCheck_3587_ = (!leanh::lean_is_exclusive(v___x_3568_)) as u8;
                    if v_isSharedCheck_3587_ == 0 {
                        v___x_3582_ = v___x_3568_;
                        v_isShared_3583_ = v_isSharedCheck_3587_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3580_);
                        leanh::lean_dec(v___x_3568_);
                        v___x_3582_ = leanh::lean_box(0);
                        v_isShared_3583_ = v_isSharedCheck_3587_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3572_ = lean_st_ref_get(v___x_3567_);
                leanh::lean_dec(v___x_3567_);
                leanh::lean_dec(v___x_3572_);
                v___x_3573_ = lean_st_ref_get(v___x_3566_);
                leanh::lean_dec(v___x_3566_);
                v_calls_3574_ = leanh::lean_ctor_get(v___x_3573_, 0);
                leanh::lean_inc_ref(v_calls_3574_);
                leanh::lean_dec(v___x_3573_);
                if v_isShared_3571_ == 0 {
                    leanh::lean_ctor_set(v___x_3570_, 0, v_calls_3574_);
                    v___x_3576_ = v___x_3570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_calls_3574_);
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
                    v_reuseFailAlloc_3586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
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
    mut v___x_3588_: *mut leanh::LeanObject,
    mut v___x_3589_: *mut leanh::LeanObject,
    mut v_mvarId_3590_: *mut leanh::LeanObject,
    mut v_needle_3591_: *mut leanh::LeanObject,
    mut v___y_3592_: *mut leanh::LeanObject,
    mut v___y_3593_: *mut leanh::LeanObject,
    mut v___y_3594_: *mut leanh::LeanObject,
    mut v___y_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3595_);
    leanh::lean_dec_ref(v___y_3594_);
    leanh::lean_dec(v___y_3593_);
    leanh::lean_dec_ref(v___y_3592_);
    leanh::lean_dec_ref(v_needle_3591_);
    return v_res_3597_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_Collector_main___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = leanh::lean_unsigned_to_nat(64);
    v___x_3599_ = l_Lean_mkPtrSet___redArg(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main(
    mut v_needle_3600_: *mut leanh::LeanObject,
    mut v_mvarId_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v_a_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
    mut v_a_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3607_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_Collector_main___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_Collector_main___closed__0_once),
        _init_l_Lean_Meta_FunInd_Collector_main___closed__0,
    );
    v___x_3608_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3,
    );
    leanh::lean_inc(v_mvarId_3601_);
    v___f_3609_ = leanh::lean_alloc_closure(
        l_Lean_Meta_FunInd_Collector_main___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_3609_, 0, v___x_3608_);
    leanh::lean_closure_set(v___f_3609_, 1, v___x_3607_);
    leanh::lean_closure_set(v___f_3609_, 2, v_mvarId_3601_);
    leanh::lean_closure_set(v___f_3609_, 3, v_needle_3600_);
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
    mut v_needle_3611_: *mut leanh::LeanObject,
    mut v_mvarId_3612_: *mut leanh::LeanObject,
    mut v_a_3613_: *mut leanh::LeanObject,
    mut v_a_3614_: *mut leanh::LeanObject,
    mut v_a_3615_: *mut leanh::LeanObject,
    mut v_a_3616_: *mut leanh::LeanObject,
    mut v_a_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Lean_Meta_FunInd_Collector_main(
        v_needle_3611_,
        v_mvarId_3612_,
        v_a_3613_,
        v_a_3614_,
        v_a_3615_,
        v_a_3616_,
    );
    leanh::lean_dec(v_a_3616_);
    leanh::lean_dec_ref(v_a_3615_);
    leanh::lean_dec(v_a_3614_);
    leanh::lean_dec_ref(v_a_3613_);
    return v_res_3618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(
    mut v_needle_3619_: *mut leanh::LeanObject,
    mut v_mvarId_3620_: *mut leanh::LeanObject,
    mut v_a_3621_: *mut leanh::LeanObject,
    mut v_a_3622_: *mut leanh::LeanObject,
    mut v_a_3623_: *mut leanh::LeanObject,
    mut v_a_3624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_needle_3627_: *mut leanh::LeanObject,
    mut v_mvarId_3628_: *mut leanh::LeanObject,
    mut v_a_3629_: *mut leanh::LeanObject,
    mut v_a_3630_: *mut leanh::LeanObject,
    mut v_a_3631_: *mut leanh::LeanObject,
    mut v_a_3632_: *mut leanh::LeanObject,
    mut v_a_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3634_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(
        v_needle_3627_,
        v_mvarId_3628_,
        v_a_3629_,
        v_a_3630_,
        v_a_3631_,
        v_a_3632_,
    );
    leanh::lean_dec(v_a_3632_);
    leanh::lean_dec_ref(v_a_3631_);
    leanh::lean_dec(v_a_3630_);
    leanh::lean_dec_ref(v_a_3629_);
    return v_res_3634_;
}
pub unsafe fn l_Lean_Meta_FunInd_collect(
    mut v_needle_3635_: *mut leanh::LeanObject,
    mut v_mvarId_3636_: *mut leanh::LeanObject,
    mut v_a_3637_: *mut leanh::LeanObject,
    mut v_a_3638_: *mut leanh::LeanObject,
    mut v_a_3639_: *mut leanh::LeanObject,
    mut v_a_3640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_needle_3643_: *mut leanh::LeanObject,
    mut v_mvarId_3644_: *mut leanh::LeanObject,
    mut v_a_3645_: *mut leanh::LeanObject,
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v_a_3647_: *mut leanh::LeanObject,
    mut v_a_3648_: *mut leanh::LeanObject,
    mut v_a_3649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ = l_Lean_Meta_FunInd_collect(
        v_needle_3643_,
        v_mvarId_3644_,
        v_a_3645_,
        v_a_3646_,
        v_a_3647_,
        v_a_3648_,
    );
    leanh::lean_dec(v_a_3648_);
    leanh::lean_dec_ref(v_a_3647_);
    leanh::lean_dec(v_a_3646_);
    leanh::lean_dec_ref(v_a_3645_);
    return v_res_3650_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_FunIndCollect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls =
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls();
    leanh::lean_mark_persistent(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_FunIndCollect(
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
pub unsafe fn initialize_Lean_Meta_Tactic_FunIndCollect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
}
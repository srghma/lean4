// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndCollect
// Imports: Lean.Meta.Tactic.Util Lean.Meta.Tactic.FunIndInfo
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_to_uint64,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_uint64, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lean_Meta_FunInd_instHashableCall___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_FunInd_instHashableCall_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_FunInd_instHashableCall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instHashableCall___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_FunInd_instHashableCall: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instHashableCall___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_FunInd_instBEqCall___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_FunInd_instBEqCall_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_FunInd_instBEqCall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instBEqCall___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_FunInd_instBEqCall: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instBEqCall___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0: u64 = 0;
static mut l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_Collector_visit___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_Collector_visit___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_FunInd_Collector_main___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_FunInd_Collector_main___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_FunInd_instHashableCall_hash(mut v_x_1826_: *mut LeanObject) -> u64 {
    let mut v_expr_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u64 = 0;
    let mut v___x_1830_: u64 = 0;
    let mut v___x_1831_: u64 = 0;
    let mut v___x_1832_: u64 = 0;
    let mut v___x_1833_: u64 = 0;
    v_expr_1827_ = lean_ctor_get(v_x_1826_, 0);
    v_relevantArgs_1828_ = lean_ctor_get(v_x_1826_, 1);
    v___x_1829_ = 0u64;
    v___x_1830_ = l_Lean_Expr_hash(v_expr_1827_);
    v___x_1831_ = lean_uint64_mix_hash(v___x_1829_, v___x_1830_);
    v___x_1832_ = l_Lean_Expr_hash(v_relevantArgs_1828_);
    v___x_1833_ = lean_uint64_mix_hash(v___x_1831_, v___x_1832_);
    return v___x_1833_;
}
pub unsafe fn l_Lean_Meta_FunInd_instHashableCall_hash___boxed(
    mut v_x_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1835_: u64 = 0;
    let mut v_r_1836_: *mut LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lean_Meta_FunInd_instHashableCall_hash(v_x_1834_);
    lean_dec_ref(v_x_1834_);
    v_r_1836_ = lean_box_uint64(v_res_1835_);
    return v_r_1836_;
}
pub unsafe fn l_Lean_Meta_FunInd_instBEqCall_beq(
    mut v_x_1839_: *mut LeanObject,
    mut v_x_1840_: *mut LeanObject,
) -> u8 {
    let mut v_expr_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantArgs_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    v_expr_1841_ = lean_ctor_get(v_x_1839_, 0);
    v_relevantArgs_1842_ = lean_ctor_get(v_x_1839_, 1);
    v_expr_1843_ = lean_ctor_get(v_x_1840_, 0);
    v_relevantArgs_1844_ = lean_ctor_get(v_x_1840_, 1);
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
    mut v_x_1847_: *mut LeanObject,
    mut v_x_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1849_: u8 = 0;
    let mut v_r_1850_: *mut LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_Meta_FunInd_instBEqCall_beq(v_x_1847_, v_x_1848_);
    lean_dec_ref(v_x_1848_);
    lean_dec_ref(v_x_1847_);
    v_r_1850_ = lean_box((v_res_1849_) as usize);
    return v_r_1850_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1() -> *mut LeanObject
{
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    v___x_1855_ = lean_box(0);
    v___x_1856_ = lean_unsigned_to_nat(16);
    v___x_1857_ = lean_mk_array(v___x_1856_, v___x_1855_);
    return v___x_1857_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2() -> *mut LeanObject
{
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    v___x_1858_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1,
    );
    v___x_1859_ = lean_unsigned_to_nat(0);
    v___x_1860_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    lean_ctor_set(v___x_1860_, 1, v___x_1858_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3() -> *mut LeanObject
{
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    v___x_1861_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2,
    );
    v___x_1862_ = l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0;
    v___x_1863_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls() -> *mut LeanObject {
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3,
    );
    return v___x_1864_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_isEmpty(mut v_sc_1865_: *mut LeanObject) -> u8 {
    let mut v_calls_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    v_calls_1866_ = lean_ctor_get(v_sc_1865_, 0);
    v___x_1867_ = lean_array_get_size(v_calls_1866_);
    v___x_1868_ = lean_unsigned_to_nat(0);
    v___x_1869_ = lean_nat_dec_eq(v___x_1867_, v___x_1868_);
    return v___x_1869_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(
    mut v_sc_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1871_: u8 = 0;
    let mut v_r_1872_: *mut LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_Meta_FunInd_SeenCalls_isEmpty(v_sc_1870_);
    lean_dec_ref(v_sc_1870_);
    v_r_1872_ = lean_box((v_res_1871_) as usize);
    return v_r_1872_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(
    mut v_xs_1873_: *mut LeanObject,
    mut v_ys_1874_: *mut LeanObject,
    mut v_x_1875_: *mut LeanObject,
) -> u8 {
    let mut v_zero_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1877_: u8 = 0;
    let mut v_one_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1876_ = lean_unsigned_to_nat(0);
                v_isZero_1877_ = lean_nat_dec_eq(v_x_1875_, v_zero_1876_);
                if v_isZero_1877_ == 1 {
                    lean_dec(v_x_1875_);
                    return v_isZero_1877_;
                } else {
                    v_one_1878_ = lean_unsigned_to_nat(1);
                    v_n_1879_ = lean_nat_sub(v_x_1875_, v_one_1878_);
                    lean_dec(v_x_1875_);
                    v___x_1880_ = lean_array_fget_borrowed(v_xs_1873_, v_n_1879_);
                    v___x_1881_ = lean_array_fget_borrowed(v_ys_1874_, v_n_1879_);
                    v___x_1882_ = lean_expr_eqv(v___x_1880_, v___x_1881_);
                    if v___x_1882_ == 0 {
                        lean_dec(v_n_1879_);
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
    mut v_xs_1884_: *mut LeanObject,
    mut v_ys_1885_: *mut LeanObject,
    mut v_x_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1887_: u8 = 0;
    let mut v_r_1888_: *mut LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_1884_, v_ys_1885_, v_x_1886_);
    lean_dec_ref(v_ys_1885_);
    lean_dec_ref(v_xs_1884_);
    v_r_1888_ = lean_box((v_res_1887_) as usize);
    return v_r_1888_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(
    mut v_a_1889_: *mut LeanObject,
    mut v_x_1890_: *mut LeanObject,
) -> u8 {
    let mut v___x_1891_: u8 = 0;
    let mut v_key_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: u8 = 0;
    let mut v_fst_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1890_) == 0 {
                    v___x_1891_ = 0;
                    return v___x_1891_;
                } else {
                    v_key_1892_ = lean_ctor_get(v_x_1890_, 0);
                    v_tail_1893_ = lean_ctor_get(v_x_1890_, 2);
                    v_fst_1897_ = lean_ctor_get(v_key_1892_, 0);
                    v_snd_1898_ = lean_ctor_get(v_key_1892_, 1);
                    v_fst_1899_ = lean_ctor_get(v_a_1889_, 0);
                    v_snd_1900_ = lean_ctor_get(v_a_1889_, 1);
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
    mut v_a_1907_: *mut LeanObject,
    mut v_x_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1909_: u8 = 0;
    let mut v_r_1910_: *mut LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_1907_, v_x_1908_);
    lean_dec(v_x_1908_);
    lean_dec_ref(v_a_1907_);
    v_r_1910_ = lean_box((v_res_1909_) as usize);
    return v_r_1910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(
    mut v_as_1911_: *mut LeanObject,
    mut v_i_1912_: usize,
    mut v_stop_1913_: usize,
    mut v_b_1914_: u64,
) -> u64 {
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_1922_: *mut LeanObject,
    mut v_i_1923_: *mut LeanObject,
    mut v_stop_1924_: *mut LeanObject,
    mut v_b_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1926_: usize = 0;
    let mut v_stop_boxed_1927_: usize = 0;
    let mut v_b_boxed_1928_: u64 = 0;
    let mut v_res_1929_: u64 = 0;
    let mut v_r_1930_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1926_ = lean_unbox_usize(v_i_1923_);
    lean_dec(v_i_1923_);
    v_stop_boxed_1927_ = lean_unbox_usize(v_stop_1924_);
    lean_dec(v_stop_1924_);
    v_b_boxed_1928_ = lean_unbox_uint64(v_b_1925_);
    lean_dec_ref(v_b_1925_);
    v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_as_1922_, v_i_boxed_1926_, v_stop_boxed_1927_, v_b_boxed_1928_);
    lean_dec_ref(v_as_1922_);
    v_r_1930_ = lean_box_uint64(v_res_1929_);
    return v_r_1930_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u64 = 0;
    v___x_1931_ = lean_unsigned_to_nat(1723);
    v___x_1932_ = lean_uint64_of_nat(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(
    mut v_x_1933_: *mut LeanObject,
    mut v_x_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v_fst_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1966_: u64 = 0;
    let mut v___x_1967_: u64 = 0;
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v_x_1934_) == 0 {
                    return v_x_1933_;
                } else {
                    v_key_1935_ = lean_ctor_get(v_x_1934_, 0);
                    v_value_1936_ = lean_ctor_get(v_x_1934_, 1);
                    v_tail_1937_ = lean_ctor_get(v_x_1934_, 2);
                    v_isSharedCheck_1980_ = (!lean_is_exclusive(v_x_1934_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v___x_1939_ = v_x_1934_;
                        v_isShared_1940_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1937_);
                        lean_inc(v_value_1936_);
                        lean_inc(v_key_1935_);
                        lean_dec(v_x_1934_);
                        v___x_1939_ = lean_box(0);
                        v_isShared_1940_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1941_ = lean_ctor_get(v_key_1935_, 0);
                v_snd_1942_ = lean_ctor_get(v_key_1935_, 1);
                v___x_1943_ = lean_array_get_size(v_x_1933_);
                if lean_obj_tag(v_fst_1941_) == 0 {
                    v___x_1978_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_1966_ = v___x_1978_;
                    state = 4;
                    continue;
                } else {
                    v_hash_1979_ = lean_ctor_get_uint64(
                        v_fst_1941_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                lean_inc(v___x_1959_);
                if v_isShared_1940_ == 0 {
                    lean_ctor_set(v___x_1939_, 2, v___x_1959_);
                    v___x_1961_ = v___x_1939_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_key_1935_);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_value_1936_);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 2, v___x_1959_);
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
                v___x_1968_ = lean_unsigned_to_nat(0);
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
    mut v_i_1981_: *mut LeanObject,
    mut v_source_1982_: *mut LeanObject,
    mut v_target_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v_es_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1984_ = lean_array_get_size(v_source_1982_);
                v___x_1985_ = lean_nat_dec_lt(v_i_1981_, v___x_1984_);
                if v___x_1985_ == 0 {
                    lean_dec_ref(v_source_1982_);
                    lean_dec(v_i_1981_);
                    return v_target_1983_;
                } else {
                    v_es_1986_ = lean_array_fget(v_source_1982_, v_i_1981_);
                    v___x_1987_ = lean_box(0);
                    v_source_1988_ = lean_array_fset(v_source_1982_, v_i_1981_, v___x_1987_);
                    v_target_1989_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_target_1983_, v_es_1986_);
                    v___x_1990_ = lean_unsigned_to_nat(1);
                    v___x_1991_ = lean_nat_add(v_i_1981_, v___x_1990_);
                    lean_dec(v_i_1981_);
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
    mut v_data_1993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1994_ = lean_array_get_size(v_data_1993_);
    v___x_1995_ = lean_unsigned_to_nat(2);
    v_nbuckets_1996_ = lean_nat_mul(v___x_1994_, v___x_1995_);
    v___x_1997_ = lean_unsigned_to_nat(0);
    v___x_1998_ = lean_box(0);
    v___x_1999_ = lean_mk_array(v_nbuckets_1996_, v___x_1998_);
    v___x_2000_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_1997_, v_data_1993_, v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(
    mut v_m_2001_: *mut LeanObject,
    mut v_a_2002_: *mut LeanObject,
    mut v_b_2003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: u8 = 0;
    let mut v_val_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_unused_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2050_: u64 = 0;
    let mut v___x_2051_: u64 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
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
                v_size_2004_ = lean_ctor_get(v_m_2001_, 0);
                v_buckets_2005_ = lean_ctor_get(v_m_2001_, 1);
                v_fst_2006_ = lean_ctor_get(v_a_2002_, 0);
                v_snd_2007_ = lean_ctor_get(v_a_2002_, 1);
                v___x_2008_ = lean_array_get_size(v_buckets_2005_);
                if lean_obj_tag(v_fst_2006_) == 0 {
                    v___x_2062_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_2050_ = v___x_2062_;
                    state = 5;
                    continue;
                } else {
                    v_hash_2063_ = lean_ctor_get_uint64(
                        v_fst_2006_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    lean_inc_ref(v_buckets_2005_);
                    lean_inc(v_size_2004_);
                    v_isSharedCheck_2046_ = (!lean_is_exclusive(v_m_2001_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v_unused_2047_ = lean_ctor_get(v_m_2001_, 1);
                        lean_dec(v_unused_2047_);
                        v_unused_2048_ = lean_ctor_get(v_m_2001_, 0);
                        lean_dec(v_unused_2048_);
                        v___x_2027_ = v_m_2001_;
                        v_isShared_2028_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_2001_);
                        v___x_2027_ = lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2003_);
                    lean_dec_ref(v_a_2002_);
                    return v_m_2001_;
                }
            }
            2 => {
                v___x_2029_ = lean_unsigned_to_nat(1);
                v_size_x27_2030_ = lean_nat_add(v_size_2004_, v___x_2029_);
                lean_dec(v_size_2004_);
                lean_inc(v_bkt_2024_);
                v___x_2031_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2031_, 0, v_a_2002_);
                lean_ctor_set(v___x_2031_, 1, v_b_2003_);
                lean_ctor_set(v___x_2031_, 2, v_bkt_2024_);
                v_buckets_x27_2032_ = lean_array_uset(v_buckets_2005_, v___x_2023_, v___x_2031_);
                v___x_2033_ = lean_unsigned_to_nat(4);
                v___x_2034_ = lean_nat_mul(v_size_x27_2030_, v___x_2033_);
                v___x_2035_ = lean_unsigned_to_nat(3);
                v___x_2036_ = lean_nat_div(v___x_2034_, v___x_2035_);
                lean_dec(v___x_2034_);
                v___x_2037_ = lean_array_get_size(v_buckets_x27_2032_);
                v___x_2038_ = lean_nat_dec_le(v___x_2036_, v___x_2037_);
                lean_dec(v___x_2036_);
                if v___x_2038_ == 0 {
                    v_val_2039_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_2032_);
                    if v_isShared_2028_ == 0 {
                        lean_ctor_set(v___x_2027_, 1, v_val_2039_);
                        lean_ctor_set(v___x_2027_, 0, v_size_x27_2030_);
                        v___x_2041_ = v___x_2027_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_size_x27_2030_);
                        lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_val_2039_);
                        v___x_2041_ = v_reuseFailAlloc_2042_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2028_ == 0 {
                        lean_ctor_set(v___x_2027_, 1, v_buckets_x27_2032_);
                        lean_ctor_set(v___x_2027_, 0, v_size_x27_2030_);
                        v___x_2044_ = v___x_2027_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_size_x27_2030_);
                        lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_buckets_x27_2032_);
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
                v___x_2052_ = lean_unsigned_to_nat(0);
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
    mut v_m_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    let mut v___y_2088_: u64 = 0;
    let mut v___x_2089_: u64 = 0;
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
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
                v_buckets_2066_ = lean_ctor_get(v_m_2064_, 1);
                v_fst_2067_ = lean_ctor_get(v_a_2065_, 0);
                v_snd_2068_ = lean_ctor_get(v_a_2065_, 1);
                v___x_2069_ = lean_array_get_size(v_buckets_2066_);
                if lean_obj_tag(v_fst_2067_) == 0 {
                    v___x_2100_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                    v___y_2088_ = v___x_2100_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2101_ = lean_ctor_get_uint64(
                        v_fst_2067_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                v___x_2090_ = lean_unsigned_to_nat(0);
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
    mut v_m_2102_: *mut LeanObject,
    mut v_a_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2104_: u8 = 0;
    let mut v_r_2105_: *mut LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_2102_, v_a_2103_);
    lean_dec_ref(v_a_2103_);
    lean_dec_ref(v_m_2102_);
    v_r_2105_ = lean_box((v_res_2104_) as usize);
    return v_r_2105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(
    mut v_calls_2106_: *mut LeanObject,
    mut v_as_2107_: *mut LeanObject,
    mut v_sz_2108_: usize,
    mut v_i_2109_: usize,
    mut v_b_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v_snd_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2127_: u8 = 0;
    let mut v_array_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v_a_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2171_: u8 = 0;
    let mut v_unused_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v_unused_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2117_ = lean_usize_dec_lt(v_i_2109_, v_sz_2108_);
                if v___x_2117_ == 0 {
                    lean_dec_ref(v_calls_2106_);
                    v___x_2118_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2118_, 0, v_b_2110_);
                    return v___x_2118_;
                } else {
                    v_snd_2119_ = lean_ctor_get(v_b_2110_, 1);
                    v_isSharedCheck_2176_ = (!lean_is_exclusive(v_b_2110_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v_unused_2177_ = lean_ctor_get(v_b_2110_, 0);
                        lean_dec(v_unused_2177_);
                        v___x_2121_ = v_b_2110_;
                        v_isShared_2122_ = v_isSharedCheck_2176_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_2119_);
                        lean_dec(v_b_2110_);
                        v___x_2121_ = lean_box(0);
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
                v_snd_2123_ = lean_ctor_get(v_snd_2119_, 1);
                v_fst_2124_ = lean_ctor_get(v_snd_2119_, 0);
                v_isSharedCheck_2175_ = (!lean_is_exclusive(v_snd_2119_)) as u8;
                if v_isSharedCheck_2175_ == 0 {
                    v___x_2126_ = v_snd_2119_;
                    v_isShared_2127_ = v_isSharedCheck_2175_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_2123_);
                    lean_inc(v_fst_2124_);
                    lean_dec(v_snd_2119_);
                    v___x_2126_ = lean_box(0);
                    v_isShared_2127_ = v_isSharedCheck_2175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_2128_ = lean_ctor_get(v_snd_2123_, 0);
                v_start_2129_ = lean_ctor_get(v_snd_2123_, 1);
                v_stop_2130_ = lean_ctor_get(v_snd_2123_, 2);
                v___x_2131_ = lean_box(0);
                v___x_2132_ = lean_nat_dec_lt(v_start_2129_, v_stop_2130_);
                if v___x_2132_ == 0 {
                    lean_dec_ref(v_calls_2106_);
                    if v_isShared_2127_ == 0 {
                        v___x_2134_ = v___x_2126_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_fst_2124_);
                        lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_snd_2123_);
                        v___x_2134_ = v_reuseFailAlloc_2139_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_2130_);
                    lean_inc(v_start_2129_);
                    lean_inc_ref(v_array_2128_);
                    v_isSharedCheck_2171_ = (!lean_is_exclusive(v_snd_2123_)) as u8;
                    if v_isSharedCheck_2171_ == 0 {
                        v_unused_2172_ = lean_ctor_get(v_snd_2123_, 2);
                        lean_dec(v_unused_2172_);
                        v_unused_2173_ = lean_ctor_get(v_snd_2123_, 1);
                        lean_dec(v_unused_2173_);
                        v_unused_2174_ = lean_ctor_get(v_snd_2123_, 0);
                        lean_dec(v_unused_2174_);
                        v___x_2141_ = v_snd_2123_;
                        v_isShared_2142_ = v_isSharedCheck_2171_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_snd_2123_);
                        v___x_2141_ = lean_box(0);
                        v_isShared_2142_ = v_isSharedCheck_2171_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2122_ == 0 {
                    lean_ctor_set(v___x_2121_, 1, v___x_2134_);
                    lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2136_ = v___x_2121_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2134_);
                    v___x_2136_ = v_reuseFailAlloc_2138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2137_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2137_, 0, v___x_2136_);
                return v___x_2137_;
            }
            6 => {
                v_a_2143_ = lean_array_uget_borrowed(v_as_2107_, v_i_2109_);
                v___x_2144_ = lean_array_fget(v_array_2128_, v_start_2129_);
                v___x_2145_ = lean_unsigned_to_nat(1);
                v___x_2146_ = lean_nat_add(v_start_2129_, v___x_2145_);
                lean_dec(v_start_2129_);
                if v_isShared_2142_ == 0 {
                    lean_ctor_set(v___x_2141_, 1, v___x_2146_);
                    v___x_2148_ = v___x_2141_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_array_2128_);
                    lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2146_);
                    lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_stop_2130_);
                    v___x_2148_ = v_reuseFailAlloc_2170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2164_ = (lean_unbox(v___x_2144_) as u8);
                if v___x_2164_ == 2 {
                    v___x_2165_ = l_Lean_Expr_isFVar(v_a_2143_);
                    if v___x_2165_ == 0 {
                        lean_dec(v___x_2144_);
                        lean_del_object(v___x_2126_);
                        lean_del_object(v___x_2121_);
                        v___x_2166_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2166_, 0, v_calls_2106_);
                        v___x_2167_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2167_, 0, v_fst_2124_);
                        lean_ctor_set(v___x_2167_, 1, v___x_2148_);
                        v___x_2168_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2168_, 0, v___x_2166_);
                        lean_ctor_set(v___x_2168_, 1, v___x_2167_);
                        v___x_2169_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2169_, 0, v___x_2168_);
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
                v___x_2150_ = (lean_unbox(v___x_2144_) as u8);
                lean_dec(v___x_2144_);
                if v___x_2150_ == 0 {
                    if v_isShared_2127_ == 0 {
                        lean_ctor_set(v___x_2126_, 1, v___x_2148_);
                        v___x_2152_ = v___x_2126_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_fst_2124_);
                        lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2148_);
                        v___x_2152_ = v_reuseFailAlloc_2156_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_inc(v_a_2143_);
                    v___x_2157_ = lean_array_push(v_fst_2124_, v_a_2143_);
                    if v_isShared_2127_ == 0 {
                        lean_ctor_set(v___x_2126_, 1, v___x_2148_);
                        lean_ctor_set(v___x_2126_, 0, v___x_2157_);
                        v___x_2159_ = v___x_2126_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
                        lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2148_);
                        v___x_2159_ = v_reuseFailAlloc_2163_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2122_ == 0 {
                    lean_ctor_set(v___x_2121_, 1, v___x_2152_);
                    lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2154_ = v___x_2121_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2152_);
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
                    lean_ctor_set(v___x_2121_, 1, v___x_2159_);
                    lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2161_ = v___x_2121_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
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
    mut v_calls_2178_: *mut LeanObject,
    mut v_as_2179_: *mut LeanObject,
    mut v_sz_2180_: *mut LeanObject,
    mut v_i_2181_: *mut LeanObject,
    mut v_b_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2184_: usize = 0;
    let mut v_i_boxed_2185_: usize = 0;
    let mut v_res_2186_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2184_ = lean_unbox_usize(v_sz_2180_);
    lean_dec(v_sz_2180_);
    v_i_boxed_2185_ = lean_unbox_usize(v_i_2181_);
    lean_dec(v_i_2181_);
    v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2178_, v_as_2179_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2182_);
    lean_dec_ref(v_as_2179_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_push(
    mut v_e_2187_: *mut LeanObject,
    mut v_funIndInfo_2188_: *mut LeanObject,
    mut v_args_2189_: *mut LeanObject,
    mut v_calls_2190_: *mut LeanObject,
    mut v_a_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_funName_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2208_: usize = 0;
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v_fst_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v_calls_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_unused_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_unused_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_a_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_funName_2196_ = lean_ctor_get(v_funIndInfo_2188_, 0);
                lean_inc(v_funName_2196_);
                v_params_2197_ = lean_ctor_get(v_funIndInfo_2188_, 3);
                lean_inc_ref(v_params_2197_);
                lean_dec_ref(v_funIndInfo_2188_);
                v___x_2198_ = lean_array_get_size(v_params_2197_);
                v___x_2199_ = lean_array_get_size(v_args_2189_);
                v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
                if v___x_2200_ == 0 {
                    lean_dec_ref(v_params_2197_);
                    lean_dec(v_funName_2196_);
                    lean_dec_ref(v_e_2187_);
                    v___x_2201_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2201_, 0, v_calls_2190_);
                    return v___x_2201_;
                } else {
                    v___x_2202_ = lean_unsigned_to_nat(0);
                    v_keys_2203_ = l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0;
                    v___x_2204_ =
                        l_Array_toSubarray___redArg(v_params_2197_, v___x_2202_, v___x_2198_);
                    v___x_2205_ = lean_box(0);
                    v___x_2206_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2206_, 0, v_keys_2203_);
                    lean_ctor_set(v___x_2206_, 1, v___x_2204_);
                    v___x_2207_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2207_, 0, v___x_2205_);
                    lean_ctor_set(v___x_2207_, 1, v___x_2206_);
                    v_sz_2208_ = lean_array_size(v_args_2189_);
                    v___x_2209_ = 0usize;
                    lean_inc_ref(v_calls_2190_);
                    v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2190_, v_args_2189_, v_sz_2208_, v___x_2209_, v___x_2207_);
                    if lean_obj_tag(v___x_2210_) == 0 {
                        v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2251_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2251_ == 0 {
                            v___x_2213_ = v___x_2210_;
                            v_isShared_2214_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2211_);
                            lean_dec(v___x_2210_);
                            v___x_2213_ = lean_box(0);
                            v_isShared_2214_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_funName_2196_);
                        lean_dec_ref(v_calls_2190_);
                        lean_dec_ref(v_e_2187_);
                        v_a_2252_ = lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2259_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2259_ == 0 {
                            v___x_2254_ = v___x_2210_;
                            v_isShared_2255_ = v_isSharedCheck_2259_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2252_);
                            lean_dec(v___x_2210_);
                            v___x_2254_ = lean_box(0);
                            v_isShared_2255_ = v_isSharedCheck_2259_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2215_ = lean_ctor_get(v_a_2211_, 0);
                if lean_obj_tag(v_fst_2215_) == 0 {
                    v_snd_2216_ = lean_ctor_get(v_a_2211_, 1);
                    lean_inc(v_snd_2216_);
                    lean_dec(v_a_2211_);
                    v_fst_2217_ = lean_ctor_get(v_snd_2216_, 0);
                    v_isSharedCheck_2245_ = (!lean_is_exclusive(v_snd_2216_)) as u8;
                    if v_isSharedCheck_2245_ == 0 {
                        v_unused_2246_ = lean_ctor_get(v_snd_2216_, 1);
                        lean_dec(v_unused_2246_);
                        v___x_2219_ = v_snd_2216_;
                        v_isShared_2220_ = v_isSharedCheck_2245_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_2217_);
                        lean_dec(v_snd_2216_);
                        v___x_2219_ = lean_box(0);
                        v_isShared_2220_ = v_isSharedCheck_2245_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2215_);
                    lean_dec(v_a_2211_);
                    lean_dec(v_funName_2196_);
                    lean_dec_ref(v_calls_2190_);
                    lean_dec_ref(v_e_2187_);
                    v_val_2247_ = lean_ctor_get(v_fst_2215_, 0);
                    lean_inc(v_val_2247_);
                    lean_dec_ref_known(v_fst_2215_, 1);
                    if v_isShared_2214_ == 0 {
                        lean_ctor_set(v___x_2213_, 0, v_val_2247_);
                        v___x_2249_ = v___x_2213_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_val_2247_);
                        v___x_2249_ = v_reuseFailAlloc_2250_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_calls_2221_ = lean_ctor_get(v_calls_2190_, 0);
                v_seen_2222_ = lean_ctor_get(v_calls_2190_, 1);
                if v_isShared_2220_ == 0 {
                    lean_ctor_set(v___x_2219_, 1, v_fst_2217_);
                    lean_ctor_set(v___x_2219_, 0, v_funName_2196_);
                    v___x_2224_ = v___x_2219_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_funName_2196_);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_fst_2217_);
                    v___x_2224_ = v_reuseFailAlloc_2244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2225_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_2222_, v___x_2224_);
                if v___x_2225_ == 0 {
                    lean_inc_ref(v_seen_2222_);
                    lean_inc_ref(v_calls_2221_);
                    v_isSharedCheck_2238_ = (!lean_is_exclusive(v_calls_2190_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v_unused_2239_ = lean_ctor_get(v_calls_2190_, 1);
                        lean_dec(v_unused_2239_);
                        v_unused_2240_ = lean_ctor_get(v_calls_2190_, 0);
                        lean_dec(v_unused_2240_);
                        v___x_2227_ = v_calls_2190_;
                        v_isShared_2228_ = v_isSharedCheck_2238_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_calls_2190_);
                        v___x_2227_ = lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2238_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2224_);
                    lean_dec_ref(v_e_2187_);
                    if v_isShared_2214_ == 0 {
                        lean_ctor_set(v___x_2213_, 0, v_calls_2190_);
                        v___x_2242_ = v___x_2213_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_calls_2190_);
                        v___x_2242_ = v_reuseFailAlloc_2243_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2229_ = lean_array_push(v_calls_2221_, v_e_2187_);
                v___x_2230_ = lean_box(0);
                v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_2222_, v___x_2224_, v___x_2230_);
                if v_isShared_2228_ == 0 {
                    lean_ctor_set(v___x_2227_, 1, v___x_2231_);
                    lean_ctor_set(v___x_2227_, 0, v___x_2229_);
                    v___x_2233_ = v___x_2227_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2231_);
                    v___x_2233_ = v_reuseFailAlloc_2237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2214_ == 0 {
                    lean_ctor_set(v___x_2213_, 0, v___x_2233_);
                    v___x_2235_ = v___x_2213_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
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
                    v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
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
    mut v_e_2260_: *mut LeanObject,
    mut v_funIndInfo_2261_: *mut LeanObject,
    mut v_args_2262_: *mut LeanObject,
    mut v_calls_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2269_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2267_);
    lean_dec_ref(v_a_2266_);
    lean_dec(v_a_2265_);
    lean_dec_ref(v_a_2264_);
    lean_dec_ref(v_args_2262_);
    return v_res_2269_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(
    mut v_calls_2270_: *mut LeanObject,
    mut v_as_2271_: *mut LeanObject,
    mut v_sz_2272_: usize,
    mut v_i_2273_: usize,
    mut v_b_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
    mut v___y_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_2270_, v_as_2271_, v_sz_2272_, v_i_2273_, v_b_2274_);
    return v___x_2280_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(
    mut v_calls_2281_: *mut LeanObject,
    mut v_as_2282_: *mut LeanObject,
    mut v_sz_2283_: *mut LeanObject,
    mut v_i_2284_: *mut LeanObject,
    mut v_b_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2291_: usize = 0;
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_res_2293_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2291_ = lean_unbox_usize(v_sz_2283_);
    lean_dec(v_sz_2283_);
    v_i_boxed_2292_ = lean_unbox_usize(v_i_2284_);
    lean_dec(v_i_2284_);
    v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_2281_, v_as_2282_, v_sz_boxed_2291_, v_i_boxed_2292_, v_b_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
    lean_dec(v___y_2289_);
    lean_dec_ref(v___y_2288_);
    lean_dec(v___y_2287_);
    lean_dec_ref(v___y_2286_);
    lean_dec_ref(v_as_2282_);
    return v_res_2293_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(
    mut v_00_u03b2_2294_: *mut LeanObject,
    mut v_m_2295_: *mut LeanObject,
    mut v_a_2296_: *mut LeanObject,
) -> u8 {
    let mut v___x_2297_: u8 = 0;
    v___x_2297_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_2295_, v_a_2296_);
    return v___x_2297_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(
    mut v_00_u03b2_2298_: *mut LeanObject,
    mut v_m_2299_: *mut LeanObject,
    mut v_a_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2301_: u8 = 0;
    let mut v_r_2302_: *mut LeanObject = core::ptr::null_mut();
    v_res_2301_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(
            v_00_u03b2_2298_,
            v_m_2299_,
            v_a_2300_,
        );
    lean_dec_ref(v_a_2300_);
    lean_dec_ref(v_m_2299_);
    v_r_2302_ = lean_box((v_res_2301_) as usize);
    return v_r_2302_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(
    mut v_00_u03b2_2303_: *mut LeanObject,
    mut v_m_2304_: *mut LeanObject,
    mut v_a_2305_: *mut LeanObject,
    mut v_b_2306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_2304_, v_a_2305_, v_b_2306_);
    return v___x_2307_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(
    mut v_00_u03b2_2308_: *mut LeanObject,
    mut v_a_2309_: *mut LeanObject,
    mut v_x_2310_: *mut LeanObject,
) -> u8 {
    let mut v___x_2311_: u8 = 0;
    v___x_2311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_2309_, v_x_2310_);
    return v___x_2311_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(
    mut v_00_u03b2_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
    mut v_x_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2315_: u8 = 0;
    let mut v_r_2316_: *mut LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_2312_, v_a_2313_, v_x_2314_);
    lean_dec(v_x_2314_);
    lean_dec_ref(v_a_2313_);
    v_r_2316_ = lean_box((v_res_2315_) as usize);
    return v_r_2316_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(
    mut v_00_u03b2_2317_: *mut LeanObject,
    mut v_data_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_2318_);
    return v___x_2319_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(
    mut v_xs_2320_: *mut LeanObject,
    mut v_ys_2321_: *mut LeanObject,
    mut v_hsz_2322_: *mut LeanObject,
    mut v_x_2323_: *mut LeanObject,
    mut v_x_2324_: *mut LeanObject,
) -> u8 {
    let mut v___x_2325_: u8 = 0;
    v___x_2325_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_2320_, v_ys_2321_, v_x_2323_);
    return v___x_2325_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(
    mut v_xs_2326_: *mut LeanObject,
    mut v_ys_2327_: *mut LeanObject,
    mut v_hsz_2328_: *mut LeanObject,
    mut v_x_2329_: *mut LeanObject,
    mut v_x_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2331_: u8 = 0;
    let mut v_r_2332_: *mut LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_2326_, v_ys_2327_, v_hsz_2328_, v_x_2329_, v_x_2330_);
    lean_dec_ref(v_ys_2327_);
    lean_dec_ref(v_xs_2326_);
    v_r_2332_ = lean_box((v_res_2331_) as usize);
    return v_r_2332_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(
    mut v_00_u03b2_2333_: *mut LeanObject,
    mut v_i_2334_: *mut LeanObject,
    mut v_source_2335_: *mut LeanObject,
    mut v_target_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v___x_2337_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_2334_, v_source_2335_, v_target_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(
    mut v_00_u03b2_2338_: *mut LeanObject,
    mut v_x_2339_: *mut LeanObject,
    mut v_x_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    v___x_2341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_2339_, v_x_2340_);
    return v___x_2341_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(
    mut v_snd_2342_: *mut LeanObject,
    mut v_x_2343_: *mut LeanObject,
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
    mut v_snd_2347_: *mut LeanObject,
    mut v_x_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2349_: u8 = 0;
    let mut v_r_2350_: *mut LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_2347_, v_x_2348_);
    lean_dec(v_x_2348_);
    lean_dec(v_snd_2347_);
    v_r_2350_ = lean_box((v_res_2349_) as usize);
    return v_r_2350_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2351_) == 0 {
                    v___x_2353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2353_, 0, v_a_2352_);
                    return v___x_2353_;
                } else {
                    v_key_2354_ = lean_ctor_get(v_a_2351_, 0);
                    lean_inc(v_key_2354_);
                    v_tail_2355_ = lean_ctor_get(v_a_2351_, 2);
                    lean_inc(v_tail_2355_);
                    lean_dec_ref_known(v_a_2351_, 3);
                    v_fst_2356_ = lean_ctor_get(v_key_2354_, 0);
                    lean_inc(v_fst_2356_);
                    lean_dec(v_key_2354_);
                    v_fst_2357_ = lean_ctor_get(v_a_2352_, 0);
                    v_snd_2358_ = lean_ctor_get(v_a_2352_, 1);
                    v_isSharedCheck_2378_ = (!lean_is_exclusive(v_a_2352_)) as u8;
                    if v_isSharedCheck_2378_ == 0 {
                        v___x_2360_ = v_a_2352_;
                        v_isShared_2361_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2358_);
                        lean_inc(v_fst_2357_);
                        lean_dec(v_a_2352_);
                        v___x_2360_ = lean_box(0);
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
                            lean_ctor_set(v___x_2360_, 0, v___x_2364_);
                            v___x_2366_ = v___x_2360_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2364_);
                            lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_snd_2358_);
                            v___x_2366_ = v_reuseFailAlloc_2368_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2369_ = l_Lean_NameSet_insert(v_snd_2358_, v_fst_2356_);
                        if v_isShared_2361_ == 0 {
                            lean_ctor_set(v___x_2360_, 1, v___x_2369_);
                            v___x_2371_ = v___x_2360_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_fst_2357_);
                            lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2369_);
                            v___x_2371_ = v_reuseFailAlloc_2373_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_2356_);
                    if v_isShared_2361_ == 0 {
                        v___x_2375_ = v___x_2360_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_fst_2357_);
                        lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_snd_2358_);
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
    mut v_as_2379_: *mut LeanObject,
    mut v_sz_2380_: usize,
    mut v_i_2381_: usize,
    mut v_b_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2383_: u8 = 0;
    let mut v_a_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc(v_a_2384_);
                    v___x_2385_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_2384_, v_b_2382_);
                    if lean_obj_tag(v___x_2385_) == 0 {
                        v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
                        lean_inc(v_a_2386_);
                        lean_dec_ref_known(v___x_2385_, 1);
                        return v_a_2386_;
                    } else {
                        v_a_2387_ = lean_ctor_get(v___x_2385_, 0);
                        lean_inc(v_a_2387_);
                        lean_dec_ref_known(v___x_2385_, 1);
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
    mut v_as_2391_: *mut LeanObject,
    mut v_sz_2392_: *mut LeanObject,
    mut v_i_2393_: *mut LeanObject,
    mut v_b_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2395_: usize = 0;
    let mut v_i_boxed_2396_: usize = 0;
    let mut v_res_2397_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2392_);
    lean_dec(v_sz_2392_);
    v_i_boxed_2396_ = lean_unbox_usize(v_i_2393_);
    lean_dec(v_i_2393_);
    v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_2391_, v_sz_boxed_2395_, v_i_boxed_2396_, v_b_2394_);
    lean_dec_ref(v_as_2391_);
    return v_res_2397_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0() -> *mut LeanObject {
    let mut v_seen_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    v_seen_2398_ = l_Lean_NameSet_empty;
    v___x_2399_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2399_, 0, v_seen_2398_);
    lean_ctor_set(v___x_2399_, 1, v_seen_2398_);
    return v___x_2399_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques(
    mut v_calls_2400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_seen_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2404_: usize = 0;
    let mut v___x_2405_: usize = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    v_seen_2401_ = lean_ctor_get(v_calls_2400_, 1);
    v___x_2402_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once),
        _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0,
    );
    v_buckets_2403_ = lean_ctor_get(v_seen_2401_, 1);
    v_sz_2404_ = lean_array_size(v_buckets_2403_);
    v___x_2405_ = 0usize;
    v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_2403_, v_sz_2404_, v___x_2405_, v___x_2402_);
    v_fst_2407_ = lean_ctor_get(v___x_2406_, 0);
    lean_inc(v_fst_2407_);
    v_snd_2408_ = lean_ctor_get(v___x_2406_, 1);
    lean_inc(v_snd_2408_);
    lean_dec_ref(v___x_2406_);
    v___f_2409_ = lean_alloc_closure(
        l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2409_, 0, v_snd_2408_);
    v___x_2410_ = l_Lean_NameSet_filter(v___f_2409_, v_fst_2407_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(
    mut v_calls_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2412_: *mut LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_2411_);
    lean_dec_ref(v_calls_2411_);
    return v_res_2412_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(
    mut v_e_2413_: *mut LeanObject,
    mut v_funIndInfo_2414_: *mut LeanObject,
    mut v_args_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut v_a_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2423_) == 0 {
                    v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2432_ = (!lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2432_ == 0 {
                        v___x_2426_ = v___x_2423_;
                        v_isShared_2427_ = v_isSharedCheck_2432_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2424_);
                        lean_dec(v___x_2423_);
                        v___x_2426_ = lean_box(0);
                        v_isShared_2427_ = v_isSharedCheck_2432_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2433_ = lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2440_ = (!lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2440_ == 0 {
                        v___x_2435_ = v___x_2423_;
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2433_);
                        lean_dec(v___x_2423_);
                        v___x_2435_ = lean_box(0);
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2428_ = lean_st_ref_set(v_a_2416_, v_a_2424_);
                if v_isShared_2427_ == 0 {
                    lean_ctor_set(v___x_2426_, 0, v___x_2428_);
                    v___x_2430_ = v___x_2426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
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
                    v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
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
    mut v_e_2441_: *mut LeanObject,
    mut v_funIndInfo_2442_: *mut LeanObject,
    mut v_args_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2450_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2448_);
    lean_dec_ref(v_a_2447_);
    lean_dec(v_a_2446_);
    lean_dec_ref(v_a_2445_);
    lean_dec(v_a_2444_);
    lean_dec_ref(v_args_2443_);
    return v_res_2450_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_saveFunInd(
    mut v_e_2451_: *mut LeanObject,
    mut v_funIndInfo_2452_: *mut LeanObject,
    mut v_args_2453_: *mut LeanObject,
    mut v_a_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
    mut v_a_2458_: *mut LeanObject,
    mut v_a_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_2462_: *mut LeanObject,
    mut v_funIndInfo_2463_: *mut LeanObject,
    mut v_args_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
    mut v_a_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2472_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2470_);
    lean_dec_ref(v_a_2469_);
    lean_dec(v_a_2468_);
    lean_dec_ref(v_a_2467_);
    lean_dec(v_a_2466_);
    lean_dec_ref(v_a_2465_);
    lean_dec_ref(v_args_2464_);
    return v_res_2472_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp___redArg(
    mut v_e_2473_: *mut LeanObject,
    mut v_funIndInfo_2474_: *mut LeanObject,
    mut v_args_2475_: *mut LeanObject,
    mut v_a_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
    mut v_a_2478_: *mut LeanObject,
    mut v_a_2479_: *mut LeanObject,
    mut v_a_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_2483_: *mut LeanObject,
    mut v_funIndInfo_2484_: *mut LeanObject,
    mut v_args_2485_: *mut LeanObject,
    mut v_a_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
    mut v_a_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2492_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2490_);
    lean_dec_ref(v_a_2489_);
    lean_dec(v_a_2488_);
    lean_dec_ref(v_a_2487_);
    lean_dec(v_a_2486_);
    lean_dec_ref(v_args_2485_);
    return v_res_2492_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visitApp(
    mut v_e_2493_: *mut LeanObject,
    mut v_funIndInfo_2494_: *mut LeanObject,
    mut v_args_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
    mut v_a_2501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_2504_: *mut LeanObject,
    mut v_funIndInfo_2505_: *mut LeanObject,
    mut v_args_2506_: *mut LeanObject,
    mut v_a_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2514_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2512_);
    lean_dec_ref(v_a_2511_);
    lean_dec(v_a_2510_);
    lean_dec_ref(v_a_2509_);
    lean_dec(v_a_2508_);
    lean_dec_ref(v_a_2507_);
    lean_dec_ref(v_args_2506_);
    return v_res_2514_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_2515_: *mut LeanObject,
    mut v_x_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2516_) == 0 {
                    return v_x_2515_;
                } else {
                    v_key_2517_ = lean_ctor_get(v_x_2516_, 0);
                    v_value_2518_ = lean_ctor_get(v_x_2516_, 1);
                    v_tail_2519_ = lean_ctor_get(v_x_2516_, 2);
                    v_isSharedCheck_2545_ = (!lean_is_exclusive(v_x_2516_)) as u8;
                    if v_isSharedCheck_2545_ == 0 {
                        v___x_2521_ = v_x_2516_;
                        v_isShared_2522_ = v_isSharedCheck_2545_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2519_);
                        lean_inc(v_value_2518_);
                        lean_inc(v_key_2517_);
                        lean_dec(v_x_2516_);
                        v___x_2521_ = lean_box(0);
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
                lean_inc(v___x_2539_);
                if v_isShared_2522_ == 0 {
                    lean_ctor_set(v___x_2521_, 2, v___x_2539_);
                    v___x_2541_ = v___x_2521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_key_2517_);
                    lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_value_2518_);
                    lean_ctor_set(v_reuseFailAlloc_2544_, 2, v___x_2539_);
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
    mut v_i_2546_: *mut LeanObject,
    mut v_source_2547_: *mut LeanObject,
    mut v_target_2548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u8 = 0;
    let mut v_es_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2549_ = lean_array_get_size(v_source_2547_);
                v___x_2550_ = lean_nat_dec_lt(v_i_2546_, v___x_2549_);
                if v___x_2550_ == 0 {
                    lean_dec_ref(v_source_2547_);
                    lean_dec(v_i_2546_);
                    return v_target_2548_;
                } else {
                    v_es_2551_ = lean_array_fget(v_source_2547_, v_i_2546_);
                    v___x_2552_ = lean_box(0);
                    v_source_2553_ = lean_array_fset(v_source_2547_, v_i_2546_, v___x_2552_);
                    v_target_2554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_2548_, v_es_2551_);
                    v___x_2555_ = lean_unsigned_to_nat(1);
                    v___x_2556_ = lean_nat_add(v_i_2546_, v___x_2555_);
                    lean_dec(v_i_2546_);
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
    mut v_data_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    v___x_2559_ = lean_array_get_size(v_data_2558_);
    v___x_2560_ = lean_unsigned_to_nat(2);
    v_nbuckets_2561_ = lean_nat_mul(v___x_2559_, v___x_2560_);
    v___x_2562_ = lean_unsigned_to_nat(0);
    v___x_2563_ = lean_box(0);
    v___x_2564_ = lean_mk_array(v_nbuckets_2561_, v___x_2563_);
    v___x_2565_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_2562_, v_data_2558_, v___x_2564_);
    return v___x_2565_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(
    mut v_a_2566_: *mut LeanObject,
    mut v_x_2567_: *mut LeanObject,
) -> u8 {
    let mut v___x_2568_: u8 = 0;
    let mut v_key_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2567_) == 0 {
                    v___x_2568_ = 0;
                    return v___x_2568_;
                } else {
                    v_key_2569_ = lean_ctor_get(v_x_2567_, 0);
                    v_tail_2570_ = lean_ctor_get(v_x_2567_, 2);
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
    mut v_a_2575_: *mut LeanObject,
    mut v_x_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2577_: u8 = 0;
    let mut v_r_2578_: *mut LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2575_, v_x_2576_);
    lean_dec(v_x_2576_);
    lean_dec_ref(v_a_2575_);
    v_r_2578_ = lean_box((v_res_2577_) as usize);
    return v_r_2578_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(
    mut v_m_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_b_2581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v_val_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2622_: u8 = 0;
    let mut v_unused_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2582_ = lean_ctor_get(v_m_2579_, 0);
                v_buckets_2583_ = lean_ctor_get(v_m_2579_, 1);
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
                    lean_inc_ref(v_buckets_2583_);
                    lean_inc(v_size_2582_);
                    v_isSharedCheck_2622_ = (!lean_is_exclusive(v_m_2579_)) as u8;
                    if v_isSharedCheck_2622_ == 0 {
                        v_unused_2623_ = lean_ctor_get(v_m_2579_, 1);
                        lean_dec(v_unused_2623_);
                        v_unused_2624_ = lean_ctor_get(v_m_2579_, 0);
                        lean_dec(v_unused_2624_);
                        v___x_2603_ = v_m_2579_;
                        v_isShared_2604_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2579_);
                        v___x_2603_ = lean_box(0);
                        v_isShared_2604_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2581_);
                    lean_dec_ref(v_a_2580_);
                    return v_m_2579_;
                }
            }
            1 => {
                v___x_2605_ = lean_unsigned_to_nat(1);
                v_size_x27_2606_ = lean_nat_add(v_size_2582_, v___x_2605_);
                lean_dec(v_size_2582_);
                lean_inc(v_bkt_2600_);
                v___x_2607_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2607_, 0, v_a_2580_);
                lean_ctor_set(v___x_2607_, 1, v_b_2581_);
                lean_ctor_set(v___x_2607_, 2, v_bkt_2600_);
                v_buckets_x27_2608_ = lean_array_uset(v_buckets_2583_, v___x_2599_, v___x_2607_);
                v___x_2609_ = lean_unsigned_to_nat(4);
                v___x_2610_ = lean_nat_mul(v_size_x27_2606_, v___x_2609_);
                v___x_2611_ = lean_unsigned_to_nat(3);
                v___x_2612_ = lean_nat_div(v___x_2610_, v___x_2611_);
                lean_dec(v___x_2610_);
                v___x_2613_ = lean_array_get_size(v_buckets_x27_2608_);
                v___x_2614_ = lean_nat_dec_le(v___x_2612_, v___x_2613_);
                lean_dec(v___x_2612_);
                if v___x_2614_ == 0 {
                    v_val_2615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_2608_);
                    if v_isShared_2604_ == 0 {
                        lean_ctor_set(v___x_2603_, 1, v_val_2615_);
                        lean_ctor_set(v___x_2603_, 0, v_size_x27_2606_);
                        v___x_2617_ = v___x_2603_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_size_x27_2606_);
                        lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_val_2615_);
                        v___x_2617_ = v_reuseFailAlloc_2618_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2604_ == 0 {
                        lean_ctor_set(v___x_2603_, 1, v_buckets_x27_2608_);
                        lean_ctor_set(v___x_2603_, 0, v_size_x27_2606_);
                        v___x_2620_ = v___x_2603_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_size_x27_2606_);
                        lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_buckets_x27_2608_);
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
    mut v_m_2625_: *mut LeanObject,
    mut v_a_2626_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    v_buckets_2627_ = lean_ctor_get(v_m_2625_, 1);
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
    mut v_m_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2648_: u8 = 0;
    let mut v_r_2649_: *mut LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_2646_, v_a_2647_);
    lean_dec_ref(v_a_2647_);
    lean_dec_ref(v_m_2646_);
    v_r_2649_ = lean_box((v_res_2648_) as usize);
    return v_r_2649_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_Collector_visit___closed__0() -> *mut LeanObject {
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2651_: *mut LeanObject = core::ptr::null_mut();
    v___x_2650_ = lean_box(0);
    v_dummy_2651_ = l_Lean_Expr_sort___override(v___x_2650_);
    return v_dummy_2651_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(
    mut v_e_2652_: *mut LeanObject,
    mut v_x_2653_: *mut LeanObject,
    mut v_x_2654_: *mut LeanObject,
    mut v_x_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
    mut v___y_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: u8 = 0;
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: usize = 0;
    let mut v___x_2680_: usize = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: usize = 0;
    let mut v___x_2683_: usize = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funName_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u8 = 0;
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2653_) == 5 {
                    v_fn_2685_ = lean_ctor_get(v_x_2653_, 0);
                    lean_inc_ref(v_fn_2685_);
                    v_arg_2686_ = lean_ctor_get(v_x_2653_, 1);
                    lean_inc_ref(v_arg_2686_);
                    lean_dec_ref_known(v_x_2653_, 2);
                    v___x_2687_ = lean_array_set(v_x_2654_, v_x_2655_, v_arg_2686_);
                    v___x_2688_ = lean_unsigned_to_nat(1);
                    v___x_2689_ = lean_nat_sub(v_x_2655_, v___x_2688_);
                    lean_dec(v_x_2655_);
                    v_x_2653_ = v_fn_2685_;
                    v_x_2654_ = v___x_2687_;
                    v_x_2655_ = v___x_2689_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_2655_);
                    if lean_obj_tag(v_x_2653_) == 4 {
                        v_declName_2691_ = lean_ctor_get(v_x_2653_, 0);
                        lean_inc(v_declName_2691_);
                        lean_dec_ref_known(v_x_2653_, 2);
                        v_funName_2692_ = lean_ctor_get(v___y_2657_, 0);
                        v___x_2693_ = lean_name_eq(v_declName_2691_, v_funName_2692_);
                        lean_dec(v_declName_2691_);
                        if v___x_2693_ == 0 {
                            lean_dec_ref(v_e_2652_);
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
                                lean_inc_ref(v___y_2657_);
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
                                if lean_obj_tag(v___x_2695_) == 0 {
                                    lean_dec_ref_known(v___x_2695_, 1);
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
                                    lean_dec_ref(v_x_2654_);
                                    return v___x_2695_;
                                }
                            } else {
                                lean_dec_ref(v_e_2652_);
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
                        lean_dec_ref(v_e_2652_);
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
                        if lean_obj_tag(v___x_2696_) == 0 {
                            lean_dec_ref_known(v___x_2696_, 1);
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
                            lean_dec_ref(v_x_2654_);
                            return v___x_2696_;
                        }
                    }
                }
            }
            1 => {
                v___x_2672_ = lean_unsigned_to_nat(0);
                v___x_2673_ = lean_array_get_size(v_x_2654_);
                v___x_2674_ = lean_box(0);
                v___x_2675_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
                if v___x_2675_ == 0 {
                    lean_dec_ref(v_x_2654_);
                    v___x_2676_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2676_, 0, v___x_2674_);
                    return v___x_2676_;
                } else {
                    v___x_2677_ = lean_nat_dec_le(v___x_2673_, v___x_2673_);
                    if v___x_2677_ == 0 {
                        if v___x_2675_ == 0 {
                            lean_dec_ref(v_x_2654_);
                            v___x_2678_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2678_, 0, v___x_2674_);
                            return v___x_2678_;
                        } else {
                            v___x_2679_ = 0usize;
                            v___x_2680_ = lean_usize_of_nat(v___x_2673_);
                            v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_2654_, v___x_2679_, v___x_2680_, v___x_2674_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
                            lean_dec_ref(v_x_2654_);
                            return v___x_2681_;
                        }
                    } else {
                        v___x_2682_ = 0usize;
                        v___x_2683_ = lean_usize_of_nat(v___x_2673_);
                        v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_2654_, v___x_2682_, v___x_2683_, v___x_2674_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
                        lean_dec_ref(v_x_2654_);
                        return v___x_2684_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visit(
    mut v_e_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
    mut v_a_2700_: *mut LeanObject,
    mut v_a_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
    mut v_a_2703_: *mut LeanObject,
    mut v_a_2704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2706_ = lean_st_ref_get(v_a_2698_);
                v___x_2707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_2706_, v_e_2697_);
                lean_dec(v___x_2706_);
                if v___x_2707_ == 0 {
                    v___x_2708_ = lean_st_ref_take(v_a_2698_);
                    v___x_2709_ = lean_box(0);
                    lean_inc_ref(v_e_2697_);
                    v___x_2710_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_2708_, v_e_2697_, v___x_2709_);
                    v___x_2711_ = lean_st_ref_set(v_a_2698_, v___x_2710_);
                    match lean_obj_tag(v_e_2697_) {
                        4 => {
                            lean_dec_ref_known(v_e_2697_, 2);
                            v___x_2724_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2724_, 0, v___x_2709_);
                            return v___x_2724_;
                        }
                        7 => {
                            v_binderType_2725_ = lean_ctor_get(v_e_2697_, 1);
                            lean_inc_ref(v_binderType_2725_);
                            v_body_2726_ = lean_ctor_get(v_e_2697_, 2);
                            lean_inc_ref(v_body_2726_);
                            lean_dec_ref_known(v_e_2697_, 3);
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
                            v_binderType_2727_ = lean_ctor_get(v_e_2697_, 1);
                            lean_inc_ref(v_binderType_2727_);
                            v_body_2728_ = lean_ctor_get(v_e_2697_, 2);
                            lean_inc_ref(v_body_2728_);
                            lean_dec_ref_known(v_e_2697_, 3);
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
                            v_expr_2729_ = lean_ctor_get(v_e_2697_, 1);
                            lean_inc_ref(v_expr_2729_);
                            lean_dec_ref_known(v_e_2697_, 2);
                            v_e_2697_ = v_expr_2729_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_2731_ = lean_ctor_get(v_e_2697_, 1);
                            lean_inc_ref(v_type_2731_);
                            v_value_2732_ = lean_ctor_get(v_e_2697_, 2);
                            lean_inc_ref(v_value_2732_);
                            v_body_2733_ = lean_ctor_get(v_e_2697_, 3);
                            lean_inc_ref(v_body_2733_);
                            lean_dec_ref_known(v_e_2697_, 4);
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
                            if lean_obj_tag(v___x_2734_) == 0 {
                                lean_dec_ref_known(v___x_2734_, 1);
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
                                if lean_obj_tag(v___x_2735_) == 0 {
                                    lean_dec_ref_known(v___x_2735_, 1);
                                    v_e_2697_ = v_body_2733_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_body_2733_);
                                    return v___x_2735_;
                                }
                            } else {
                                lean_dec_ref(v_body_2733_);
                                lean_dec_ref(v_value_2732_);
                                return v___x_2734_;
                            }
                        }
                        5 => {
                            v_dummy_2737_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_FunInd_Collector_visit___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_FunInd_Collector_visit___closed__0_once
                                ),
                                _init_l_Lean_Meta_FunInd_Collector_visit___closed__0,
                            );
                            v_nargs_2738_ = l_Lean_Expr_getAppNumArgs(v_e_2697_);
                            lean_inc(v_nargs_2738_);
                            v___x_2739_ = lean_mk_array(v_nargs_2738_, v_dummy_2737_);
                            v___x_2740_ = lean_unsigned_to_nat(1);
                            v___x_2741_ = lean_nat_sub(v_nargs_2738_, v___x_2740_);
                            lean_dec(v_nargs_2738_);
                            lean_inc_ref(v_e_2697_);
                            v___x_2742_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_2697_, v_e_2697_, v___x_2739_, v___x_2741_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
                            return v___x_2742_;
                        }
                        11 => {
                            v_struct_2743_ = lean_ctor_get(v_e_2697_, 2);
                            lean_inc_ref(v_struct_2743_);
                            lean_dec_ref_known(v_e_2697_, 3);
                            v_e_2697_ = v_struct_2743_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_e_2697_);
                            v___x_2745_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2745_, 0, v___x_2709_);
                            return v___x_2745_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_2697_);
                    v___x_2746_ = lean_box(0);
                    v___x_2747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2747_, 0, v___x_2746_);
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
                if lean_obj_tag(v___x_2722_) == 0 {
                    lean_dec_ref_known(v___x_2722_, 1);
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
                    lean_dec_ref(v_b_2714_);
                    return v___x_2722_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(
    mut v_as_2748_: *mut LeanObject,
    mut v_i_2749_: usize,
    mut v_stop_2750_: usize,
    mut v_b_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2760_ = lean_usize_dec_eq(v_i_2749_, v_stop_2750_);
                if v___x_2760_ == 0 {
                    v___x_2761_ = lean_array_uget_borrowed(v_as_2748_, v_i_2749_);
                    lean_inc(v___x_2761_);
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
                    if lean_obj_tag(v___x_2762_) == 0 {
                        v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
                        lean_inc(v_a_2763_);
                        lean_dec_ref_known(v___x_2762_, 1);
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
                    v___x_2767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2767_, 0, v_b_2751_);
                    return v___x_2767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(
    mut v_as_2768_: *mut LeanObject,
    mut v_i_2769_: *mut LeanObject,
    mut v_stop_2770_: *mut LeanObject,
    mut v_b_2771_: *mut LeanObject,
    mut v___y_2772_: *mut LeanObject,
    mut v___y_2773_: *mut LeanObject,
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2780_: usize = 0;
    let mut v_stop_boxed_2781_: usize = 0;
    let mut v_res_2782_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2780_ = lean_unbox_usize(v_i_2769_);
    lean_dec(v_i_2769_);
    v_stop_boxed_2781_ = lean_unbox_usize(v_stop_2770_);
    lean_dec(v_stop_2770_);
    v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_2768_, v_i_boxed_2780_, v_stop_boxed_2781_, v_b_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
    lean_dec(v___y_2778_);
    lean_dec_ref(v___y_2777_);
    lean_dec(v___y_2776_);
    lean_dec_ref(v___y_2775_);
    lean_dec(v___y_2774_);
    lean_dec_ref(v___y_2773_);
    lean_dec(v___y_2772_);
    lean_dec_ref(v_as_2768_);
    return v_res_2782_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_visit___boxed(
    mut v_e_2783_: *mut LeanObject,
    mut v_a_2784_: *mut LeanObject,
    mut v_a_2785_: *mut LeanObject,
    mut v_a_2786_: *mut LeanObject,
    mut v_a_2787_: *mut LeanObject,
    mut v_a_2788_: *mut LeanObject,
    mut v_a_2789_: *mut LeanObject,
    mut v_a_2790_: *mut LeanObject,
    mut v_a_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2792_: *mut LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_Meta_FunInd_Collector_visit(
        v_e_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_,
    );
    lean_dec(v_a_2790_);
    lean_dec_ref(v_a_2789_);
    lean_dec(v_a_2788_);
    lean_dec_ref(v_a_2787_);
    lean_dec(v_a_2786_);
    lean_dec_ref(v_a_2785_);
    lean_dec(v_a_2784_);
    return v_res_2792_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(
    mut v_e_2793_: *mut LeanObject,
    mut v_x_2794_: *mut LeanObject,
    mut v_x_2795_: *mut LeanObject,
    mut v_x_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
    mut v___y_2799_: *mut LeanObject,
    mut v___y_2800_: *mut LeanObject,
    mut v___y_2801_: *mut LeanObject,
    mut v___y_2802_: *mut LeanObject,
    mut v___y_2803_: *mut LeanObject,
    mut v___y_2804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2805_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2803_);
    lean_dec_ref(v___y_2802_);
    lean_dec(v___y_2801_);
    lean_dec_ref(v___y_2800_);
    lean_dec(v___y_2799_);
    lean_dec_ref(v___y_2798_);
    lean_dec(v___y_2797_);
    return v_res_2805_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(
    mut v_00_u03b2_2806_: *mut LeanObject,
    mut v_m_2807_: *mut LeanObject,
    mut v_a_2808_: *mut LeanObject,
) -> u8 {
    let mut v___x_2809_: u8 = 0;
    v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_2807_, v_a_2808_);
    return v___x_2809_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(
    mut v_00_u03b2_2810_: *mut LeanObject,
    mut v_m_2811_: *mut LeanObject,
    mut v_a_2812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2813_: u8 = 0;
    let mut v_r_2814_: *mut LeanObject = core::ptr::null_mut();
    v_res_2813_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_2810_, v_m_2811_, v_a_2812_);
    lean_dec_ref(v_a_2812_);
    lean_dec_ref(v_m_2811_);
    v_r_2814_ = lean_box((v_res_2813_) as usize);
    return v_r_2814_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(
    mut v_00_u03b2_2815_: *mut LeanObject,
    mut v_m_2816_: *mut LeanObject,
    mut v_a_2817_: *mut LeanObject,
    mut v_b_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_2816_, v_a_2817_, v_b_2818_);
    return v___x_2819_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(
    mut v_00_u03b2_2820_: *mut LeanObject,
    mut v_a_2821_: *mut LeanObject,
    mut v_x_2822_: *mut LeanObject,
) -> u8 {
    let mut v___x_2823_: u8 = 0;
    v___x_2823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_2821_, v_x_2822_);
    return v___x_2823_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(
    mut v_00_u03b2_2824_: *mut LeanObject,
    mut v_a_2825_: *mut LeanObject,
    mut v_x_2826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2827_: u8 = 0;
    let mut v_r_2828_: *mut LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_2824_, v_a_2825_, v_x_2826_);
    lean_dec(v_x_2826_);
    lean_dec_ref(v_a_2825_);
    v_r_2828_ = lean_box((v_res_2827_) as usize);
    return v_r_2828_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(
    mut v_00_u03b2_2829_: *mut LeanObject,
    mut v_data_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_2830_);
    return v___x_2831_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2832_: *mut LeanObject,
    mut v_i_2833_: *mut LeanObject,
    mut v_source_2834_: *mut LeanObject,
    mut v_target_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    v___x_2836_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_2833_, v_source_2834_, v_target_2835_);
    return v___x_2836_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_2837_: *mut LeanObject,
    mut v_x_2838_: *mut LeanObject,
    mut v_x_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    v___x_2840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_2838_, v_x_2839_);
    return v___x_2840_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(
    mut v_e_2841_: *mut LeanObject,
    mut v___y_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2864_: u8 = 0;
    let mut v_unused_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2844_ = l_Lean_Expr_hasMVar(v_e_2841_);
                if v___x_2844_ == 0 {
                    v___x_2845_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2845_, 0, v_e_2841_);
                    return v___x_2845_;
                } else {
                    v___x_2846_ = lean_st_ref_get(v___y_2842_);
                    v_mctx_2847_ = lean_ctor_get(v___x_2846_, 0);
                    lean_inc_ref(v_mctx_2847_);
                    lean_dec(v___x_2846_);
                    v___x_2848_ = l_Lean_instantiateMVarsCore(v_mctx_2847_, v_e_2841_);
                    v_fst_2849_ = lean_ctor_get(v___x_2848_, 0);
                    lean_inc(v_fst_2849_);
                    v_snd_2850_ = lean_ctor_get(v___x_2848_, 1);
                    lean_inc(v_snd_2850_);
                    lean_dec_ref(v___x_2848_);
                    v___x_2851_ = lean_st_ref_take(v___y_2842_);
                    v_cache_2852_ = lean_ctor_get(v___x_2851_, 1);
                    v_zetaDeltaFVarIds_2853_ = lean_ctor_get(v___x_2851_, 2);
                    v_postponed_2854_ = lean_ctor_get(v___x_2851_, 3);
                    v_diag_2855_ = lean_ctor_get(v___x_2851_, 4);
                    v_isSharedCheck_2864_ = (!lean_is_exclusive(v___x_2851_)) as u8;
                    if v_isSharedCheck_2864_ == 0 {
                        v_unused_2865_ = lean_ctor_get(v___x_2851_, 0);
                        lean_dec(v_unused_2865_);
                        v___x_2857_ = v___x_2851_;
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2855_);
                        lean_inc(v_postponed_2854_);
                        lean_inc(v_zetaDeltaFVarIds_2853_);
                        lean_inc(v_cache_2852_);
                        lean_dec(v___x_2851_);
                        v___x_2857_ = lean_box(0);
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2858_ == 0 {
                    lean_ctor_set(v___x_2857_, 0, v_snd_2850_);
                    v___x_2860_ = v___x_2857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_snd_2850_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_cache_2852_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_zetaDeltaFVarIds_2853_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_postponed_2854_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_diag_2855_);
                    v___x_2860_ = v_reuseFailAlloc_2863_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2861_ = lean_st_ref_set(v___y_2842_, v___x_2860_);
                v___x_2862_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2862_, 0, v_fst_2849_);
                return v___x_2862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(
    mut v_e_2866_: *mut LeanObject,
    mut v___y_2867_: *mut LeanObject,
    mut v___y_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2869_: *mut LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_2866_, v___y_2867_);
    lean_dec(v___y_2867_);
    return v_res_2869_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(
    mut v_e_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
    mut v___y_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    v___x_2879_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_2870_, v___y_2875_);
    return v___x_2879_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(
    mut v_e_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
    mut v___y_2882_: *mut LeanObject,
    mut v___y_2883_: *mut LeanObject,
    mut v___y_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
    mut v___y_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
    mut v___y_2888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2889_: *mut LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    lean_dec(v___y_2887_);
    lean_dec_ref(v___y_2886_);
    lean_dec(v___y_2885_);
    lean_dec_ref(v___y_2884_);
    lean_dec(v___y_2883_);
    lean_dec_ref(v___y_2882_);
    lean_dec(v___y_2881_);
    return v_res_2889_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(
    mut v_as_2890_: *mut LeanObject,
    mut v_sz_2891_: usize,
    mut v_i_2892_: usize,
    mut v_b_2893_: *mut LeanObject,
    mut v___y_2894_: *mut LeanObject,
    mut v___y_2895_: *mut LeanObject,
    mut v___y_2896_: *mut LeanObject,
    mut v___y_2897_: *mut LeanObject,
    mut v___y_2898_: *mut LeanObject,
    mut v___y_2899_: *mut LeanObject,
    mut v___y_2900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: usize = 0;
    let mut v___x_2914_: usize = 0;
    let mut v_reuseFailAlloc_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_a_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2953_: u8 = 0;
    let mut v_a_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_unused_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2902_ = lean_usize_dec_lt(v_i_2892_, v_sz_2891_);
                if v___x_2902_ == 0 {
                    v___x_2903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2903_, 0, v_b_2893_);
                    return v___x_2903_;
                } else {
                    v_snd_2904_ = lean_ctor_get(v_b_2893_, 1);
                    v_isSharedCheck_2962_ = (!lean_is_exclusive(v_b_2893_)) as u8;
                    if v_isSharedCheck_2962_ == 0 {
                        v_unused_2963_ = lean_ctor_get(v_b_2893_, 0);
                        lean_dec(v_unused_2963_);
                        v___x_2906_ = v_b_2893_;
                        v_isShared_2907_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2904_);
                        lean_dec(v_b_2893_);
                        v___x_2906_ = lean_box(0);
                        v_isShared_2907_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2908_ = lean_box(0);
                v_a_2917_ = lean_array_uget_borrowed(v_as_2890_, v_i_2892_);
                if lean_obj_tag(v_a_2917_) == 0 {
                    v_a_2910_ = v_snd_2904_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_2904_);
                    v_val_2918_ = lean_ctor_get(v_a_2917_, 0);
                    v___x_2919_ = lean_box(0);
                    v___x_2920_ = l_Lean_LocalDecl_isAuxDecl(v_val_2918_);
                    if v___x_2920_ == 0 {
                        v___x_2921_ = l_Lean_LocalDecl_value_x3f(v_val_2918_, v___x_2920_);
                        if lean_obj_tag(v___x_2921_) == 1 {
                            v_val_2922_ = lean_ctor_get(v___x_2921_, 0);
                            lean_inc(v_val_2922_);
                            lean_dec_ref_known(v___x_2921_, 1);
                            v___x_2923_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_2922_, v___y_2898_);
                            if lean_obj_tag(v___x_2923_) == 0 {
                                v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
                                lean_inc(v_a_2924_);
                                lean_dec_ref_known(v___x_2923_, 1);
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
                                if lean_obj_tag(v___x_2925_) == 0 {
                                    lean_dec_ref_known(v___x_2925_, 1);
                                    v_a_2910_ = v___x_2919_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_2906_);
                                    v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
                                    v_isSharedCheck_2933_ = (!lean_is_exclusive(v___x_2925_)) as u8;
                                    if v_isSharedCheck_2933_ == 0 {
                                        v___x_2928_ = v___x_2925_;
                                        v_isShared_2929_ = v_isSharedCheck_2933_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2926_);
                                        lean_dec(v___x_2925_);
                                        v___x_2928_ = lean_box(0);
                                        v_isShared_2929_ = v_isSharedCheck_2933_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_2906_);
                                v_a_2934_ = lean_ctor_get(v___x_2923_, 0);
                                v_isSharedCheck_2941_ = (!lean_is_exclusive(v___x_2923_)) as u8;
                                if v_isSharedCheck_2941_ == 0 {
                                    v___x_2936_ = v___x_2923_;
                                    v_isShared_2937_ = v_isSharedCheck_2941_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_2934_);
                                    lean_dec(v___x_2923_);
                                    v___x_2936_ = lean_box(0);
                                    v_isShared_2937_ = v_isSharedCheck_2941_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2921_);
                            v___x_2942_ = l_Lean_LocalDecl_type(v_val_2918_);
                            v___x_2943_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_2942_, v___y_2898_);
                            if lean_obj_tag(v___x_2943_) == 0 {
                                v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
                                lean_inc(v_a_2944_);
                                lean_dec_ref_known(v___x_2943_, 1);
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
                                if lean_obj_tag(v___x_2945_) == 0 {
                                    lean_dec_ref_known(v___x_2945_, 1);
                                    v_a_2910_ = v___x_2919_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_2906_);
                                    v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
                                    v_isSharedCheck_2953_ = (!lean_is_exclusive(v___x_2945_)) as u8;
                                    if v_isSharedCheck_2953_ == 0 {
                                        v___x_2948_ = v___x_2945_;
                                        v_isShared_2949_ = v_isSharedCheck_2953_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2946_);
                                        lean_dec(v___x_2945_);
                                        v___x_2948_ = lean_box(0);
                                        v_isShared_2949_ = v_isSharedCheck_2953_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_2906_);
                                v_a_2954_ = lean_ctor_get(v___x_2943_, 0);
                                v_isSharedCheck_2961_ = (!lean_is_exclusive(v___x_2943_)) as u8;
                                if v_isSharedCheck_2961_ == 0 {
                                    v___x_2956_ = v___x_2943_;
                                    v_isShared_2957_ = v_isSharedCheck_2961_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_2954_);
                                    lean_dec(v___x_2943_);
                                    v___x_2956_ = lean_box(0);
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
                    lean_ctor_set(v___x_2906_, 1, v_a_2910_);
                    lean_ctor_set(v___x_2906_, 0, v___x_2908_);
                    v___x_2912_ = v___x_2906_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2908_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_a_2910_);
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
                    v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
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
                    v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
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
                    v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
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
                    v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
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
    mut v_as_2964_: *mut LeanObject,
    mut v_sz_2965_: *mut LeanObject,
    mut v_i_2966_: *mut LeanObject,
    mut v_b_2967_: *mut LeanObject,
    mut v___y_2968_: *mut LeanObject,
    mut v___y_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2976_: usize = 0;
    let mut v_i_boxed_2977_: usize = 0;
    let mut v_res_2978_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2976_ = lean_unbox_usize(v_sz_2965_);
    lean_dec(v_sz_2965_);
    v_i_boxed_2977_ = lean_unbox_usize(v_i_2966_);
    lean_dec(v_i_2966_);
    v_res_2978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_2964_, v_sz_boxed_2976_, v_i_boxed_2977_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
    lean_dec(v___y_2974_);
    lean_dec_ref(v___y_2973_);
    lean_dec(v___y_2972_);
    lean_dec_ref(v___y_2971_);
    lean_dec(v___y_2970_);
    lean_dec_ref(v___y_2969_);
    lean_dec(v___y_2968_);
    lean_dec_ref(v_as_2964_);
    return v_res_2978_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(
    mut v_as_2979_: *mut LeanObject,
    mut v_sz_2980_: usize,
    mut v_i_2981_: usize,
    mut v_b_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: usize = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_a_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v_a_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_unused_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_usize_dec_lt(v_i_2981_, v_sz_2980_);
                if v___x_2991_ == 0 {
                    v___x_2992_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2992_, 0, v_b_2982_);
                    return v___x_2992_;
                } else {
                    v_snd_2993_ = lean_ctor_get(v_b_2982_, 1);
                    v_isSharedCheck_3051_ = (!lean_is_exclusive(v_b_2982_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v_unused_3052_ = lean_ctor_get(v_b_2982_, 0);
                        lean_dec(v_unused_3052_);
                        v___x_2995_ = v_b_2982_;
                        v_isShared_2996_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2993_);
                        lean_dec(v_b_2982_);
                        v___x_2995_ = lean_box(0);
                        v_isShared_2996_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2997_ = lean_box(0);
                v_a_3006_ = lean_array_uget_borrowed(v_as_2979_, v_i_2981_);
                if lean_obj_tag(v_a_3006_) == 0 {
                    v_a_2999_ = v_snd_2993_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_2993_);
                    v_val_3007_ = lean_ctor_get(v_a_3006_, 0);
                    v___x_3008_ = lean_box(0);
                    v___x_3009_ = l_Lean_LocalDecl_isAuxDecl(v_val_3007_);
                    if v___x_3009_ == 0 {
                        v___x_3010_ = l_Lean_LocalDecl_value_x3f(v_val_3007_, v___x_3009_);
                        if lean_obj_tag(v___x_3010_) == 1 {
                            v_val_3011_ = lean_ctor_get(v___x_3010_, 0);
                            lean_inc(v_val_3011_);
                            lean_dec_ref_known(v___x_3010_, 1);
                            v___x_3012_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3011_, v___y_2987_);
                            if lean_obj_tag(v___x_3012_) == 0 {
                                v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
                                lean_inc(v_a_3013_);
                                lean_dec_ref_known(v___x_3012_, 1);
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
                                if lean_obj_tag(v___x_3014_) == 0 {
                                    lean_dec_ref_known(v___x_3014_, 1);
                                    v_a_2999_ = v___x_3008_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_2995_);
                                    v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
                                    v_isSharedCheck_3022_ = (!lean_is_exclusive(v___x_3014_)) as u8;
                                    if v_isSharedCheck_3022_ == 0 {
                                        v___x_3017_ = v___x_3014_;
                                        v_isShared_3018_ = v_isSharedCheck_3022_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3015_);
                                        lean_dec(v___x_3014_);
                                        v___x_3017_ = lean_box(0);
                                        v_isShared_3018_ = v_isSharedCheck_3022_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_2995_);
                                v_a_3023_ = lean_ctor_get(v___x_3012_, 0);
                                v_isSharedCheck_3030_ = (!lean_is_exclusive(v___x_3012_)) as u8;
                                if v_isSharedCheck_3030_ == 0 {
                                    v___x_3025_ = v___x_3012_;
                                    v_isShared_3026_ = v_isSharedCheck_3030_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_3023_);
                                    lean_dec(v___x_3012_);
                                    v___x_3025_ = lean_box(0);
                                    v_isShared_3026_ = v_isSharedCheck_3030_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_3010_);
                            v___x_3031_ = l_Lean_LocalDecl_type(v_val_3007_);
                            v___x_3032_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3031_, v___y_2987_);
                            if lean_obj_tag(v___x_3032_) == 0 {
                                v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
                                lean_inc(v_a_3033_);
                                lean_dec_ref_known(v___x_3032_, 1);
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
                                if lean_obj_tag(v___x_3034_) == 0 {
                                    lean_dec_ref_known(v___x_3034_, 1);
                                    v_a_2999_ = v___x_3008_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_2995_);
                                    v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
                                    v_isSharedCheck_3042_ = (!lean_is_exclusive(v___x_3034_)) as u8;
                                    if v_isSharedCheck_3042_ == 0 {
                                        v___x_3037_ = v___x_3034_;
                                        v_isShared_3038_ = v_isSharedCheck_3042_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3035_);
                                        lean_dec(v___x_3034_);
                                        v___x_3037_ = lean_box(0);
                                        v_isShared_3038_ = v_isSharedCheck_3042_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_2995_);
                                v_a_3043_ = lean_ctor_get(v___x_3032_, 0);
                                v_isSharedCheck_3050_ = (!lean_is_exclusive(v___x_3032_)) as u8;
                                if v_isSharedCheck_3050_ == 0 {
                                    v___x_3045_ = v___x_3032_;
                                    v_isShared_3046_ = v_isSharedCheck_3050_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_3043_);
                                    lean_dec(v___x_3032_);
                                    v___x_3045_ = lean_box(0);
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
                    lean_ctor_set(v___x_2995_, 1, v_a_2999_);
                    lean_ctor_set(v___x_2995_, 0, v___x_2997_);
                    v___x_3001_ = v___x_2995_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2997_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_a_2999_);
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
                    v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
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
                    v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
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
                    v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
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
                    v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
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
    mut v_as_3053_: *mut LeanObject,
    mut v_sz_3054_: *mut LeanObject,
    mut v_i_3055_: *mut LeanObject,
    mut v_b_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
    mut v___y_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3065_: usize = 0;
    let mut v_i_boxed_3066_: usize = 0;
    let mut v_res_3067_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3065_ = lean_unbox_usize(v_sz_3054_);
    lean_dec(v_sz_3054_);
    v_i_boxed_3066_ = lean_unbox_usize(v_i_3055_);
    lean_dec(v_i_3055_);
    v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_3053_, v_sz_boxed_3065_, v_i_boxed_3066_, v_b_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
    lean_dec(v___y_3063_);
    lean_dec_ref(v___y_3062_);
    lean_dec(v___y_3061_);
    lean_dec_ref(v___y_3060_);
    lean_dec(v___y_3059_);
    lean_dec_ref(v___y_3058_);
    lean_dec(v___y_3057_);
    lean_dec_ref(v_as_3053_);
    return v_res_3067_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(
    mut v_as_3068_: *mut LeanObject,
    mut v_sz_3069_: usize,
    mut v_i_3070_: usize,
    mut v_b_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
    mut v___y_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
    mut v___y_3077_: *mut LeanObject,
    mut v___y_3078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: usize = 0;
    let mut v___x_3092_: usize = 0;
    let mut v_reuseFailAlloc_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_a_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3131_: u8 = 0;
    let mut v_a_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut v_isSharedCheck_3140_: u8 = 0;
    let mut v_unused_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3080_ = lean_usize_dec_lt(v_i_3070_, v_sz_3069_);
                if v___x_3080_ == 0 {
                    v___x_3081_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3081_, 0, v_b_3071_);
                    return v___x_3081_;
                } else {
                    v_snd_3082_ = lean_ctor_get(v_b_3071_, 1);
                    v_isSharedCheck_3140_ = (!lean_is_exclusive(v_b_3071_)) as u8;
                    if v_isSharedCheck_3140_ == 0 {
                        v_unused_3141_ = lean_ctor_get(v_b_3071_, 0);
                        lean_dec(v_unused_3141_);
                        v___x_3084_ = v_b_3071_;
                        v_isShared_3085_ = v_isSharedCheck_3140_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3082_);
                        lean_dec(v_b_3071_);
                        v___x_3084_ = lean_box(0);
                        v_isShared_3085_ = v_isSharedCheck_3140_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3086_ = lean_box(0);
                v_a_3095_ = lean_array_uget_borrowed(v_as_3068_, v_i_3070_);
                if lean_obj_tag(v_a_3095_) == 0 {
                    v_a_3088_ = v_snd_3082_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_3082_);
                    v_val_3096_ = lean_ctor_get(v_a_3095_, 0);
                    v___x_3097_ = lean_box(0);
                    v___x_3098_ = l_Lean_LocalDecl_isAuxDecl(v_val_3096_);
                    if v___x_3098_ == 0 {
                        v___x_3099_ = l_Lean_LocalDecl_value_x3f(v_val_3096_, v___x_3098_);
                        if lean_obj_tag(v___x_3099_) == 1 {
                            v_val_3100_ = lean_ctor_get(v___x_3099_, 0);
                            lean_inc(v_val_3100_);
                            lean_dec_ref_known(v___x_3099_, 1);
                            v___x_3101_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3100_, v___y_3076_);
                            if lean_obj_tag(v___x_3101_) == 0 {
                                v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
                                lean_inc(v_a_3102_);
                                lean_dec_ref_known(v___x_3101_, 1);
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
                                if lean_obj_tag(v___x_3103_) == 0 {
                                    lean_dec_ref_known(v___x_3103_, 1);
                                    v_a_3088_ = v___x_3097_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_3084_);
                                    v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
                                    v_isSharedCheck_3111_ = (!lean_is_exclusive(v___x_3103_)) as u8;
                                    if v_isSharedCheck_3111_ == 0 {
                                        v___x_3106_ = v___x_3103_;
                                        v_isShared_3107_ = v_isSharedCheck_3111_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3104_);
                                        lean_dec(v___x_3103_);
                                        v___x_3106_ = lean_box(0);
                                        v_isShared_3107_ = v_isSharedCheck_3111_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_3084_);
                                v_a_3112_ = lean_ctor_get(v___x_3101_, 0);
                                v_isSharedCheck_3119_ = (!lean_is_exclusive(v___x_3101_)) as u8;
                                if v_isSharedCheck_3119_ == 0 {
                                    v___x_3114_ = v___x_3101_;
                                    v_isShared_3115_ = v_isSharedCheck_3119_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_3112_);
                                    lean_dec(v___x_3101_);
                                    v___x_3114_ = lean_box(0);
                                    v_isShared_3115_ = v_isSharedCheck_3119_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_3099_);
                            v___x_3120_ = l_Lean_LocalDecl_type(v_val_3096_);
                            v___x_3121_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3120_, v___y_3076_);
                            if lean_obj_tag(v___x_3121_) == 0 {
                                v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
                                lean_inc(v_a_3122_);
                                lean_dec_ref_known(v___x_3121_, 1);
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
                                if lean_obj_tag(v___x_3123_) == 0 {
                                    lean_dec_ref_known(v___x_3123_, 1);
                                    v_a_3088_ = v___x_3097_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_3084_);
                                    v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
                                    v_isSharedCheck_3131_ = (!lean_is_exclusive(v___x_3123_)) as u8;
                                    if v_isSharedCheck_3131_ == 0 {
                                        v___x_3126_ = v___x_3123_;
                                        v_isShared_3127_ = v_isSharedCheck_3131_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3124_);
                                        lean_dec(v___x_3123_);
                                        v___x_3126_ = lean_box(0);
                                        v_isShared_3127_ = v_isSharedCheck_3131_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_3084_);
                                v_a_3132_ = lean_ctor_get(v___x_3121_, 0);
                                v_isSharedCheck_3139_ = (!lean_is_exclusive(v___x_3121_)) as u8;
                                if v_isSharedCheck_3139_ == 0 {
                                    v___x_3134_ = v___x_3121_;
                                    v_isShared_3135_ = v_isSharedCheck_3139_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_3132_);
                                    lean_dec(v___x_3121_);
                                    v___x_3134_ = lean_box(0);
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
                    lean_ctor_set(v___x_3084_, 1, v_a_3088_);
                    lean_ctor_set(v___x_3084_, 0, v___x_3086_);
                    v___x_3090_ = v___x_3084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3086_);
                    lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_3088_);
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
                    v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
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
                    v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
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
                    v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
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
                    v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
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
    mut v_as_3142_: *mut LeanObject,
    mut v_sz_3143_: *mut LeanObject,
    mut v_i_3144_: *mut LeanObject,
    mut v_b_3145_: *mut LeanObject,
    mut v___y_3146_: *mut LeanObject,
    mut v___y_3147_: *mut LeanObject,
    mut v___y_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3154_: usize = 0;
    let mut v_i_boxed_3155_: usize = 0;
    let mut v_res_3156_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3154_ = lean_unbox_usize(v_sz_3143_);
    lean_dec(v_sz_3143_);
    v_i_boxed_3155_ = lean_unbox_usize(v_i_3144_);
    lean_dec(v_i_3144_);
    v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_3142_, v_sz_boxed_3154_, v_i_boxed_3155_, v_b_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
    lean_dec(v___y_3152_);
    lean_dec_ref(v___y_3151_);
    lean_dec(v___y_3150_);
    lean_dec_ref(v___y_3149_);
    lean_dec(v___y_3148_);
    lean_dec_ref(v___y_3147_);
    lean_dec(v___y_3146_);
    lean_dec_ref(v_as_3142_);
    return v_res_3156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(
    mut v_as_3157_: *mut LeanObject,
    mut v_sz_3158_: usize,
    mut v_i_3159_: usize,
    mut v_b_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: usize = 0;
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v_a_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3224_: u8 = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v_unused_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3169_ = lean_usize_dec_lt(v_i_3159_, v_sz_3158_);
                if v___x_3169_ == 0 {
                    v___x_3170_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3170_, 0, v_b_3160_);
                    return v___x_3170_;
                } else {
                    v_snd_3171_ = lean_ctor_get(v_b_3160_, 1);
                    v_isSharedCheck_3229_ = (!lean_is_exclusive(v_b_3160_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v_unused_3230_ = lean_ctor_get(v_b_3160_, 0);
                        lean_dec(v_unused_3230_);
                        v___x_3173_ = v_b_3160_;
                        v_isShared_3174_ = v_isSharedCheck_3229_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3171_);
                        lean_dec(v_b_3160_);
                        v___x_3173_ = lean_box(0);
                        v_isShared_3174_ = v_isSharedCheck_3229_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3175_ = lean_box(0);
                v_a_3184_ = lean_array_uget_borrowed(v_as_3157_, v_i_3159_);
                if lean_obj_tag(v_a_3184_) == 0 {
                    v_a_3177_ = v_snd_3171_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_3171_);
                    v_val_3185_ = lean_ctor_get(v_a_3184_, 0);
                    v___x_3186_ = lean_box(0);
                    v___x_3187_ = l_Lean_LocalDecl_isAuxDecl(v_val_3185_);
                    if v___x_3187_ == 0 {
                        v___x_3188_ = l_Lean_LocalDecl_value_x3f(v_val_3185_, v___x_3187_);
                        if lean_obj_tag(v___x_3188_) == 1 {
                            v_val_3189_ = lean_ctor_get(v___x_3188_, 0);
                            lean_inc(v_val_3189_);
                            lean_dec_ref_known(v___x_3188_, 1);
                            v___x_3190_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_3189_, v___y_3165_);
                            if lean_obj_tag(v___x_3190_) == 0 {
                                v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
                                lean_inc(v_a_3191_);
                                lean_dec_ref_known(v___x_3190_, 1);
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
                                if lean_obj_tag(v___x_3192_) == 0 {
                                    lean_dec_ref_known(v___x_3192_, 1);
                                    v_a_3177_ = v___x_3186_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_3173_);
                                    v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
                                    v_isSharedCheck_3200_ = (!lean_is_exclusive(v___x_3192_)) as u8;
                                    if v_isSharedCheck_3200_ == 0 {
                                        v___x_3195_ = v___x_3192_;
                                        v_isShared_3196_ = v_isSharedCheck_3200_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3193_);
                                        lean_dec(v___x_3192_);
                                        v___x_3195_ = lean_box(0);
                                        v_isShared_3196_ = v_isSharedCheck_3200_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_3173_);
                                v_a_3201_ = lean_ctor_get(v___x_3190_, 0);
                                v_isSharedCheck_3208_ = (!lean_is_exclusive(v___x_3190_)) as u8;
                                if v_isSharedCheck_3208_ == 0 {
                                    v___x_3203_ = v___x_3190_;
                                    v_isShared_3204_ = v_isSharedCheck_3208_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_3201_);
                                    lean_dec(v___x_3190_);
                                    v___x_3203_ = lean_box(0);
                                    v_isShared_3204_ = v_isSharedCheck_3208_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_3188_);
                            v___x_3209_ = l_Lean_LocalDecl_type(v_val_3185_);
                            v___x_3210_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_3209_, v___y_3165_);
                            if lean_obj_tag(v___x_3210_) == 0 {
                                v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
                                lean_inc(v_a_3211_);
                                lean_dec_ref_known(v___x_3210_, 1);
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
                                if lean_obj_tag(v___x_3212_) == 0 {
                                    lean_dec_ref_known(v___x_3212_, 1);
                                    v_a_3177_ = v___x_3186_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_3173_);
                                    v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
                                    v_isSharedCheck_3220_ = (!lean_is_exclusive(v___x_3212_)) as u8;
                                    if v_isSharedCheck_3220_ == 0 {
                                        v___x_3215_ = v___x_3212_;
                                        v_isShared_3216_ = v_isSharedCheck_3220_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3213_);
                                        lean_dec(v___x_3212_);
                                        v___x_3215_ = lean_box(0);
                                        v_isShared_3216_ = v_isSharedCheck_3220_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_3173_);
                                v_a_3221_ = lean_ctor_get(v___x_3210_, 0);
                                v_isSharedCheck_3228_ = (!lean_is_exclusive(v___x_3210_)) as u8;
                                if v_isSharedCheck_3228_ == 0 {
                                    v___x_3223_ = v___x_3210_;
                                    v_isShared_3224_ = v_isSharedCheck_3228_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_3221_);
                                    lean_dec(v___x_3210_);
                                    v___x_3223_ = lean_box(0);
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
                    lean_ctor_set(v___x_3173_, 1, v_a_3177_);
                    lean_ctor_set(v___x_3173_, 0, v___x_3175_);
                    v___x_3179_ = v___x_3173_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3175_);
                    lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_a_3177_);
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
                    v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
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
                    v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
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
                    v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
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
                    v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
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
    mut v_as_3231_: *mut LeanObject,
    mut v_sz_3232_: *mut LeanObject,
    mut v_i_3233_: *mut LeanObject,
    mut v_b_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
    mut v___y_3241_: *mut LeanObject,
    mut v___y_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3243_: usize = 0;
    let mut v_i_boxed_3244_: usize = 0;
    let mut v_res_3245_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3243_ = lean_unbox_usize(v_sz_3232_);
    lean_dec(v_sz_3232_);
    v_i_boxed_3244_ = lean_unbox_usize(v_i_3233_);
    lean_dec(v_i_3233_);
    v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_3231_, v_sz_boxed_3243_, v_i_boxed_3244_, v_b_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
    lean_dec(v___y_3241_);
    lean_dec_ref(v___y_3240_);
    lean_dec(v___y_3239_);
    lean_dec_ref(v___y_3238_);
    lean_dec(v___y_3237_);
    lean_dec_ref(v___y_3236_);
    lean_dec(v___y_3235_);
    lean_dec_ref(v_as_3231_);
    return v_res_3245_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(
    mut v_init_3246_: *mut LeanObject,
    mut v_n_3247_: *mut LeanObject,
    mut v_b_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
    mut v___y_3254_: *mut LeanObject,
    mut v___y_3255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3260_: usize = 0;
    let mut v___x_3261_: usize = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3266_: u8 = 0;
    let mut v_fst_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v_a_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_vs_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3289_: usize = 0;
    let mut v___x_3290_: usize = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v_fst_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3306_: u8 = 0;
    let mut v_a_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_3247_) == 0 {
                    v_cs_3257_ = lean_ctor_get(v_n_3247_, 0);
                    v___x_3258_ = lean_box(0);
                    v___x_3259_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3259_, 0, v___x_3258_);
                    lean_ctor_set(v___x_3259_, 1, v_b_3248_);
                    v_sz_3260_ = lean_array_size(v_cs_3257_);
                    v___x_3261_ = 0usize;
                    v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_3246_, v_cs_3257_, v_sz_3260_, v___x_3261_, v___x_3259_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
                    if lean_obj_tag(v___x_3262_) == 0 {
                        v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3277_ = (!lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3277_ == 0 {
                            v___x_3265_ = v___x_3262_;
                            v_isShared_3266_ = v_isSharedCheck_3277_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3263_);
                            lean_dec(v___x_3262_);
                            v___x_3265_ = lean_box(0);
                            v_isShared_3266_ = v_isSharedCheck_3277_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3278_ = lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3285_ = (!lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3280_ = v___x_3262_;
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3278_);
                            lean_dec(v___x_3262_);
                            v___x_3280_ = lean_box(0);
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3286_ = lean_ctor_get(v_n_3247_, 0);
                    v___x_3287_ = lean_box(0);
                    v___x_3288_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3288_, 0, v___x_3287_);
                    lean_ctor_set(v___x_3288_, 1, v_b_3248_);
                    v_sz_3289_ = lean_array_size(v_vs_3286_);
                    v___x_3290_ = 0usize;
                    v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_3286_, v_sz_3289_, v___x_3290_, v___x_3288_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
                    if lean_obj_tag(v___x_3291_) == 0 {
                        v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
                        v_isSharedCheck_3306_ = (!lean_is_exclusive(v___x_3291_)) as u8;
                        if v_isSharedCheck_3306_ == 0 {
                            v___x_3294_ = v___x_3291_;
                            v_isShared_3295_ = v_isSharedCheck_3306_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3292_);
                            lean_dec(v___x_3291_);
                            v___x_3294_ = lean_box(0);
                            v_isShared_3295_ = v_isSharedCheck_3306_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3307_ = lean_ctor_get(v___x_3291_, 0);
                        v_isSharedCheck_3314_ = (!lean_is_exclusive(v___x_3291_)) as u8;
                        if v_isSharedCheck_3314_ == 0 {
                            v___x_3309_ = v___x_3291_;
                            v_isShared_3310_ = v_isSharedCheck_3314_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3307_);
                            lean_dec(v___x_3291_);
                            v___x_3309_ = lean_box(0);
                            v_isShared_3310_ = v_isSharedCheck_3314_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3267_ = lean_ctor_get(v_a_3263_, 0);
                if lean_obj_tag(v_fst_3267_) == 0 {
                    v_snd_3268_ = lean_ctor_get(v_a_3263_, 1);
                    lean_inc(v_snd_3268_);
                    lean_dec(v_a_3263_);
                    v___x_3269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3269_, 0, v_snd_3268_);
                    if v_isShared_3266_ == 0 {
                        lean_ctor_set(v___x_3265_, 0, v___x_3269_);
                        v___x_3271_ = v___x_3265_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
                        v___x_3271_ = v_reuseFailAlloc_3272_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3267_);
                    lean_dec(v_a_3263_);
                    v_val_3273_ = lean_ctor_get(v_fst_3267_, 0);
                    lean_inc(v_val_3273_);
                    lean_dec_ref_known(v_fst_3267_, 1);
                    if v_isShared_3266_ == 0 {
                        lean_ctor_set(v___x_3265_, 0, v_val_3273_);
                        v___x_3275_ = v___x_3265_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_val_3273_);
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
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3283_;
            }
            6 => {
                v_fst_3296_ = lean_ctor_get(v_a_3292_, 0);
                if lean_obj_tag(v_fst_3296_) == 0 {
                    v_snd_3297_ = lean_ctor_get(v_a_3292_, 1);
                    lean_inc(v_snd_3297_);
                    lean_dec(v_a_3292_);
                    v___x_3298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3298_, 0, v_snd_3297_);
                    if v_isShared_3295_ == 0 {
                        lean_ctor_set(v___x_3294_, 0, v___x_3298_);
                        v___x_3300_ = v___x_3294_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                        v___x_3300_ = v_reuseFailAlloc_3301_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3296_);
                    lean_dec(v_a_3292_);
                    v_val_3302_ = lean_ctor_get(v_fst_3296_, 0);
                    lean_inc(v_val_3302_);
                    lean_dec_ref_known(v_fst_3296_, 1);
                    if v_isShared_3295_ == 0 {
                        lean_ctor_set(v___x_3294_, 0, v_val_3302_);
                        v___x_3304_ = v___x_3294_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_val_3302_);
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
                    v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
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
    mut v_init_3315_: *mut LeanObject,
    mut v_as_3316_: *mut LeanObject,
    mut v_sz_3317_: usize,
    mut v_i_3318_: usize,
    mut v_b_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v_a_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: usize = 0;
    let mut v_reuseFailAlloc_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_a_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_unused_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_usize_dec_lt(v_i_3318_, v_sz_3317_);
                if v___x_3328_ == 0 {
                    v___x_3329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3329_, 0, v_b_3319_);
                    return v___x_3329_;
                } else {
                    v_snd_3330_ = lean_ctor_get(v_b_3319_, 1);
                    v_isSharedCheck_3364_ = (!lean_is_exclusive(v_b_3319_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v_unused_3365_ = lean_ctor_get(v_b_3319_, 0);
                        lean_dec(v_unused_3365_);
                        v___x_3332_ = v_b_3319_;
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3330_);
                        lean_dec(v_b_3319_);
                        v___x_3332_ = lean_box(0);
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3334_ = lean_array_uget_borrowed(v_as_3316_, v_i_3318_);
                lean_inc(v_snd_3330_);
                v___x_3335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3315_, v_a_3334_, v_snd_3330_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
                if lean_obj_tag(v___x_3335_) == 0 {
                    v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3355_ = (!lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3355_ == 0 {
                        v___x_3338_ = v___x_3335_;
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3336_);
                        lean_dec(v___x_3335_);
                        v___x_3338_ = lean_box(0);
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3332_);
                    lean_dec(v_snd_3330_);
                    v_a_3356_ = lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3363_ = (!lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3363_ == 0 {
                        v___x_3358_ = v___x_3335_;
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3356_);
                        lean_dec(v___x_3335_);
                        v___x_3358_ = lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3336_) == 0 {
                    v___x_3340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3340_, 0, v_a_3336_);
                    if v_isShared_3333_ == 0 {
                        lean_ctor_set(v___x_3332_, 0, v___x_3340_);
                        v___x_3342_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3340_);
                        lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_snd_3330_);
                        v___x_3342_ = v_reuseFailAlloc_3346_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3338_);
                    lean_dec(v_snd_3330_);
                    v_a_3347_ = lean_ctor_get(v_a_3336_, 0);
                    lean_inc(v_a_3347_);
                    lean_dec_ref_known(v_a_3336_, 1);
                    v___x_3348_ = lean_box(0);
                    if v_isShared_3333_ == 0 {
                        lean_ctor_set(v___x_3332_, 1, v_a_3347_);
                        lean_ctor_set(v___x_3332_, 0, v___x_3348_);
                        v___x_3350_ = v___x_3332_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3348_);
                        lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3347_);
                        v___x_3350_ = v_reuseFailAlloc_3354_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3339_ == 0 {
                    lean_ctor_set(v___x_3338_, 0, v___x_3342_);
                    v___x_3344_ = v___x_3338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
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
                    v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
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
    mut v_init_3366_: *mut LeanObject,
    mut v_as_3367_: *mut LeanObject,
    mut v_sz_3368_: *mut LeanObject,
    mut v_i_3369_: *mut LeanObject,
    mut v_b_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3379_: usize = 0;
    let mut v_i_boxed_3380_: usize = 0;
    let mut v_res_3381_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3379_ = lean_unbox_usize(v_sz_3368_);
    lean_dec(v_sz_3368_);
    v_i_boxed_3380_ = lean_unbox_usize(v_i_3369_);
    lean_dec(v_i_3369_);
    v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_3366_, v_as_3367_, v_sz_boxed_3379_, v_i_boxed_3380_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
    lean_dec(v___y_3377_);
    lean_dec_ref(v___y_3376_);
    lean_dec(v___y_3375_);
    lean_dec_ref(v___y_3374_);
    lean_dec(v___y_3373_);
    lean_dec_ref(v___y_3372_);
    lean_dec(v___y_3371_);
    lean_dec_ref(v_as_3367_);
    return v_res_3381_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(
    mut v_init_3382_: *mut LeanObject,
    mut v_n_3383_: *mut LeanObject,
    mut v_b_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3393_: *mut LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3382_, v_n_3383_, v_b_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    lean_dec(v___y_3391_);
    lean_dec_ref(v___y_3390_);
    lean_dec(v___y_3389_);
    lean_dec_ref(v___y_3388_);
    lean_dec(v___y_3387_);
    lean_dec_ref(v___y_3386_);
    lean_dec(v___y_3385_);
    lean_dec_ref(v_n_3383_);
    return v_res_3393_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(
    mut v_t_3394_: *mut LeanObject,
    mut v_init_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v_a_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3418_: usize = 0;
    let mut v___x_3419_: usize = 0;
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v_fst_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3434_: u8 = 0;
    let mut v_a_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v_a_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3404_ = lean_ctor_get(v_t_3394_, 0);
                v_tail_3405_ = lean_ctor_get(v_t_3394_, 1);
                v___x_3406_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_3395_, v_root_3404_, v_init_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
                if lean_obj_tag(v___x_3406_) == 0 {
                    v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3443_ = (!lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v___x_3409_ = v___x_3406_;
                        v_isShared_3410_ = v_isSharedCheck_3443_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3407_);
                        lean_dec(v___x_3406_);
                        v___x_3409_ = lean_box(0);
                        v_isShared_3410_ = v_isSharedCheck_3443_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3444_ = lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3451_ = (!lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v___x_3446_ = v___x_3406_;
                        v_isShared_3447_ = v_isSharedCheck_3451_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3444_);
                        lean_dec(v___x_3406_);
                        v___x_3446_ = lean_box(0);
                        v_isShared_3447_ = v_isSharedCheck_3451_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3407_) == 0 {
                    v_a_3411_ = lean_ctor_get(v_a_3407_, 0);
                    lean_inc(v_a_3411_);
                    lean_dec_ref_known(v_a_3407_, 1);
                    if v_isShared_3410_ == 0 {
                        lean_ctor_set(v___x_3409_, 0, v_a_3411_);
                        v___x_3413_ = v___x_3409_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3411_);
                        v___x_3413_ = v_reuseFailAlloc_3414_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3409_);
                    v_a_3415_ = lean_ctor_get(v_a_3407_, 0);
                    lean_inc(v_a_3415_);
                    lean_dec_ref_known(v_a_3407_, 1);
                    v___x_3416_ = lean_box(0);
                    v___x_3417_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3417_, 0, v___x_3416_);
                    lean_ctor_set(v___x_3417_, 1, v_a_3415_);
                    v_sz_3418_ = lean_array_size(v_tail_3405_);
                    v___x_3419_ = 0usize;
                    v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_3405_, v_sz_3418_, v___x_3419_, v___x_3417_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
                    if lean_obj_tag(v___x_3420_) == 0 {
                        v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3434_ = (!lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3434_ == 0 {
                            v___x_3423_ = v___x_3420_;
                            v_isShared_3424_ = v_isSharedCheck_3434_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3421_);
                            lean_dec(v___x_3420_);
                            v___x_3423_ = lean_box(0);
                            v_isShared_3424_ = v_isSharedCheck_3434_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3435_ = lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3442_ = (!lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3442_ == 0 {
                            v___x_3437_ = v___x_3420_;
                            v_isShared_3438_ = v_isSharedCheck_3442_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3435_);
                            lean_dec(v___x_3420_);
                            v___x_3437_ = lean_box(0);
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
                v_fst_3425_ = lean_ctor_get(v_a_3421_, 0);
                if lean_obj_tag(v_fst_3425_) == 0 {
                    v_snd_3426_ = lean_ctor_get(v_a_3421_, 1);
                    lean_inc(v_snd_3426_);
                    lean_dec(v_a_3421_);
                    if v_isShared_3424_ == 0 {
                        lean_ctor_set(v___x_3423_, 0, v_snd_3426_);
                        v___x_3428_ = v___x_3423_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_snd_3426_);
                        v___x_3428_ = v_reuseFailAlloc_3429_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3425_);
                    lean_dec(v_a_3421_);
                    v_val_3430_ = lean_ctor_get(v_fst_3425_, 0);
                    lean_inc(v_val_3430_);
                    lean_dec_ref_known(v_fst_3425_, 1);
                    if v_isShared_3424_ == 0 {
                        lean_ctor_set(v___x_3423_, 0, v_val_3430_);
                        v___x_3432_ = v___x_3423_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_val_3430_);
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
                    v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
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
                    v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
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
    mut v_t_3452_: *mut LeanObject,
    mut v_init_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
    mut v___y_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3462_: *mut LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_3452_, v_init_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
    lean_dec(v___y_3460_);
    lean_dec_ref(v___y_3459_);
    lean_dec(v___y_3458_);
    lean_dec_ref(v___y_3457_);
    lean_dec(v___y_3456_);
    lean_dec_ref(v___y_3455_);
    lean_dec(v___y_3454_);
    lean_dec_ref(v_t_3452_);
    return v_res_3462_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(
    mut v_mvarId_3463_: *mut LeanObject,
    mut v_a_3464_: *mut LeanObject,
    mut v_a_3465_: *mut LeanObject,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
    mut v_a_3468_: *mut LeanObject,
    mut v_a_3469_: *mut LeanObject,
    mut v_a_3470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_a_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3472_ = lean_ctor_get(v_a_3467_, 2);
                v_decls_3473_ = lean_ctor_get(v_lctx_3472_, 1);
                v___x_3474_ = lean_box(0);
                v___x_3475_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_3473_, v___x_3474_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
                if lean_obj_tag(v___x_3475_) == 0 {
                    lean_dec_ref_known(v___x_3475_, 1);
                    v___x_3476_ = l_Lean_MVarId_getType(
                        v_mvarId_3463_,
                        v_a_3467_,
                        v_a_3468_,
                        v_a_3469_,
                        v_a_3470_,
                    );
                    if lean_obj_tag(v___x_3476_) == 0 {
                        v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
                        lean_inc(v_a_3477_);
                        lean_dec_ref_known(v___x_3476_, 1);
                        v___x_3478_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_3477_, v_a_3468_);
                        if lean_obj_tag(v___x_3478_) == 0 {
                            v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
                            lean_inc(v_a_3479_);
                            lean_dec_ref_known(v___x_3478_, 1);
                            v___x_3480_ = l_Lean_Meta_FunInd_Collector_visit(
                                v_a_3479_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_,
                                v_a_3469_, v_a_3470_,
                            );
                            return v___x_3480_;
                        } else {
                            v_a_3481_ = lean_ctor_get(v___x_3478_, 0);
                            v_isSharedCheck_3488_ = (!lean_is_exclusive(v___x_3478_)) as u8;
                            if v_isSharedCheck_3488_ == 0 {
                                v___x_3483_ = v___x_3478_;
                                v_isShared_3484_ = v_isSharedCheck_3488_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3481_);
                                lean_dec(v___x_3478_);
                                v___x_3483_ = lean_box(0);
                                v_isShared_3484_ = v_isSharedCheck_3488_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3489_ = lean_ctor_get(v___x_3476_, 0);
                        v_isSharedCheck_3496_ = (!lean_is_exclusive(v___x_3476_)) as u8;
                        if v_isSharedCheck_3496_ == 0 {
                            v___x_3491_ = v___x_3476_;
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3489_);
                            lean_dec(v___x_3476_);
                            v___x_3491_ = lean_box(0);
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_3463_);
                    return v___x_3475_;
                }
            }
            1 => {
                if v_isShared_3484_ == 0 {
                    v___x_3486_ = v___x_3483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
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
                    v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
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
    mut v_mvarId_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
    mut v_a_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3506_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3504_);
    lean_dec_ref(v_a_3503_);
    lean_dec(v_a_3502_);
    lean_dec_ref(v_a_3501_);
    lean_dec(v_a_3500_);
    lean_dec_ref(v_a_3499_);
    lean_dec(v_a_3498_);
    return v_res_3506_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
    mut v_mvarId_3507_: *mut LeanObject,
    mut v_x_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_a_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3507_,
                    v_x_3508_,
                    v___y_3509_,
                    v___y_3510_,
                    v___y_3511_,
                    v___y_3512_,
                );
                if lean_obj_tag(v___x_3514_) == 0 {
                    v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3522_ = (!lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3522_ == 0 {
                        v___x_3517_ = v___x_3514_;
                        v_isShared_3518_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3515_);
                        lean_dec(v___x_3514_);
                        v___x_3517_ = lean_box(0);
                        v_isShared_3518_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3523_ = lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3530_ = (!lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3530_ == 0 {
                        v___x_3525_ = v___x_3514_;
                        v_isShared_3526_ = v_isSharedCheck_3530_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3523_);
                        lean_dec(v___x_3514_);
                        v___x_3525_ = lean_box(0);
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
                    v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
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
                    v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
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
    mut v_mvarId_3531_: *mut LeanObject,
    mut v_x_3532_: *mut LeanObject,
    mut v___y_3533_: *mut LeanObject,
    mut v___y_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3538_: *mut LeanObject = core::ptr::null_mut();
    v_res_3538_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(
            v_mvarId_3531_,
            v_x_3532_,
            v___y_3533_,
            v___y_3534_,
            v___y_3535_,
            v___y_3536_,
        );
    lean_dec(v___y_3536_);
    lean_dec_ref(v___y_3535_);
    lean_dec(v___y_3534_);
    lean_dec_ref(v___y_3533_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(
    mut v_00_u03b1_3539_: *mut LeanObject,
    mut v_mvarId_3540_: *mut LeanObject,
    mut v_x_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3548_: *mut LeanObject,
    mut v_mvarId_3549_: *mut LeanObject,
    mut v_x_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3556_: *mut LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(
        v_00_u03b1_3548_,
        v_mvarId_3549_,
        v_x_3550_,
        v___y_3551_,
        v___y_3552_,
        v___y_3553_,
        v___y_3554_,
    );
    lean_dec(v___y_3554_);
    lean_dec_ref(v___y_3553_);
    lean_dec(v___y_3552_);
    lean_dec_ref(v___y_3551_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main___lam__0(
    mut v___x_3557_: *mut LeanObject,
    mut v___x_3558_: *mut LeanObject,
    mut v_mvarId_3559_: *mut LeanObject,
    mut v_needle_3560_: *mut LeanObject,
    mut v___y_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_calls_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut v_unused_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3566_ = lean_st_mk_ref(v___x_3557_);
                v___x_3567_ = lean_st_mk_ref(v___x_3558_);
                v___x_3568_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_3559_, v___x_3567_, v_needle_3560_, v___x_3566_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
                if lean_obj_tag(v___x_3568_) == 0 {
                    v_isSharedCheck_3578_ = (!lean_is_exclusive(v___x_3568_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v_unused_3579_ = lean_ctor_get(v___x_3568_, 0);
                        lean_dec(v_unused_3579_);
                        v___x_3570_ = v___x_3568_;
                        v_isShared_3571_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3568_);
                        v___x_3570_ = lean_box(0);
                        v_isShared_3571_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3567_);
                    lean_dec(v___x_3566_);
                    v_a_3580_ = lean_ctor_get(v___x_3568_, 0);
                    v_isSharedCheck_3587_ = (!lean_is_exclusive(v___x_3568_)) as u8;
                    if v_isSharedCheck_3587_ == 0 {
                        v___x_3582_ = v___x_3568_;
                        v_isShared_3583_ = v_isSharedCheck_3587_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3580_);
                        lean_dec(v___x_3568_);
                        v___x_3582_ = lean_box(0);
                        v_isShared_3583_ = v_isSharedCheck_3587_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3572_ = lean_st_ref_get(v___x_3567_);
                lean_dec(v___x_3567_);
                lean_dec(v___x_3572_);
                v___x_3573_ = lean_st_ref_get(v___x_3566_);
                lean_dec(v___x_3566_);
                v_calls_3574_ = lean_ctor_get(v___x_3573_, 0);
                lean_inc_ref(v_calls_3574_);
                lean_dec(v___x_3573_);
                if v_isShared_3571_ == 0 {
                    lean_ctor_set(v___x_3570_, 0, v_calls_3574_);
                    v___x_3576_ = v___x_3570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_calls_3574_);
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
                    v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
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
    mut v___x_3588_: *mut LeanObject,
    mut v___x_3589_: *mut LeanObject,
    mut v_mvarId_3590_: *mut LeanObject,
    mut v_needle_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
    mut v___y_3593_: *mut LeanObject,
    mut v___y_3594_: *mut LeanObject,
    mut v___y_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3597_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3595_);
    lean_dec_ref(v___y_3594_);
    lean_dec(v___y_3593_);
    lean_dec_ref(v___y_3592_);
    lean_dec_ref(v_needle_3591_);
    return v_res_3597_;
}
pub unsafe fn _init_l_Lean_Meta_FunInd_Collector_main___closed__0() -> *mut LeanObject {
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    v___x_3598_ = lean_unsigned_to_nat(64);
    v___x_3599_ = l_Lean_mkPtrSet___redArg(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_Meta_FunInd_Collector_main(
    mut v_needle_3600_: *mut LeanObject,
    mut v_mvarId_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
    mut v_a_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    v___x_3607_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_Collector_main___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_Collector_main___closed__0_once),
        _init_l_Lean_Meta_FunInd_Collector_main___closed__0,
    );
    v___x_3608_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once),
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3,
    );
    lean_inc(v_mvarId_3601_);
    v___f_3609_ = lean_alloc_closure(
        l_Lean_Meta_FunInd_Collector_main___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_3609_, 0, v___x_3608_);
    lean_closure_set(v___f_3609_, 1, v___x_3607_);
    lean_closure_set(v___f_3609_, 2, v_mvarId_3601_);
    lean_closure_set(v___f_3609_, 3, v_needle_3600_);
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
    mut v_needle_3611_: *mut LeanObject,
    mut v_mvarId_3612_: *mut LeanObject,
    mut v_a_3613_: *mut LeanObject,
    mut v_a_3614_: *mut LeanObject,
    mut v_a_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3618_: *mut LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Lean_Meta_FunInd_Collector_main(
        v_needle_3611_,
        v_mvarId_3612_,
        v_a_3613_,
        v_a_3614_,
        v_a_3615_,
        v_a_3616_,
    );
    lean_dec(v_a_3616_);
    lean_dec_ref(v_a_3615_);
    lean_dec(v_a_3614_);
    lean_dec_ref(v_a_3613_);
    return v_res_3618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(
    mut v_needle_3619_: *mut LeanObject,
    mut v_mvarId_3620_: *mut LeanObject,
    mut v_a_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_needle_3627_: *mut LeanObject,
    mut v_mvarId_3628_: *mut LeanObject,
    mut v_a_3629_: *mut LeanObject,
    mut v_a_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
    mut v_a_3632_: *mut LeanObject,
    mut v_a_3633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3634_: *mut LeanObject = core::ptr::null_mut();
    v_res_3634_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(
        v_needle_3627_,
        v_mvarId_3628_,
        v_a_3629_,
        v_a_3630_,
        v_a_3631_,
        v_a_3632_,
    );
    lean_dec(v_a_3632_);
    lean_dec_ref(v_a_3631_);
    lean_dec(v_a_3630_);
    lean_dec_ref(v_a_3629_);
    return v_res_3634_;
}
pub unsafe fn l_Lean_Meta_FunInd_collect(
    mut v_needle_3635_: *mut LeanObject,
    mut v_mvarId_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
    mut v_a_3638_: *mut LeanObject,
    mut v_a_3639_: *mut LeanObject,
    mut v_a_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_needle_3643_: *mut LeanObject,
    mut v_mvarId_3644_: *mut LeanObject,
    mut v_a_3645_: *mut LeanObject,
    mut v_a_3646_: *mut LeanObject,
    mut v_a_3647_: *mut LeanObject,
    mut v_a_3648_: *mut LeanObject,
    mut v_a_3649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3650_: *mut LeanObject = core::ptr::null_mut();
    v_res_3650_ = l_Lean_Meta_FunInd_collect(
        v_needle_3643_,
        v_mvarId_3644_,
        v_a_3645_,
        v_a_3646_,
        v_a_3647_,
        v_a_3648_,
    );
    lean_dec(v_a_3648_);
    lean_dec_ref(v_a_3647_);
    lean_dec(v_a_3646_);
    lean_dec_ref(v_a_3645_);
    return v_res_3650_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_FunIndCollect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls =
        _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls();
    lean_mark_persistent(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_FunIndCollect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_FunIndCollect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
}

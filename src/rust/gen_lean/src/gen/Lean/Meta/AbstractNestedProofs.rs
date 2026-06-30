// Lean compiler output
// Module: Lean.Meta.AbstractNestedProofs
// Imports: Init.Grind.Util Lean.Meta.Closure Lean.Meta.Transform
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_set, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_infer_type, lean_mk_array, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_set___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_setExporting, l_Lean_withoutExporting___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isAppOf, l_Lean_Expr_isAtomic,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash, l_Lean_instBEqFVarId_beq,
    l_Lean_instHashableFVarId_hash, l_Lean_mkAppN,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_setType, l_Lean_LocalDecl_setValue, l_Lean_LocalDecl_type,
    l_Lean_LocalDecl_value_x3f, lean_local_ctx_find,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_inferType___boxed, l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::Closure::{
    initialize_Lean_Meta_Closure, l_Lean_Meta_mkAuxTheorem, l_Lean_Meta_mkAuxTheorem___boxed,
    runtime_initialize_Lean_Meta_Closure,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, l_Lean_Core_betaReduce, l_Lean_Meta_zetaReduce,
    l_Lean_Meta_zetaReduce___boxed, runtime_initialize_Lean_Meta_Transform,
};
use crate::r#gen::Lean::Util::Sorry::l_Lean_Expr_hasSorry;
pub static l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [110, 101, 115, 116, 101, 100, 80, 114, 111, 111, 102, 0],
};
static mut l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_0:
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
            l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value
        ) as *mut leanh::LeanObject,
        1862916703178820790 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        97, 98, 115, 116, 114, 97, 99, 116, 32, 110, 101, 115, 116, 101, 100, 32, 112, 114, 111,
        111, 102, 115, 0,
    ],
};
static mut l_Lean_Meta_AbstractNestedProofs_visit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_abstractNestedProofs___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_abstractNestedProofs___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_abstractNestedProofs___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_abstractNestedProofs___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__0(
    mut v_proof_1842_: *mut leanh::LeanObject,
    mut v___x_1843_: u8,
    mut v_inst_1844_: *mut leanh::LeanObject,
    mut v_cache_1845_: u8,
    mut v_type_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: u8 = 0;
    let mut v___x_1855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_cache_1845_ == 0 {
                    v___y_1848_ = v_cache_1845_;
                    state = 1;
                    continue;
                } else {
                    v___x_1854_ = l_Lean_Expr_hasSorry(v_proof_1842_);
                    if v___x_1854_ == 0 {
                        v___y_1848_ = v_cache_1845_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1855_ = 0;
                        v___y_1848_ = v___x_1855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1849_ = leanh::lean_box(0);
                v___x_1850_ = leanh::lean_box((v___x_1843_) as usize);
                v___x_1851_ = leanh::lean_box((v___y_1848_) as usize);
                v___x_1852_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_mkAuxTheorem___boxed as *mut core::ffi::c_void,
                    10,
                    5,
                );
                leanh::lean_closure_set(v___x_1852_, 0, v_type_1846_);
                leanh::lean_closure_set(v___x_1852_, 1, v_proof_1842_);
                leanh::lean_closure_set(v___x_1852_, 2, v___x_1850_);
                leanh::lean_closure_set(v___x_1852_, 3, v___x_1849_);
                leanh::lean_closure_set(v___x_1852_, 4, v___x_1851_);
                v___x_1853_ = leanh::lean_apply_2(
                    v_inst_1844_,
                    leanh::lean_box(0),
                    v___x_1852_,
                );
                return v___x_1853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__0___boxed(
    mut v_proof_1856_: *mut leanh::LeanObject,
    mut v___x_1857_: *mut leanh::LeanObject,
    mut v_inst_1858_: *mut leanh::LeanObject,
    mut v_cache_1859_: *mut leanh::LeanObject,
    mut v_type_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_150__boxed_1861_: u8 = 0;
    let mut v_cache_boxed_1862_: u8 = 0;
    let mut v_res_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_150__boxed_1861_ = (leanh::lean_unbox(v___x_1857_) as u8);
    v_cache_boxed_1862_ = (leanh::lean_unbox(v_cache_1859_) as u8);
    v_res_1863_ = l_Lean_Meta_abstractProof___redArg___lam__0(
        v_proof_1856_,
        v___x_150__boxed_1861_,
        v_inst_1858_,
        v_cache_boxed_1862_,
        v_type_1860_,
    );
    return v_res_1863_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__1(
    mut v_postprocessType_1864_: *mut leanh::LeanObject,
    mut v_toBind_1865_: *mut leanh::LeanObject,
    mut v___f_1866_: *mut leanh::LeanObject,
    mut v_type_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = leanh::lean_apply_1(v_postprocessType_1864_, v_type_1867_);
    v___x_1869_ = leanh::lean_apply_4(
        v_toBind_1865_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1868_,
        v___f_1866_,
    );
    return v___x_1869_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__2(
    mut v___x_1870_: u8,
    mut v_inst_1871_: *mut leanh::LeanObject,
    mut v_toBind_1872_: *mut leanh::LeanObject,
    mut v___f_1873_: *mut leanh::LeanObject,
    mut v_type_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = leanh::lean_box((v___x_1870_) as usize);
    v___x_1876_ = leanh::lean_box((v___x_1870_) as usize);
    v___x_1877_ = leanh::lean_box((v___x_1870_) as usize);
    v___x_1878_ = leanh::lean_alloc_closure(
        l_Lean_Meta_zetaReduce___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_1878_, 0, v_type_1874_);
    leanh::lean_closure_set(v___x_1878_, 1, v___x_1875_);
    leanh::lean_closure_set(v___x_1878_, 2, v___x_1876_);
    leanh::lean_closure_set(v___x_1878_, 3, v___x_1877_);
    v___x_1879_ = leanh::lean_apply_2(v_inst_1871_, leanh::lean_box(0), v___x_1878_);
    v___x_1880_ = leanh::lean_apply_4(
        v_toBind_1872_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1879_,
        v___f_1873_,
    );
    return v___x_1880_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__2___boxed(
    mut v___x_1881_: *mut leanh::LeanObject,
    mut v_inst_1882_: *mut leanh::LeanObject,
    mut v_toBind_1883_: *mut leanh::LeanObject,
    mut v___f_1884_: *mut leanh::LeanObject,
    mut v_type_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_180__boxed_1886_: u8 = 0;
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_180__boxed_1886_ = (leanh::lean_unbox(v___x_1881_) as u8);
    v_res_1887_ = l_Lean_Meta_abstractProof___redArg___lam__2(
        v___x_180__boxed_1886_,
        v_inst_1882_,
        v_toBind_1883_,
        v___f_1884_,
        v_type_1885_,
    );
    return v_res_1887_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__3(
    mut v_type_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_Lean_Core_betaReduce(v_type_1888_, v___y_1891_, v___y_1892_);
    return v___x_1894_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__3___boxed(
    mut v_type_1895_: *mut leanh::LeanObject,
    mut v___y_1896_: *mut leanh::LeanObject,
    mut v___y_1897_: *mut leanh::LeanObject,
    mut v___y_1898_: *mut leanh::LeanObject,
    mut v___y_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_Lean_Meta_abstractProof___redArg___lam__3(
        v_type_1895_,
        v___y_1896_,
        v___y_1897_,
        v___y_1898_,
        v___y_1899_,
    );
    leanh::lean_dec(v___y_1899_);
    leanh::lean_dec_ref(v___y_1898_);
    leanh::lean_dec(v___y_1897_);
    leanh::lean_dec_ref(v___y_1896_);
    return v_res_1901_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___lam__4(
    mut v_inst_1902_: *mut leanh::LeanObject,
    mut v_toBind_1903_: *mut leanh::LeanObject,
    mut v___f_1904_: *mut leanh::LeanObject,
    mut v_type_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1906_ = leanh::lean_alloc_closure(
        l_Lean_Meta_abstractProof___redArg___lam__3___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1906_, 0, v_type_1905_);
    v___x_1907_ = leanh::lean_apply_2(v_inst_1902_, leanh::lean_box(0), v___f_1906_);
    v___x_1908_ = leanh::lean_apply_4(
        v_toBind_1903_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1907_,
        v___f_1904_,
    );
    return v___x_1908_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg(
    mut v_inst_1909_: *mut leanh::LeanObject,
    mut v_inst_1910_: *mut leanh::LeanObject,
    mut v_inst_1911_: *mut leanh::LeanObject,
    mut v_inst_1912_: *mut leanh::LeanObject,
    mut v_proof_1913_: *mut leanh::LeanObject,
    mut v_cache_1914_: u8,
    mut v_postprocessType_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1916_ = leanh::lean_ctor_get(v_inst_1909_, 1);
    leanh::lean_inc_n(v_toBind_1916_, 4);
    leanh::lean_inc_ref(v_proof_1913_);
    v___x_1917_ = leanh::lean_alloc_closure(
        l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_1917_, 0, v_proof_1913_);
    leanh::lean_inc_n(v_inst_1910_, 3);
    v___x_1918_ = leanh::lean_apply_2(v_inst_1910_, leanh::lean_box(0), v___x_1917_);
    v___x_1919_ = 1;
    v___x_1920_ = leanh::lean_box((v___x_1919_) as usize);
    v___x_1921_ = leanh::lean_box((v_cache_1914_) as usize);
    v___f_1922_ = leanh::lean_alloc_closure(
        l_Lean_Meta_abstractProof___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1922_, 0, v_proof_1913_);
    leanh::lean_closure_set(v___f_1922_, 1, v___x_1920_);
    leanh::lean_closure_set(v___f_1922_, 2, v_inst_1910_);
    leanh::lean_closure_set(v___f_1922_, 3, v___x_1921_);
    v___f_1923_ = leanh::lean_alloc_closure(
        l_Lean_Meta_abstractProof___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1923_, 0, v_postprocessType_1915_);
    leanh::lean_closure_set(v___f_1923_, 1, v_toBind_1916_);
    leanh::lean_closure_set(v___f_1923_, 2, v___f_1922_);
    v___x_1924_ = leanh::lean_box((v___x_1919_) as usize);
    v___f_1925_ = leanh::lean_alloc_closure(
        l_Lean_Meta_abstractProof___redArg___lam__2___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1925_, 0, v___x_1924_);
    leanh::lean_closure_set(v___f_1925_, 1, v_inst_1910_);
    leanh::lean_closure_set(v___f_1925_, 2, v_toBind_1916_);
    leanh::lean_closure_set(v___f_1925_, 3, v___f_1923_);
    v___f_1926_ = leanh::lean_alloc_closure(
        l_Lean_Meta_abstractProof___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1926_, 0, v_inst_1910_);
    leanh::lean_closure_set(v___f_1926_, 1, v_toBind_1916_);
    leanh::lean_closure_set(v___f_1926_, 2, v___f_1925_);
    v___x_1927_ = l_Lean_withoutExporting___redArg(
        v_inst_1909_,
        v_inst_1911_,
        v_inst_1912_,
        v___x_1918_,
        v___x_1919_,
    );
    v___x_1928_ = leanh::lean_apply_4(
        v_toBind_1916_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1927_,
        v___f_1926_,
    );
    return v___x_1928_;
}
pub unsafe fn l_Lean_Meta_abstractProof___redArg___boxed(
    mut v_inst_1929_: *mut leanh::LeanObject,
    mut v_inst_1930_: *mut leanh::LeanObject,
    mut v_inst_1931_: *mut leanh::LeanObject,
    mut v_inst_1932_: *mut leanh::LeanObject,
    mut v_proof_1933_: *mut leanh::LeanObject,
    mut v_cache_1934_: *mut leanh::LeanObject,
    mut v_postprocessType_1935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_boxed_1936_: u8 = 0;
    let mut v_res_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cache_boxed_1936_ = (leanh::lean_unbox(v_cache_1934_) as u8);
    v_res_1937_ = l_Lean_Meta_abstractProof___redArg(
        v_inst_1929_,
        v_inst_1930_,
        v_inst_1931_,
        v_inst_1932_,
        v_proof_1933_,
        v_cache_boxed_1936_,
        v_postprocessType_1935_,
    );
    return v_res_1937_;
}
pub unsafe fn l_Lean_Meta_abstractProof(
    mut v_m_1938_: *mut leanh::LeanObject,
    mut v_inst_1939_: *mut leanh::LeanObject,
    mut v_inst_1940_: *mut leanh::LeanObject,
    mut v_inst_1941_: *mut leanh::LeanObject,
    mut v_inst_1942_: *mut leanh::LeanObject,
    mut v_inst_1943_: *mut leanh::LeanObject,
    mut v_proof_1944_: *mut leanh::LeanObject,
    mut v_cache_1945_: u8,
    mut v_postprocessType_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1947_ = l_Lean_Meta_abstractProof___redArg(
        v_inst_1939_,
        v_inst_1940_,
        v_inst_1941_,
        v_inst_1943_,
        v_proof_1944_,
        v_cache_1945_,
        v_postprocessType_1946_,
    );
    return v___x_1947_;
}
pub unsafe fn l_Lean_Meta_abstractProof___boxed(
    mut v_m_1948_: *mut leanh::LeanObject,
    mut v_inst_1949_: *mut leanh::LeanObject,
    mut v_inst_1950_: *mut leanh::LeanObject,
    mut v_inst_1951_: *mut leanh::LeanObject,
    mut v_inst_1952_: *mut leanh::LeanObject,
    mut v_inst_1953_: *mut leanh::LeanObject,
    mut v_proof_1954_: *mut leanh::LeanObject,
    mut v_cache_1955_: *mut leanh::LeanObject,
    mut v_postprocessType_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_boxed_1957_: u8 = 0;
    let mut v_res_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cache_boxed_1957_ = (leanh::lean_unbox(v_cache_1955_) as u8);
    v_res_1958_ = l_Lean_Meta_abstractProof(
        v_m_1948_,
        v_inst_1949_,
        v_inst_1950_,
        v_inst_1951_,
        v_inst_1952_,
        v_inst_1953_,
        v_proof_1954_,
        v_cache_boxed_1957_,
        v_postprocessType_1956_,
    );
    leanh::lean_dec(v_inst_1952_);
    return v_res_1958_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_getLambdaBody(
    mut v_e_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_body_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_1959_) == 6 {
                    v_body_1960_ = leanh::lean_ctor_get(v_e_1959_, 2);
                    v_e_1959_ = v_body_1960_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_e_1959_);
                    return v_e_1959_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_getLambdaBody___boxed(
    mut v_e_1962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_1962_);
    leanh::lean_dec_ref(v_e_1962_);
    return v_res_1963_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(
    mut v_a_1964_: u8,
    mut v___y_1965_: u8,
    mut v_as_1966_: *mut leanh::LeanObject,
    mut v_i_1967_: usize,
    mut v_stop_1968_: usize,
) -> u8 {
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: u8 = 0;
    let mut v___y_1972_: u8 = 0;
    let mut v___x_1973_: usize = 0;
    let mut v___x_1974_: usize = 0;
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1969_ = lean_usize_dec_eq(v_i_1967_, v_stop_1968_);
                if v___x_1969_ == 0 {
                    v___x_1970_ = 1;
                    v___x_1976_ = lean_array_uget_borrowed(v_as_1966_, v_i_1967_);
                    v___x_1977_ = l_Lean_Expr_isAtomic(v___x_1976_);
                    if v___x_1977_ == 0 {
                        v___y_1972_ = v_a_1964_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1972_ = v___y_1965_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1978_ = 0;
                    return v___x_1978_;
                }
            }
            1 => {
                if v___y_1972_ == 0 {
                    v___x_1973_ = 1usize;
                    v___x_1974_ = lean_usize_add(v_i_1967_, v___x_1973_);
                    v_i_1967_ = v___x_1974_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1970_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(
    mut v_a_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
    mut v_as_1981_: *mut leanh::LeanObject,
    mut v_i_1982_: *mut leanh::LeanObject,
    mut v_stop_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4293__boxed_1984_: u8 = 0;
    let mut v___y_4294__boxed_1985_: u8 = 0;
    let mut v_i_boxed_1986_: usize = 0;
    let mut v_stop_boxed_1987_: usize = 0;
    let mut v_res_1988_: u8 = 0;
    let mut v_r_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_4293__boxed_1984_ = (leanh::lean_unbox(v_a_1979_) as u8);
    v___y_4294__boxed_1985_ = (leanh::lean_unbox(v___y_1980_) as u8);
    v_i_boxed_1986_ = leanh::lean_unbox_usize(v_i_1982_);
    leanh::lean_dec(v_i_1982_);
    v_stop_boxed_1987_ = leanh::lean_unbox_usize(v_stop_1983_);
    leanh::lean_dec(v_stop_1983_);
    v_res_1988_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4293__boxed_1984_, v___y_4294__boxed_1985_, v_as_1981_, v_i_boxed_1986_, v_stop_boxed_1987_);
    leanh::lean_dec_ref(v_as_1981_);
    v_r_1989_ = leanh::lean_box((v_res_1988_) as usize);
    return v_r_1989_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(
    mut v_a_1990_: u8,
    mut v___x_1991_: u8,
    mut v___x_1992_: *mut leanh::LeanObject,
    mut v_x_1993_: *mut leanh::LeanObject,
    mut v_x_1994_: *mut leanh::LeanObject,
    mut v_x_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1998_: u8 = 0;
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: usize = 0;
    let mut v___x_2007_: usize = 0;
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1993_) == 5 {
                    v_fn_2011_ = leanh::lean_ctor_get(v_x_1993_, 0);
                    leanh::lean_inc_ref(v_fn_2011_);
                    v_arg_2012_ = leanh::lean_ctor_get(v_x_1993_, 1);
                    leanh::lean_inc_ref(v_arg_2012_);
                    leanh::lean_dec_ref_known(v_x_1993_, 2);
                    v___x_2013_ = lean_array_set(v_x_1994_, v_x_1995_, v_arg_2012_);
                    v___x_2014_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2015_ = lean_nat_sub(v_x_1995_, v___x_2014_);
                    leanh::lean_dec(v_x_1995_);
                    v_x_1993_ = v_fn_2011_;
                    v_x_1994_ = v___x_2013_;
                    v_x_1995_ = v___x_2015_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_1995_);
                    v___x_2017_ = l_Lean_Expr_isAtomic(v_x_1993_);
                    if v___x_2017_ == 0 {
                        leanh::lean_dec_ref(v_x_1994_);
                        leanh::lean_dec_ref(v_x_1993_);
                        leanh::lean_dec_ref(v___x_1992_);
                        v___x_2018_ = leanh::lean_box((v_a_1990_) as usize);
                        v___x_2019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2019_, 0, v___x_2018_);
                        return v___x_2019_;
                    } else {
                        if v___x_1991_ == 0 {
                            if leanh::lean_obj_tag(v_x_1993_) == 4 {
                                v_declName_2020_ = leanh::lean_ctor_get(v_x_1993_, 0);
                                leanh::lean_inc(v_declName_2020_);
                                leanh::lean_dec_ref_known(v_x_1993_, 2);
                                v___x_2021_ = l_Lean_Environment_contains(
                                    v___x_1992_,
                                    v_declName_2020_,
                                    v_a_1990_,
                                );
                                if v___x_2021_ == 0 {
                                    leanh::lean_dec_ref(v_x_1994_);
                                    v___x_2022_ = leanh::lean_box((v_a_1990_) as usize);
                                    v___x_2023_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
                                    return v___x_2023_;
                                } else {
                                    v___y_1998_ = v___x_1991_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_x_1993_);
                                leanh::lean_dec_ref(v___x_1992_);
                                v___y_1998_ = v___x_1991_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_x_1994_);
                            leanh::lean_dec_ref(v_x_1993_);
                            leanh::lean_dec_ref(v___x_1992_);
                            v___x_2024_ = leanh::lean_box((v_a_1990_) as usize);
                            v___x_2025_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2025_, 0, v___x_2024_);
                            return v___x_2025_;
                        }
                    }
                }
            }
            1 => {
                v___x_1999_ = leanh::lean_unsigned_to_nat(0);
                v___x_2000_ = lean_array_get_size(v_x_1994_);
                v___x_2001_ = lean_nat_dec_lt(v___x_1999_, v___x_2000_);
                if v___x_2001_ == 0 {
                    leanh::lean_dec_ref(v_x_1994_);
                    v___x_2002_ = leanh::lean_box((v___y_1998_) as usize);
                    v___x_2003_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2003_, 0, v___x_2002_);
                    return v___x_2003_;
                } else {
                    if v___x_2001_ == 0 {
                        leanh::lean_dec_ref(v_x_1994_);
                        v___x_2004_ = leanh::lean_box((v___y_1998_) as usize);
                        v___x_2005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2005_, 0, v___x_2004_);
                        return v___x_2005_;
                    } else {
                        v___x_2006_ = 0usize;
                        v___x_2007_ = lean_usize_of_nat(v___x_2000_);
                        v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_1990_, v___y_1998_, v_x_1994_, v___x_2006_, v___x_2007_);
                        leanh::lean_dec_ref(v_x_1994_);
                        v___x_2009_ = leanh::lean_box((v___x_2008_) as usize);
                        v___x_2010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2010_, 0, v___x_2009_);
                        return v___x_2010_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(
    mut v_a_2026_: *mut leanh::LeanObject,
    mut v___x_2027_: *mut leanh::LeanObject,
    mut v___x_2028_: *mut leanh::LeanObject,
    mut v_x_2029_: *mut leanh::LeanObject,
    mut v_x_2030_: *mut leanh::LeanObject,
    mut v_x_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4319__boxed_2033_: u8 = 0;
    let mut v___x_4320__boxed_2034_: u8 = 0;
    let mut v_res_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_4319__boxed_2033_ = (leanh::lean_unbox(v_a_2026_) as u8);
    v___x_4320__boxed_2034_ = (leanh::lean_unbox(v___x_2027_) as u8);
    v_res_2035_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_4319__boxed_2033_, v___x_4320__boxed_2034_, v___x_2028_, v_x_2029_, v_x_2030_, v_x_2031_);
    return v_res_2035_;
}
pub unsafe fn _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = leanh::lean_box(0);
    v_dummy_2044_ = l_Lean_Expr_sort___override(v___x_2043_);
    return v_dummy_2044_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(
    mut v_e_2045_: *mut leanh::LeanObject,
    mut v_env_2046_: *mut leanh::LeanObject,
    mut v___y_2047_: *mut leanh::LeanObject,
    mut v___y_2048_: *mut leanh::LeanObject,
    mut v___y_2049_: *mut leanh::LeanObject,
    mut v___y_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2057_: u8 = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_unused_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_2045_);
                v___x_2052_ = l_Lean_Meta_isProof(
                    v_e_2045_,
                    v___y_2047_,
                    v___y_2048_,
                    v___y_2049_,
                    v___y_2050_,
                );
                if leanh::lean_obj_tag(v___x_2052_) == 0 {
                    v_a_2053_ = leanh::lean_ctor_get(v___x_2052_, 0);
                    leanh::lean_inc(v_a_2053_);
                    v___x_2054_ = (leanh::lean_unbox(v_a_2053_) as u8);
                    if v___x_2054_ == 0 {
                        leanh::lean_dec(v_a_2053_);
                        leanh::lean_dec_ref(v_env_2046_);
                        leanh::lean_dec_ref(v_e_2045_);
                        return v___x_2052_;
                    } else {
                        v_isSharedCheck_2073_ =
                            (!leanh::lean_is_exclusive(v___x_2052_)) as u8;
                        if v_isSharedCheck_2073_ == 0 {
                            v_unused_2074_ = leanh::lean_ctor_get(v___x_2052_, 0);
                            leanh::lean_dec(v_unused_2074_);
                            v___x_2056_ = v___x_2052_;
                            v_isShared_2057_ = v_isSharedCheck_2073_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2052_);
                            v___x_2056_ = leanh::lean_box(0);
                            v_isShared_2057_ = v_isSharedCheck_2073_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2046_);
                    leanh::lean_dec_ref(v_e_2045_);
                    return v___x_2052_;
                }
            }
            1 => {
                v___x_2058_ =
                    l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3;
                v___x_2059_ = l_Lean_Expr_isAppOf(v_e_2045_, v___x_2058_);
                if v___x_2059_ == 0 {
                    leanh::lean_del_object(v___x_2056_);
                    v___x_2060_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_2045_);
                    leanh::lean_dec_ref(v_e_2045_);
                    v_dummy_2061_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once), _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
                    v_nargs_2062_ = l_Lean_Expr_getAppNumArgs(v___x_2060_);
                    leanh::lean_inc(v_nargs_2062_);
                    v___x_2063_ = lean_mk_array(v_nargs_2062_, v_dummy_2061_);
                    v___x_2064_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2065_ = lean_nat_sub(v_nargs_2062_, v___x_2064_);
                    leanh::lean_dec(v_nargs_2062_);
                    v___x_2066_ = (leanh::lean_unbox(v_a_2053_) as u8);
                    leanh::lean_dec(v_a_2053_);
                    v___x_2067_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v___x_2066_, v___x_2059_, v_env_2046_, v___x_2060_, v___x_2063_, v___x_2065_);
                    return v___x_2067_;
                } else {
                    leanh::lean_dec(v_a_2053_);
                    leanh::lean_dec_ref(v_env_2046_);
                    leanh::lean_dec_ref(v_e_2045_);
                    v___x_2068_ = 0;
                    v___x_2069_ = leanh::lean_box((v___x_2068_) as usize);
                    if v_isShared_2057_ == 0 {
                        leanh::lean_ctor_set(v___x_2056_, 0, v___x_2069_);
                        v___x_2071_ = v___x_2056_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
                        v___x_2071_ = v_reuseFailAlloc_2072_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(
    mut v_e_2075_: *mut leanh::LeanObject,
    mut v_env_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2082_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(
        v_e_2075_,
        v_env_2076_,
        v___y_2077_,
        v___y_2078_,
        v___y_2079_,
        v___y_2080_,
    );
    leanh::lean_dec(v___y_2080_);
    leanh::lean_dec_ref(v___y_2079_);
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    return v_res_2082_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(
    mut v___y_2083_: *mut leanh::LeanObject,
    mut v_isExporting_2084_: u8,
    mut v___x_2085_: *mut leanh::LeanObject,
    mut v___y_2086_: *mut leanh::LeanObject,
    mut v___x_2087_: *mut leanh::LeanObject,
    mut v_a_x3f_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v_unused_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2123_: u8 = 0;
    let mut v_unused_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2090_ = lean_st_ref_take(v___y_2083_);
                v_env_2091_ = leanh::lean_ctor_get(v___x_2090_, 0);
                v_nextMacroScope_2092_ = leanh::lean_ctor_get(v___x_2090_, 1);
                v_ngen_2093_ = leanh::lean_ctor_get(v___x_2090_, 2);
                v_auxDeclNGen_2094_ = leanh::lean_ctor_get(v___x_2090_, 3);
                v_traceState_2095_ = leanh::lean_ctor_get(v___x_2090_, 4);
                v_messages_2096_ = leanh::lean_ctor_get(v___x_2090_, 6);
                v_infoState_2097_ = leanh::lean_ctor_get(v___x_2090_, 7);
                v_snapshotTasks_2098_ = leanh::lean_ctor_get(v___x_2090_, 8);
                v_isSharedCheck_2123_ = (!leanh::lean_is_exclusive(v___x_2090_)) as u8;
                if v_isSharedCheck_2123_ == 0 {
                    v_unused_2124_ = leanh::lean_ctor_get(v___x_2090_, 5);
                    leanh::lean_dec(v_unused_2124_);
                    v___x_2100_ = v___x_2090_;
                    v_isShared_2101_ = v_isSharedCheck_2123_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2098_);
                    leanh::lean_inc(v_infoState_2097_);
                    leanh::lean_inc(v_messages_2096_);
                    leanh::lean_inc(v_traceState_2095_);
                    leanh::lean_inc(v_auxDeclNGen_2094_);
                    leanh::lean_inc(v_ngen_2093_);
                    leanh::lean_inc(v_nextMacroScope_2092_);
                    leanh::lean_inc(v_env_2091_);
                    leanh::lean_dec(v___x_2090_);
                    v___x_2100_ = leanh::lean_box(0);
                    v_isShared_2101_ = v_isSharedCheck_2123_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2102_ = l_Lean_Environment_setExporting(v_env_2091_, v_isExporting_2084_);
                if v_isShared_2101_ == 0 {
                    leanh::lean_ctor_set(v___x_2100_, 5, v___x_2085_);
                    leanh::lean_ctor_set(v___x_2100_, 0, v___x_2102_);
                    v___x_2104_ = v___x_2100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2122_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_nextMacroScope_2092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_ngen_2093_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 3, v_auxDeclNGen_2094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 4, v_traceState_2095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 5, v___x_2085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 6, v_messages_2096_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 7, v_infoState_2097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 8, v_snapshotTasks_2098_);
                    v___x_2104_ = v_reuseFailAlloc_2122_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2105_ = lean_st_ref_set(v___y_2083_, v___x_2104_);
                v___x_2106_ = lean_st_ref_take(v___y_2086_);
                v_mctx_2107_ = leanh::lean_ctor_get(v___x_2106_, 0);
                v_zetaDeltaFVarIds_2108_ = leanh::lean_ctor_get(v___x_2106_, 2);
                v_postponed_2109_ = leanh::lean_ctor_get(v___x_2106_, 3);
                v_diag_2110_ = leanh::lean_ctor_get(v___x_2106_, 4);
                v_isSharedCheck_2120_ = (!leanh::lean_is_exclusive(v___x_2106_)) as u8;
                if v_isSharedCheck_2120_ == 0 {
                    v_unused_2121_ = leanh::lean_ctor_get(v___x_2106_, 1);
                    leanh::lean_dec(v_unused_2121_);
                    v___x_2112_ = v___x_2106_;
                    v_isShared_2113_ = v_isSharedCheck_2120_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2110_);
                    leanh::lean_inc(v_postponed_2109_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2108_);
                    leanh::lean_inc(v_mctx_2107_);
                    leanh::lean_dec(v___x_2106_);
                    v___x_2112_ = leanh::lean_box(0);
                    v_isShared_2113_ = v_isSharedCheck_2120_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2113_ == 0 {
                    leanh::lean_ctor_set(v___x_2112_, 1, v___x_2087_);
                    v___x_2115_ = v___x_2112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_mctx_2107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2087_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2119_,
                        2,
                        v_zetaDeltaFVarIds_2108_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_postponed_2109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 4, v_diag_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2119_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2116_ = lean_st_ref_set(v___y_2086_, v___x_2115_);
                v___x_2117_ = leanh::lean_box(0);
                v___x_2118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2118_, 0, v___x_2117_);
                return v___x_2118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(
    mut v___y_2125_: *mut leanh::LeanObject,
    mut v_isExporting_2126_: *mut leanh::LeanObject,
    mut v___x_2127_: *mut leanh::LeanObject,
    mut v___y_2128_: *mut leanh::LeanObject,
    mut v___x_2129_: *mut leanh::LeanObject,
    mut v_a_x3f_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2132_: u8 = 0;
    let mut v_res_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2132_ = (leanh::lean_unbox(v_isExporting_2126_) as u8);
    v_res_2133_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_2125_, v_isExporting_boxed_2132_, v___x_2127_, v___y_2128_, v___x_2129_, v_a_x3f_2130_);
    leanh::lean_dec(v_a_x3f_2130_);
    leanh::lean_dec(v___y_2128_);
    leanh::lean_dec(v___y_2125_);
    return v_res_2133_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2134_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2135_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
    v___x_2136_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2136_, 0, v___x_2135_);
    return v___x_2136_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
    v___x_2138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2137_);
    leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
    return v___x_2138_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
    v___x_2140_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2140_, 0, v___x_2139_);
    leanh::lean_ctor_set(v___x_2140_, 1, v___x_2139_);
    leanh::lean_ctor_set(v___x_2140_, 2, v___x_2139_);
    leanh::lean_ctor_set(v___x_2140_, 3, v___x_2139_);
    leanh::lean_ctor_set(v___x_2140_, 4, v___x_2139_);
    leanh::lean_ctor_set(v___x_2140_, 5, v___x_2139_);
    return v___x_2140_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(
    mut v_x_2141_: *mut leanh::LeanObject,
    mut v_isExporting_2142_: u8,
    mut v___y_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
    mut v___y_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2150_: u8 = 0;
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_unused_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_a_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_unused_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut v_unused_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut v_unused_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2148_ = lean_st_ref_get(v___y_2146_);
                v_env_2149_ = leanh::lean_ctor_get(v___x_2148_, 0);
                leanh::lean_inc_ref(v_env_2149_);
                leanh::lean_dec(v___x_2148_);
                v_isExporting_2150_ = leanh::lean_ctor_get_uint8(
                    v_env_2149_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_2149_);
                v___x_2151_ = lean_st_ref_take(v___y_2146_);
                v_env_2152_ = leanh::lean_ctor_get(v___x_2151_, 0);
                v_nextMacroScope_2153_ = leanh::lean_ctor_get(v___x_2151_, 1);
                v_ngen_2154_ = leanh::lean_ctor_get(v___x_2151_, 2);
                v_auxDeclNGen_2155_ = leanh::lean_ctor_get(v___x_2151_, 3);
                v_traceState_2156_ = leanh::lean_ctor_get(v___x_2151_, 4);
                v_messages_2157_ = leanh::lean_ctor_get(v___x_2151_, 6);
                v_infoState_2158_ = leanh::lean_ctor_get(v___x_2151_, 7);
                v_snapshotTasks_2159_ = leanh::lean_ctor_get(v___x_2151_, 8);
                v_isSharedCheck_2213_ = (!leanh::lean_is_exclusive(v___x_2151_)) as u8;
                if v_isSharedCheck_2213_ == 0 {
                    v_unused_2214_ = leanh::lean_ctor_get(v___x_2151_, 5);
                    leanh::lean_dec(v_unused_2214_);
                    v___x_2161_ = v___x_2151_;
                    v_isShared_2162_ = v_isSharedCheck_2213_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2159_);
                    leanh::lean_inc(v_infoState_2158_);
                    leanh::lean_inc(v_messages_2157_);
                    leanh::lean_inc(v_traceState_2156_);
                    leanh::lean_inc(v_auxDeclNGen_2155_);
                    leanh::lean_inc(v_ngen_2154_);
                    leanh::lean_inc(v_nextMacroScope_2153_);
                    leanh::lean_inc(v_env_2152_);
                    leanh::lean_dec(v___x_2151_);
                    v___x_2161_ = leanh::lean_box(0);
                    v_isShared_2162_ = v_isSharedCheck_2213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2163_ = l_Lean_Environment_setExporting(v_env_2152_, v_isExporting_2142_);
                v___x_2164_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
                if v_isShared_2162_ == 0 {
                    leanh::lean_ctor_set(v___x_2161_, 5, v___x_2164_);
                    leanh::lean_ctor_set(v___x_2161_, 0, v___x_2163_);
                    v___x_2166_ = v___x_2161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2212_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_nextMacroScope_2153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_ngen_2154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 3, v_auxDeclNGen_2155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 4, v_traceState_2156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 5, v___x_2164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 6, v_messages_2157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 7, v_infoState_2158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 8, v_snapshotTasks_2159_);
                    v___x_2166_ = v_reuseFailAlloc_2212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2167_ = lean_st_ref_set(v___y_2146_, v___x_2166_);
                v___x_2168_ = lean_st_ref_take(v___y_2144_);
                v_mctx_2169_ = leanh::lean_ctor_get(v___x_2168_, 0);
                v_zetaDeltaFVarIds_2170_ = leanh::lean_ctor_get(v___x_2168_, 2);
                v_postponed_2171_ = leanh::lean_ctor_get(v___x_2168_, 3);
                v_diag_2172_ = leanh::lean_ctor_get(v___x_2168_, 4);
                v_isSharedCheck_2210_ = (!leanh::lean_is_exclusive(v___x_2168_)) as u8;
                if v_isSharedCheck_2210_ == 0 {
                    v_unused_2211_ = leanh::lean_ctor_get(v___x_2168_, 1);
                    leanh::lean_dec(v_unused_2211_);
                    v___x_2174_ = v___x_2168_;
                    v_isShared_2175_ = v_isSharedCheck_2210_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2172_);
                    leanh::lean_inc(v_postponed_2171_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2170_);
                    leanh::lean_inc(v_mctx_2169_);
                    leanh::lean_dec(v___x_2168_);
                    v___x_2174_ = leanh::lean_box(0);
                    v_isShared_2175_ = v_isSharedCheck_2210_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2176_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
                if v_isShared_2175_ == 0 {
                    leanh::lean_ctor_set(v___x_2174_, 1, v___x_2176_);
                    v___x_2178_ = v___x_2174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_mctx_2169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2176_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2209_,
                        2,
                        v_zetaDeltaFVarIds_2170_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_postponed_2171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_diag_2172_);
                    v___x_2178_ = v_reuseFailAlloc_2209_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2179_ = lean_st_ref_set(v___y_2144_, v___x_2178_);
                leanh::lean_inc(v___y_2146_);
                leanh::lean_inc_ref(v___y_2145_);
                leanh::lean_inc(v___y_2144_);
                leanh::lean_inc_ref(v___y_2143_);
                v_r_2180_ = leanh::lean_apply_5(
                    v_x_2141_,
                    v___y_2143_,
                    v___y_2144_,
                    v___y_2145_,
                    v___y_2146_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_2180_) == 0 {
                    v_a_2181_ = leanh::lean_ctor_get(v_r_2180_, 0);
                    v_isSharedCheck_2197_ = (!leanh::lean_is_exclusive(v_r_2180_)) as u8;
                    if v_isSharedCheck_2197_ == 0 {
                        v___x_2183_ = v_r_2180_;
                        v_isShared_2184_ = v_isSharedCheck_2197_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2181_);
                        leanh::lean_dec(v_r_2180_);
                        v___x_2183_ = leanh::lean_box(0);
                        v_isShared_2184_ = v_isSharedCheck_2197_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2198_ = leanh::lean_ctor_get(v_r_2180_, 0);
                    leanh::lean_inc(v_a_2198_);
                    leanh::lean_dec_ref_known(v_r_2180_, 1);
                    v___x_2199_ = leanh::lean_box(0);
                    v___x_2200_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_2146_, v_isExporting_2150_, v___x_2164_, v___y_2144_, v___x_2176_, v___x_2199_);
                    v_isSharedCheck_2207_ = (!leanh::lean_is_exclusive(v___x_2200_)) as u8;
                    if v_isSharedCheck_2207_ == 0 {
                        v_unused_2208_ = leanh::lean_ctor_get(v___x_2200_, 0);
                        leanh::lean_dec(v_unused_2208_);
                        v___x_2202_ = v___x_2200_;
                        v_isShared_2203_ = v_isSharedCheck_2207_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2200_);
                        v___x_2202_ = leanh::lean_box(0);
                        v_isShared_2203_ = v_isSharedCheck_2207_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_2181_);
                if v_isShared_2184_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2183_, 1);
                    v___x_2186_ = v___x_2183_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2181_);
                    v___x_2186_ = v_reuseFailAlloc_2196_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2187_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_2146_, v_isExporting_2150_, v___x_2164_, v___y_2144_, v___x_2176_, v___x_2186_);
                leanh::lean_dec_ref(v___x_2186_);
                v_isSharedCheck_2194_ = (!leanh::lean_is_exclusive(v___x_2187_)) as u8;
                if v_isSharedCheck_2194_ == 0 {
                    v_unused_2195_ = leanh::lean_ctor_get(v___x_2187_, 0);
                    leanh::lean_dec(v_unused_2195_);
                    v___x_2189_ = v___x_2187_;
                    v_isShared_2190_ = v_isSharedCheck_2194_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2187_);
                    v___x_2189_ = leanh::lean_box(0);
                    v_isShared_2190_ = v_isSharedCheck_2194_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2190_ == 0 {
                    leanh::lean_ctor_set(v___x_2189_, 0, v_a_2181_);
                    v___x_2192_ = v___x_2189_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2181_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2192_;
            }
            9 => {
                if v_isShared_2203_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2202_, 1);
                    leanh::lean_ctor_set(v___x_2202_, 0, v_a_2198_);
                    v___x_2205_ = v___x_2202_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2198_);
                    v___x_2205_ = v_reuseFailAlloc_2206_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(
    mut v_x_2215_: *mut leanh::LeanObject,
    mut v_isExporting_2216_: *mut leanh::LeanObject,
    mut v___y_2217_: *mut leanh::LeanObject,
    mut v___y_2218_: *mut leanh::LeanObject,
    mut v___y_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2222_: u8 = 0;
    let mut v_res_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2222_ = (leanh::lean_unbox(v_isExporting_2216_) as u8);
    v_res_2223_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_2215_, v_isExporting_boxed_2222_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
    leanh::lean_dec(v___y_2220_);
    leanh::lean_dec_ref(v___y_2219_);
    leanh::lean_dec(v___y_2218_);
    leanh::lean_dec_ref(v___y_2217_);
    return v_res_2223_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(
    mut v_x_2224_: *mut leanh::LeanObject,
    mut v_when_2225_: u8,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
    mut v___y_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_2225_ == 0 {
        let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_2229_);
        leanh::lean_inc_ref(v___y_2228_);
        leanh::lean_inc(v___y_2227_);
        leanh::lean_inc_ref(v___y_2226_);
        v___x_2231_ = leanh::lean_apply_5(
            v_x_2224_,
            v___y_2226_,
            v___y_2227_,
            v___y_2228_,
            v___y_2229_,
            leanh::lean_box(0),
        );
        return v___x_2231_;
    } else {
        let mut v___x_2232_: u8 = 0;
        let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2232_ = 0;
        v___x_2233_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_2224_, v___x_2232_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
        return v___x_2233_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(
    mut v_x_2234_: *mut leanh::LeanObject,
    mut v_when_2235_: *mut leanh::LeanObject,
    mut v___y_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
    mut v___y_2238_: *mut leanh::LeanObject,
    mut v___y_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_2241_: u8 = 0;
    let mut v_res_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_2241_ = (leanh::lean_unbox(v_when_2235_) as u8);
    v_res_2242_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_2234_, v_when_boxed_2241_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
    leanh::lean_dec(v___y_2239_);
    leanh::lean_dec_ref(v___y_2238_);
    leanh::lean_dec(v___y_2237_);
    leanh::lean_dec_ref(v___y_2236_);
    return v_res_2242_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(
    mut v_e_2243_: *mut leanh::LeanObject,
    mut v_a_2244_: *mut leanh::LeanObject,
    mut v_a_2245_: *mut leanh::LeanObject,
    mut v_a_2246_: *mut leanh::LeanObject,
    mut v_a_2247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = lean_st_ref_get(v_a_2247_);
    v_env_2250_ = leanh::lean_ctor_get(v___x_2249_, 0);
    leanh::lean_inc_ref(v_env_2250_);
    leanh::lean_dec(v___x_2249_);
    v___f_2251_ = leanh::lean_alloc_closure(
        l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_2251_, 0, v_e_2243_);
    leanh::lean_closure_set(v___f_2251_, 1, v_env_2250_);
    v___x_2252_ = 1;
    v___x_2253_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_2251_, v___x_2252_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
    return v___x_2253_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(
    mut v_e_2254_: *mut leanh::LeanObject,
    mut v_a_2255_: *mut leanh::LeanObject,
    mut v_a_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(
        v_e_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_,
    );
    leanh::lean_dec(v_a_2258_);
    leanh::lean_dec_ref(v_a_2257_);
    leanh::lean_dec(v_a_2256_);
    leanh::lean_dec_ref(v_a_2255_);
    return v_res_2260_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(
    mut v_a_2261_: u8,
    mut v___x_2262_: u8,
    mut v___x_2263_: *mut leanh::LeanObject,
    mut v_x_2264_: *mut leanh::LeanObject,
    mut v_x_2265_: *mut leanh::LeanObject,
    mut v_x_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
    mut v___y_2268_: *mut leanh::LeanObject,
    mut v___y_2269_: *mut leanh::LeanObject,
    mut v___y_2270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2272_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_2261_, v___x_2262_, v___x_2263_, v_x_2264_, v_x_2265_, v_x_2266_);
    return v___x_2272_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(
    mut v_a_2273_: *mut leanh::LeanObject,
    mut v___x_2274_: *mut leanh::LeanObject,
    mut v___x_2275_: *mut leanh::LeanObject,
    mut v_x_2276_: *mut leanh::LeanObject,
    mut v_x_2277_: *mut leanh::LeanObject,
    mut v_x_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4730__boxed_2284_: u8 = 0;
    let mut v___x_4731__boxed_2285_: u8 = 0;
    let mut v_res_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_4730__boxed_2284_ = (leanh::lean_unbox(v_a_2273_) as u8);
    v___x_4731__boxed_2285_ = (leanh::lean_unbox(v___x_2274_) as u8);
    v_res_2286_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(
            v_a_4730__boxed_2284_,
            v___x_4731__boxed_2285_,
            v___x_2275_,
            v_x_2276_,
            v_x_2277_,
            v_x_2278_,
            v___y_2279_,
            v___y_2280_,
            v___y_2281_,
            v___y_2282_,
        );
    leanh::lean_dec(v___y_2282_);
    leanh::lean_dec_ref(v___y_2281_);
    leanh::lean_dec(v___y_2280_);
    leanh::lean_dec_ref(v___y_2279_);
    return v_res_2286_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(
    mut v_00_u03b1_2287_: *mut leanh::LeanObject,
    mut v_x_2288_: *mut leanh::LeanObject,
    mut v_isExporting_2289_: u8,
    mut v___y_2290_: *mut leanh::LeanObject,
    mut v___y_2291_: *mut leanh::LeanObject,
    mut v___y_2292_: *mut leanh::LeanObject,
    mut v___y_2293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_2288_, v_isExporting_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(
    mut v_00_u03b1_2296_: *mut leanh::LeanObject,
    mut v_x_2297_: *mut leanh::LeanObject,
    mut v_isExporting_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2304_: u8 = 0;
    let mut v_res_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2304_ = (leanh::lean_unbox(v_isExporting_2298_) as u8);
    v_res_2305_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(v_00_u03b1_2296_, v_x_2297_, v_isExporting_boxed_2304_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
    leanh::lean_dec(v___y_2302_);
    leanh::lean_dec_ref(v___y_2301_);
    leanh::lean_dec(v___y_2300_);
    leanh::lean_dec_ref(v___y_2299_);
    return v_res_2305_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(
    mut v_00_u03b1_2306_: *mut leanh::LeanObject,
    mut v_x_2307_: *mut leanh::LeanObject,
    mut v_when_2308_: u8,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_2307_, v_when_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    return v___x_2314_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(
    mut v_00_u03b1_2315_: *mut leanh::LeanObject,
    mut v_x_2316_: *mut leanh::LeanObject,
    mut v_when_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
    mut v___y_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
    mut v___y_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_2323_: u8 = 0;
    let mut v_res_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_2323_ = (leanh::lean_unbox(v_when_2317_) as u8);
    v_res_2324_ =
        l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(
            v_00_u03b1_2315_,
            v_x_2316_,
            v_when_boxed_2323_,
            v___y_2318_,
            v___y_2319_,
            v___y_2320_,
            v___y_2321_,
        );
    leanh::lean_dec(v___y_2321_);
    leanh::lean_dec_ref(v___y_2320_);
    leanh::lean_dec(v___y_2319_);
    leanh::lean_dec_ref(v___y_2318_);
    return v_res_2324_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(
    mut v_x_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: u8,
    mut v___y_2327_: *mut leanh::LeanObject,
    mut v___y_2328_: *mut leanh::LeanObject,
    mut v___y_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = leanh::lean_box((v___y_2326_) as usize);
    leanh::lean_inc(v___y_2327_);
    v___x_2334_ = leanh::lean_apply_7(
        v_x_2325_,
        v___x_2333_,
        v___y_2327_,
        v___y_2328_,
        v___y_2329_,
        v___y_2330_,
        v___y_2331_,
        leanh::lean_box(0),
    );
    return v___x_2334_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_29299__boxed_2343_: u8 = 0;
    let mut v_res_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_29299__boxed_2343_ = (leanh::lean_unbox(v___y_2336_) as u8);
    v_res_2344_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_x_2335_, v___y_29299__boxed_2343_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    leanh::lean_dec(v___y_2337_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(
    mut v_lctx_2345_: *mut leanh::LeanObject,
    mut v_localInsts_2346_: *mut leanh::LeanObject,
    mut v_x_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: u8,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2355_ = leanh::lean_box((v___y_2348_) as usize);
                leanh::lean_inc(v___y_2349_);
                v___f_2356_ = leanh::lean_alloc_closure(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___f_2356_, 0, v_x_2347_);
                leanh::lean_closure_set(v___f_2356_, 1, v___x_2355_);
                leanh::lean_closure_set(v___f_2356_, 2, v___y_2349_);
                v___x_2357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    leanh::lean_box(0),
                    v_lctx_2345_,
                    v_localInsts_2346_,
                    v___f_2356_,
                    v___y_2350_,
                    v___y_2351_,
                    v___y_2352_,
                    v___y_2353_,
                );
                if leanh::lean_obj_tag(v___x_2357_) == 0 {
                    return v___x_2357_;
                } else {
                    v_a_2358_ = leanh::lean_ctor_get(v___x_2357_, 0);
                    v_isSharedCheck_2365_ = (!leanh::lean_is_exclusive(v___x_2357_)) as u8;
                    if v_isSharedCheck_2365_ == 0 {
                        v___x_2360_ = v___x_2357_;
                        v_isShared_2361_ = v_isSharedCheck_2365_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2358_);
                        leanh::lean_dec(v___x_2357_);
                        v___x_2360_ = leanh::lean_box(0);
                        v_isShared_2361_ = v_isSharedCheck_2365_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2361_ == 0 {
                    v___x_2363_ = v___x_2360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
                    v___x_2363_ = v_reuseFailAlloc_2364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(
    mut v_lctx_2366_: *mut leanh::LeanObject,
    mut v_localInsts_2367_: *mut leanh::LeanObject,
    mut v_x_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v___y_2370_: *mut leanh::LeanObject,
    mut v___y_2371_: *mut leanh::LeanObject,
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v___y_2373_: *mut leanh::LeanObject,
    mut v___y_2374_: *mut leanh::LeanObject,
    mut v___y_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_29324__boxed_2376_: u8 = 0;
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_29324__boxed_2376_ = (leanh::lean_unbox(v___y_2369_) as u8);
    v_res_2377_ =
        l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(
            v_lctx_2366_,
            v_localInsts_2367_,
            v_x_2368_,
            v___y_29324__boxed_2376_,
            v___y_2370_,
            v___y_2371_,
            v___y_2372_,
            v___y_2373_,
            v___y_2374_,
        );
    leanh::lean_dec(v___y_2374_);
    leanh::lean_dec_ref(v___y_2373_);
    leanh::lean_dec(v___y_2372_);
    leanh::lean_dec_ref(v___y_2371_);
    leanh::lean_dec(v___y_2370_);
    return v_res_2377_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(
    mut v_00_u03b1_2378_: *mut leanh::LeanObject,
    mut v_lctx_2379_: *mut leanh::LeanObject,
    mut v_localInsts_2380_: *mut leanh::LeanObject,
    mut v_x_2381_: *mut leanh::LeanObject,
    mut v___y_2382_: u8,
    mut v___y_2383_: *mut leanh::LeanObject,
    mut v___y_2384_: *mut leanh::LeanObject,
    mut v___y_2385_: *mut leanh::LeanObject,
    mut v___y_2386_: *mut leanh::LeanObject,
    mut v___y_2387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ =
        l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(
            v_lctx_2379_,
            v_localInsts_2380_,
            v_x_2381_,
            v___y_2382_,
            v___y_2383_,
            v___y_2384_,
            v___y_2385_,
            v___y_2386_,
            v___y_2387_,
        );
    return v___x_2389_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(
    mut v_00_u03b1_2390_: *mut leanh::LeanObject,
    mut v_lctx_2391_: *mut leanh::LeanObject,
    mut v_localInsts_2392_: *mut leanh::LeanObject,
    mut v_x_2393_: *mut leanh::LeanObject,
    mut v___y_2394_: *mut leanh::LeanObject,
    mut v___y_2395_: *mut leanh::LeanObject,
    mut v___y_2396_: *mut leanh::LeanObject,
    mut v___y_2397_: *mut leanh::LeanObject,
    mut v___y_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_29368__boxed_2401_: u8 = 0;
    let mut v_res_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_29368__boxed_2401_ = (leanh::lean_unbox(v___y_2394_) as u8);
    v_res_2402_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(
        v_00_u03b1_2390_,
        v_lctx_2391_,
        v_localInsts_2392_,
        v_x_2393_,
        v___y_29368__boxed_2401_,
        v___y_2395_,
        v___y_2396_,
        v___y_2397_,
        v___y_2398_,
        v___y_2399_,
    );
    leanh::lean_dec(v___y_2399_);
    leanh::lean_dec_ref(v___y_2398_);
    leanh::lean_dec(v___y_2397_);
    leanh::lean_dec_ref(v___y_2396_);
    leanh::lean_dec(v___y_2395_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(
    mut v_k_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: u8,
    mut v___y_2405_: *mut leanh::LeanObject,
    mut v_b_2406_: *mut leanh::LeanObject,
    mut v_c_2407_: *mut leanh::LeanObject,
    mut v___y_2408_: *mut leanh::LeanObject,
    mut v___y_2409_: *mut leanh::LeanObject,
    mut v___y_2410_: *mut leanh::LeanObject,
    mut v___y_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = leanh::lean_box((v___y_2404_) as usize);
    leanh::lean_inc(v___y_2411_);
    leanh::lean_inc_ref(v___y_2410_);
    leanh::lean_inc(v___y_2409_);
    leanh::lean_inc_ref(v___y_2408_);
    leanh::lean_inc(v___y_2405_);
    v___x_2414_ = leanh::lean_apply_9(
        v_k_2403_,
        v_b_2406_,
        v_c_2407_,
        v___x_2413_,
        v___y_2405_,
        v___y_2408_,
        v___y_2409_,
        v___y_2410_,
        v___y_2411_,
        leanh::lean_box(0),
    );
    return v___x_2414_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(
    mut v_k_2415_: *mut leanh::LeanObject,
    mut v___y_2416_: *mut leanh::LeanObject,
    mut v___y_2417_: *mut leanh::LeanObject,
    mut v_b_2418_: *mut leanh::LeanObject,
    mut v_c_2419_: *mut leanh::LeanObject,
    mut v___y_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
    mut v___y_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_29391__boxed_2425_: u8 = 0;
    let mut v_res_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_29391__boxed_2425_ = (leanh::lean_unbox(v___y_2416_) as u8);
    v_res_2426_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_2415_, v___y_29391__boxed_2425_, v___y_2417_, v_b_2418_, v_c_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
    leanh::lean_dec(v___y_2423_);
    leanh::lean_dec_ref(v___y_2422_);
    leanh::lean_dec(v___y_2421_);
    leanh::lean_dec_ref(v___y_2420_);
    leanh::lean_dec(v___y_2417_);
    return v_res_2426_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(
    mut v_e_2427_: *mut leanh::LeanObject,
    mut v_k_2428_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2429_: u8,
    mut v_preserveNondepLet_2430_: u8,
    mut v___y_2431_: u8,
    mut v___y_2432_: *mut leanh::LeanObject,
    mut v___y_2433_: *mut leanh::LeanObject,
    mut v___y_2434_: *mut leanh::LeanObject,
    mut v___y_2435_: *mut leanh::LeanObject,
    mut v___y_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: u8 = 0;
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2438_ = leanh::lean_box((v___y_2431_) as usize);
                leanh::lean_inc(v___y_2432_);
                v___f_2439_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___f_2439_, 0, v_k_2428_);
                leanh::lean_closure_set(v___f_2439_, 1, v___x_2438_);
                leanh::lean_closure_set(v___f_2439_, 2, v___y_2432_);
                v___x_2440_ = 1;
                v___x_2441_ = 0;
                v___x_2442_ = leanh::lean_box(0);
                v___x_2443_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_2427_,
                    v___x_2440_,
                    v___x_2440_,
                    v_preserveNondepLet_2430_,
                    v___x_2441_,
                    v___x_2442_,
                    v___f_2439_,
                    v_cleanupAnnotations_2429_,
                    v___y_2433_,
                    v___y_2434_,
                    v___y_2435_,
                    v___y_2436_,
                );
                if leanh::lean_obj_tag(v___x_2443_) == 0 {
                    return v___x_2443_;
                } else {
                    v_a_2444_ = leanh::lean_ctor_get(v___x_2443_, 0);
                    v_isSharedCheck_2451_ = (!leanh::lean_is_exclusive(v___x_2443_)) as u8;
                    if v_isSharedCheck_2451_ == 0 {
                        v___x_2446_ = v___x_2443_;
                        v_isShared_2447_ = v_isSharedCheck_2451_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2444_);
                        leanh::lean_dec(v___x_2443_);
                        v___x_2446_ = leanh::lean_box(0);
                        v_isShared_2447_ = v_isSharedCheck_2451_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2447_ == 0 {
                    v___x_2449_ = v___x_2446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
                    v___x_2449_ = v_reuseFailAlloc_2450_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(
    mut v_e_2452_: *mut leanh::LeanObject,
    mut v_k_2453_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2454_: *mut leanh::LeanObject,
    mut v_preserveNondepLet_2455_: *mut leanh::LeanObject,
    mut v___y_2456_: *mut leanh::LeanObject,
    mut v___y_2457_: *mut leanh::LeanObject,
    mut v___y_2458_: *mut leanh::LeanObject,
    mut v___y_2459_: *mut leanh::LeanObject,
    mut v___y_2460_: *mut leanh::LeanObject,
    mut v___y_2461_: *mut leanh::LeanObject,
    mut v___y_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2463_: u8 = 0;
    let mut v_preserveNondepLet_boxed_2464_: u8 = 0;
    let mut v___y_29416__boxed_2465_: u8 = 0;
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2463_ = (leanh::lean_unbox(v_cleanupAnnotations_2454_) as u8);
    v_preserveNondepLet_boxed_2464_ = (leanh::lean_unbox(v_preserveNondepLet_2455_) as u8);
    v___y_29416__boxed_2465_ = (leanh::lean_unbox(v___y_2456_) as u8);
    v_res_2466_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_2452_, v_k_2453_, v_cleanupAnnotations_boxed_2463_, v_preserveNondepLet_boxed_2464_, v___y_29416__boxed_2465_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
    leanh::lean_dec(v___y_2461_);
    leanh::lean_dec_ref(v___y_2460_);
    leanh::lean_dec(v___y_2459_);
    leanh::lean_dec_ref(v___y_2458_);
    leanh::lean_dec(v___y_2457_);
    return v_res_2466_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(
    mut v_00_u03b1_2467_: *mut leanh::LeanObject,
    mut v_e_2468_: *mut leanh::LeanObject,
    mut v_k_2469_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2470_: u8,
    mut v_preserveNondepLet_2471_: u8,
    mut v___y_2472_: u8,
    mut v___y_2473_: *mut leanh::LeanObject,
    mut v___y_2474_: *mut leanh::LeanObject,
    mut v___y_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_2468_, v_k_2469_, v_cleanupAnnotations_2470_, v_preserveNondepLet_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
    return v___x_2479_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(
    mut v_00_u03b1_2480_: *mut leanh::LeanObject,
    mut v_e_2481_: *mut leanh::LeanObject,
    mut v_k_2482_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2483_: *mut leanh::LeanObject,
    mut v_preserveNondepLet_2484_: *mut leanh::LeanObject,
    mut v___y_2485_: *mut leanh::LeanObject,
    mut v___y_2486_: *mut leanh::LeanObject,
    mut v___y_2487_: *mut leanh::LeanObject,
    mut v___y_2488_: *mut leanh::LeanObject,
    mut v___y_2489_: *mut leanh::LeanObject,
    mut v___y_2490_: *mut leanh::LeanObject,
    mut v___y_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2492_: u8 = 0;
    let mut v_preserveNondepLet_boxed_2493_: u8 = 0;
    let mut v___y_29466__boxed_2494_: u8 = 0;
    let mut v_res_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2492_ = (leanh::lean_unbox(v_cleanupAnnotations_2483_) as u8);
    v_preserveNondepLet_boxed_2493_ = (leanh::lean_unbox(v_preserveNondepLet_2484_) as u8);
    v___y_29466__boxed_2494_ = (leanh::lean_unbox(v___y_2485_) as u8);
    v_res_2495_ =
        l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(
            v_00_u03b1_2480_,
            v_e_2481_,
            v_k_2482_,
            v_cleanupAnnotations_boxed_2492_,
            v_preserveNondepLet_boxed_2493_,
            v___y_29466__boxed_2494_,
            v___y_2486_,
            v___y_2487_,
            v___y_2488_,
            v___y_2489_,
            v___y_2490_,
        );
    leanh::lean_dec(v___y_2490_);
    leanh::lean_dec_ref(v___y_2489_);
    leanh::lean_dec(v___y_2488_);
    leanh::lean_dec_ref(v___y_2487_);
    leanh::lean_dec(v___y_2486_);
    return v_res_2495_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(
    mut v_type_2496_: *mut leanh::LeanObject,
    mut v_k_2497_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2498_: u8,
    mut v___y_2499_: u8,
    mut v___y_2500_: *mut leanh::LeanObject,
    mut v___y_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
    mut v___y_2504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: u8 = 0;
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2506_ = leanh::lean_box((v___y_2499_) as usize);
                leanh::lean_inc(v___y_2500_);
                v___f_2507_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___f_2507_, 0, v_k_2497_);
                leanh::lean_closure_set(v___f_2507_, 1, v___x_2506_);
                leanh::lean_closure_set(v___f_2507_, 2, v___y_2500_);
                v___x_2508_ = 0;
                v___x_2509_ = leanh::lean_box(0);
                v___x_2510_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_2508_,
                        v___x_2509_,
                        v_type_2496_,
                        v___f_2507_,
                        v_cleanupAnnotations_2498_,
                        v___x_2508_,
                        v___y_2501_,
                        v___y_2502_,
                        v___y_2503_,
                        v___y_2504_,
                    );
                if leanh::lean_obj_tag(v___x_2510_) == 0 {
                    return v___x_2510_;
                } else {
                    v_a_2511_ = leanh::lean_ctor_get(v___x_2510_, 0);
                    v_isSharedCheck_2518_ = (!leanh::lean_is_exclusive(v___x_2510_)) as u8;
                    if v_isSharedCheck_2518_ == 0 {
                        v___x_2513_ = v___x_2510_;
                        v_isShared_2514_ = v_isSharedCheck_2518_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2511_);
                        leanh::lean_dec(v___x_2510_);
                        v___x_2513_ = leanh::lean_box(0);
                        v_isShared_2514_ = v_isSharedCheck_2518_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2514_ == 0 {
                    v___x_2516_ = v___x_2513_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
                    v___x_2516_ = v_reuseFailAlloc_2517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(
    mut v_type_2519_: *mut leanh::LeanObject,
    mut v_k_2520_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2521_: *mut leanh::LeanObject,
    mut v___y_2522_: *mut leanh::LeanObject,
    mut v___y_2523_: *mut leanh::LeanObject,
    mut v___y_2524_: *mut leanh::LeanObject,
    mut v___y_2525_: *mut leanh::LeanObject,
    mut v___y_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2529_: u8 = 0;
    let mut v___y_29489__boxed_2530_: u8 = 0;
    let mut v_res_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2529_ = (leanh::lean_unbox(v_cleanupAnnotations_2521_) as u8);
    v___y_29489__boxed_2530_ = (leanh::lean_unbox(v___y_2522_) as u8);
    v_res_2531_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(
            v_type_2519_,
            v_k_2520_,
            v_cleanupAnnotations_boxed_2529_,
            v___y_29489__boxed_2530_,
            v___y_2523_,
            v___y_2524_,
            v___y_2525_,
            v___y_2526_,
            v___y_2527_,
        );
    leanh::lean_dec(v___y_2527_);
    leanh::lean_dec_ref(v___y_2526_);
    leanh::lean_dec(v___y_2525_);
    leanh::lean_dec_ref(v___y_2524_);
    leanh::lean_dec(v___y_2523_);
    return v_res_2531_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(
    mut v_00_u03b1_2532_: *mut leanh::LeanObject,
    mut v_type_2533_: *mut leanh::LeanObject,
    mut v_k_2534_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2535_: u8,
    mut v___y_2536_: u8,
    mut v___y_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
    mut v___y_2540_: *mut leanh::LeanObject,
    mut v___y_2541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2543_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(
            v_type_2533_,
            v_k_2534_,
            v_cleanupAnnotations_2535_,
            v___y_2536_,
            v___y_2537_,
            v___y_2538_,
            v___y_2539_,
            v___y_2540_,
            v___y_2541_,
        );
    return v___x_2543_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(
    mut v_00_u03b1_2544_: *mut leanh::LeanObject,
    mut v_type_2545_: *mut leanh::LeanObject,
    mut v_k_2546_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2547_: *mut leanh::LeanObject,
    mut v___y_2548_: *mut leanh::LeanObject,
    mut v___y_2549_: *mut leanh::LeanObject,
    mut v___y_2550_: *mut leanh::LeanObject,
    mut v___y_2551_: *mut leanh::LeanObject,
    mut v___y_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2555_: u8 = 0;
    let mut v___y_29537__boxed_2556_: u8 = 0;
    let mut v_res_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2555_ = (leanh::lean_unbox(v_cleanupAnnotations_2547_) as u8);
    v___y_29537__boxed_2556_ = (leanh::lean_unbox(v___y_2548_) as u8);
    v_res_2557_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(
        v_00_u03b1_2544_,
        v_type_2545_,
        v_k_2546_,
        v_cleanupAnnotations_boxed_2555_,
        v___y_29537__boxed_2556_,
        v___y_2549_,
        v___y_2550_,
        v___y_2551_,
        v___y_2552_,
        v___y_2553_,
    );
    leanh::lean_dec(v___y_2553_);
    leanh::lean_dec_ref(v___y_2552_);
    leanh::lean_dec(v___y_2551_);
    leanh::lean_dec_ref(v___y_2550_);
    leanh::lean_dec(v___y_2549_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(
    mut v_x_2558_: *mut leanh::LeanObject,
    mut v_x_2559_: *mut leanh::LeanObject,
    mut v_x_2560_: *mut leanh::LeanObject,
    mut v_x_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2562_ = leanh::lean_ctor_get(v_x_2558_, 0);
                v_vs_2563_ = leanh::lean_ctor_get(v_x_2558_, 1);
                v_isSharedCheck_2587_ = (!leanh::lean_is_exclusive(v_x_2558_)) as u8;
                if v_isSharedCheck_2587_ == 0 {
                    v___x_2565_ = v_x_2558_;
                    v_isShared_2566_ = v_isSharedCheck_2587_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2563_);
                    leanh::lean_inc(v_ks_2562_);
                    leanh::lean_dec(v_x_2558_);
                    v___x_2565_ = leanh::lean_box(0);
                    v_isShared_2566_ = v_isSharedCheck_2587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2567_ = lean_array_get_size(v_ks_2562_);
                v___x_2568_ = lean_nat_dec_lt(v_x_2559_, v___x_2567_);
                if v___x_2568_ == 0 {
                    leanh::lean_dec(v_x_2559_);
                    v___x_2569_ = lean_array_push(v_ks_2562_, v_x_2560_);
                    v___x_2570_ = lean_array_push(v_vs_2563_, v_x_2561_);
                    if v_isShared_2566_ == 0 {
                        leanh::lean_ctor_set(v___x_2565_, 1, v___x_2570_);
                        leanh::lean_ctor_set(v___x_2565_, 0, v___x_2569_);
                        v___x_2572_ = v___x_2565_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2573_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2569_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 1, v___x_2570_);
                        v___x_2572_ = v_reuseFailAlloc_2573_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2574_ = lean_array_fget_borrowed(v_ks_2562_, v_x_2559_);
                    v___x_2575_ = l_Lean_instBEqFVarId_beq(v_x_2560_, v_k_x27_2574_);
                    if v___x_2575_ == 0 {
                        if v_isShared_2566_ == 0 {
                            v___x_2577_ = v___x_2565_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2581_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_ks_2562_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_vs_2563_);
                            v___x_2577_ = v_reuseFailAlloc_2581_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2582_ = lean_array_fset(v_ks_2562_, v_x_2559_, v_x_2560_);
                        v___x_2583_ = lean_array_fset(v_vs_2563_, v_x_2559_, v_x_2561_);
                        leanh::lean_dec(v_x_2559_);
                        if v_isShared_2566_ == 0 {
                            leanh::lean_ctor_set(v___x_2565_, 1, v___x_2583_);
                            leanh::lean_ctor_set(v___x_2565_, 0, v___x_2582_);
                            v___x_2585_ = v___x_2565_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2586_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2582_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___x_2583_);
                            v___x_2585_ = v_reuseFailAlloc_2586_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2572_;
            }
            3 => {
                v___x_2578_ = leanh::lean_unsigned_to_nat(1);
                v___x_2579_ = lean_nat_add(v_x_2559_, v___x_2578_);
                leanh::lean_dec(v_x_2559_);
                v_x_2558_ = v___x_2577_;
                v_x_2559_ = v___x_2579_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(
    mut v_n_2588_: *mut leanh::LeanObject,
    mut v_k_2589_: *mut leanh::LeanObject,
    mut v_v_2590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = leanh::lean_unsigned_to_nat(0);
    v___x_2592_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_n_2588_, v___x_2591_, v_k_2589_, v_v_2590_);
    return v___x_2592_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0()
-> usize {
    let mut v___x_2593_: usize = 0;
    let mut v___x_2594_: usize = 0;
    let mut v___x_2595_: usize = 0;
    v___x_2593_ = 5usize;
    v___x_2594_ = 1usize;
    v___x_2595_ = lean_usize_shift_left(v___x_2594_, v___x_2593_);
    return v___x_2595_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1()
-> usize {
    let mut v___x_2596_: usize = 0;
    let mut v___x_2597_: usize = 0;
    let mut v___x_2598_: usize = 0;
    v___x_2596_ = 1usize;
    v___x_2597_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0);
    v___x_2598_ = lean_usize_sub(v___x_2597_, v___x_2596_);
    return v___x_2598_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2599_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(
    mut v_x_2600_: *mut leanh::LeanObject,
    mut v_x_2601_: usize,
    mut v_x_2602_: usize,
    mut v_x_2603_: *mut leanh::LeanObject,
    mut v_x_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: usize = 0;
    let mut v___x_2607_: usize = 0;
    let mut v___x_2608_: usize = 0;
    let mut v___x_2609_: usize = 0;
    let mut v_j_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v_v_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2636_: u8 = 0;
    let mut v_node_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2640_: u8 = 0;
    let mut v___x_2641_: usize = 0;
    let mut v___x_2642_: usize = 0;
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2649_: u8 = 0;
    let mut v_unused_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2660_: u8 = 0;
    let mut v_ks_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: usize = 0;
    let mut v___x_2667_: u8 = 0;
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v_reuseFailAlloc_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2600_) == 0 {
                    v_es_2605_ = leanh::lean_ctor_get(v_x_2600_, 0);
                    v___x_2606_ = 5usize;
                    v___x_2607_ = 1usize;
                    v___x_2608_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1);
                    v___x_2609_ = lean_usize_land(v_x_2601_, v___x_2608_);
                    v_j_2610_ = lean_usize_to_nat(v___x_2609_);
                    v___x_2611_ = lean_array_get_size(v_es_2605_);
                    v___x_2612_ = lean_nat_dec_lt(v_j_2610_, v___x_2611_);
                    if v___x_2612_ == 0 {
                        leanh::lean_dec(v_j_2610_);
                        leanh::lean_dec(v_x_2604_);
                        leanh::lean_dec(v_x_2603_);
                        return v_x_2600_;
                    } else {
                        leanh::lean_inc_ref(v_es_2605_);
                        v_isSharedCheck_2649_ = (!leanh::lean_is_exclusive(v_x_2600_)) as u8;
                        if v_isSharedCheck_2649_ == 0 {
                            v_unused_2650_ = leanh::lean_ctor_get(v_x_2600_, 0);
                            leanh::lean_dec(v_unused_2650_);
                            v___x_2614_ = v_x_2600_;
                            v_isShared_2615_ = v_isSharedCheck_2649_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2600_);
                            v___x_2614_ = leanh::lean_box(0);
                            v_isShared_2615_ = v_isSharedCheck_2649_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2651_ = leanh::lean_ctor_get(v_x_2600_, 0);
                    v_vs_2652_ = leanh::lean_ctor_get(v_x_2600_, 1);
                    v_isSharedCheck_2672_ = (!leanh::lean_is_exclusive(v_x_2600_)) as u8;
                    if v_isSharedCheck_2672_ == 0 {
                        v___x_2654_ = v_x_2600_;
                        v_isShared_2655_ = v_isSharedCheck_2672_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2652_);
                        leanh::lean_inc(v_ks_2651_);
                        leanh::lean_dec(v_x_2600_);
                        v___x_2654_ = leanh::lean_box(0);
                        v_isShared_2655_ = v_isSharedCheck_2672_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2616_ = lean_array_fget(v_es_2605_, v_j_2610_);
                v___x_2617_ = leanh::lean_box(0);
                v_xs_x27_2618_ = lean_array_fset(v_es_2605_, v_j_2610_, v___x_2617_);
                match leanh::lean_obj_tag(v_v_2616_) {
                    0 => {
                        v_key_2625_ = leanh::lean_ctor_get(v_v_2616_, 0);
                        v_val_2626_ = leanh::lean_ctor_get(v_v_2616_, 1);
                        v_isSharedCheck_2636_ = (!leanh::lean_is_exclusive(v_v_2616_)) as u8;
                        if v_isSharedCheck_2636_ == 0 {
                            v___x_2628_ = v_v_2616_;
                            v_isShared_2629_ = v_isSharedCheck_2636_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2626_);
                            leanh::lean_inc(v_key_2625_);
                            leanh::lean_dec(v_v_2616_);
                            v___x_2628_ = leanh::lean_box(0);
                            v_isShared_2629_ = v_isSharedCheck_2636_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2637_ = leanh::lean_ctor_get(v_v_2616_, 0);
                        v_isSharedCheck_2647_ = (!leanh::lean_is_exclusive(v_v_2616_)) as u8;
                        if v_isSharedCheck_2647_ == 0 {
                            v___x_2639_ = v_v_2616_;
                            v_isShared_2640_ = v_isSharedCheck_2647_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2637_);
                            leanh::lean_dec(v_v_2616_);
                            v___x_2639_ = leanh::lean_box(0);
                            v_isShared_2640_ = v_isSharedCheck_2647_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2648_, 0, v_x_2603_);
                        leanh::lean_ctor_set(v___x_2648_, 1, v_x_2604_);
                        v___y_2620_ = v___x_2648_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2621_ = lean_array_fset(v_xs_x27_2618_, v_j_2610_, v___y_2620_);
                leanh::lean_dec(v_j_2610_);
                if v_isShared_2615_ == 0 {
                    leanh::lean_ctor_set(v___x_2614_, 0, v___x_2621_);
                    v___x_2623_ = v___x_2614_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2623_;
            }
            4 => {
                v___x_2630_ = l_Lean_instBEqFVarId_beq(v_x_2603_, v_key_2625_);
                if v___x_2630_ == 0 {
                    leanh::lean_del_object(v___x_2628_);
                    v___x_2631_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2625_,
                        v_val_2626_,
                        v_x_2603_,
                        v_x_2604_,
                    );
                    v___x_2632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2632_, 0, v___x_2631_);
                    v___y_2620_ = v___x_2632_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2626_);
                    leanh::lean_dec(v_key_2625_);
                    if v_isShared_2629_ == 0 {
                        leanh::lean_ctor_set(v___x_2628_, 1, v_x_2604_);
                        leanh::lean_ctor_set(v___x_2628_, 0, v_x_2603_);
                        v___x_2634_ = v___x_2628_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2635_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_x_2603_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_x_2604_);
                        v___x_2634_ = v_reuseFailAlloc_2635_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2620_ = v___x_2634_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2641_ = lean_usize_shift_right(v_x_2601_, v___x_2606_);
                v___x_2642_ = lean_usize_add(v_x_2602_, v___x_2607_);
                v___x_2643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_node_2637_, v___x_2641_, v___x_2642_, v_x_2603_, v_x_2604_);
                if v_isShared_2640_ == 0 {
                    leanh::lean_ctor_set(v___x_2639_, 0, v___x_2643_);
                    v___x_2645_ = v___x_2639_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
                    v___x_2645_ = v_reuseFailAlloc_2646_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2620_ = v___x_2645_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2655_ == 0 {
                    v___x_2657_ = v___x_2654_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_ks_2651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_vs_2652_);
                    v___x_2657_ = v_reuseFailAlloc_2671_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2658_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v___x_2657_, v_x_2603_, v_x_2604_);
                v___x_2666_ = 7usize;
                v___x_2667_ = lean_usize_dec_le(v___x_2666_, v_x_2602_);
                if v___x_2667_ == 0 {
                    v___x_2668_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2658_);
                    v___x_2669_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2670_ = lean_nat_dec_lt(v___x_2668_, v___x_2669_);
                    leanh::lean_dec(v___x_2668_);
                    v___y_2660_ = v___x_2670_;
                    state = 10;
                    continue;
                } else {
                    v___y_2660_ = v___x_2667_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2660_ == 0 {
                    v_ks_2661_ = leanh::lean_ctor_get(v_newNode_2658_, 0);
                    leanh::lean_inc_ref(v_ks_2661_);
                    v_vs_2662_ = leanh::lean_ctor_get(v_newNode_2658_, 1);
                    leanh::lean_inc_ref(v_vs_2662_);
                    leanh::lean_dec_ref(v_newNode_2658_);
                    v___x_2663_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2664_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2);
                    v___x_2665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_x_2602_, v_ks_2661_, v_vs_2662_, v___x_2663_, v___x_2664_);
                    leanh::lean_dec_ref(v_vs_2662_);
                    leanh::lean_dec_ref(v_ks_2661_);
                    return v___x_2665_;
                } else {
                    return v_newNode_2658_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(
    mut v_depth_2673_: usize,
    mut v_keys_2674_: *mut leanh::LeanObject,
    mut v_vals_2675_: *mut leanh::LeanObject,
    mut v_i_2676_: *mut leanh::LeanObject,
    mut v_entries_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: u8 = 0;
    let mut v_k_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u64 = 0;
    let mut v_h_2683_: usize = 0;
    let mut v___x_2684_: usize = 0;
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: usize = 0;
    let mut v___x_2687_: usize = 0;
    let mut v___x_2688_: usize = 0;
    let mut v_h_2689_: usize = 0;
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2678_ = lean_array_get_size(v_keys_2674_);
                v___x_2679_ = lean_nat_dec_lt(v_i_2676_, v___x_2678_);
                if v___x_2679_ == 0 {
                    leanh::lean_dec(v_i_2676_);
                    return v_entries_2677_;
                } else {
                    v_k_2680_ = lean_array_fget_borrowed(v_keys_2674_, v_i_2676_);
                    v_v_2681_ = lean_array_fget_borrowed(v_vals_2675_, v_i_2676_);
                    v___x_2682_ = l_Lean_instHashableFVarId_hash(v_k_2680_);
                    v_h_2683_ = lean_uint64_to_usize(v___x_2682_);
                    v___x_2684_ = 5usize;
                    v___x_2685_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2686_ = 1usize;
                    v___x_2687_ = lean_usize_sub(v_depth_2673_, v___x_2686_);
                    v___x_2688_ = lean_usize_mul(v___x_2684_, v___x_2687_);
                    v_h_2689_ = lean_usize_shift_right(v_h_2683_, v___x_2688_);
                    v___x_2690_ = lean_nat_add(v_i_2676_, v___x_2685_);
                    leanh::lean_dec(v_i_2676_);
                    leanh::lean_inc(v_v_2681_);
                    leanh::lean_inc(v_k_2680_);
                    v___x_2691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_entries_2677_, v_h_2689_, v_depth_2673_, v_k_2680_, v_v_2681_);
                    v_i_2676_ = v___x_2690_;
                    v_entries_2677_ = v___x_2691_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg___boxed(
    mut v_depth_2693_: *mut leanh::LeanObject,
    mut v_keys_2694_: *mut leanh::LeanObject,
    mut v_vals_2695_: *mut leanh::LeanObject,
    mut v_i_2696_: *mut leanh::LeanObject,
    mut v_entries_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2698_: usize = 0;
    let mut v_res_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2698_ = leanh::lean_unbox_usize(v_depth_2693_);
    leanh::lean_dec(v_depth_2693_);
    v_res_2699_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_boxed_2698_, v_keys_2694_, v_vals_2695_, v_i_2696_, v_entries_2697_);
    leanh::lean_dec_ref(v_vals_2695_);
    leanh::lean_dec_ref(v_keys_2694_);
    return v_res_2699_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___boxed(
    mut v_x_2700_: *mut leanh::LeanObject,
    mut v_x_2701_: *mut leanh::LeanObject,
    mut v_x_2702_: *mut leanh::LeanObject,
    mut v_x_2703_: *mut leanh::LeanObject,
    mut v_x_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_29649__boxed_2705_: usize = 0;
    let mut v_x_29650__boxed_2706_: usize = 0;
    let mut v_res_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_29649__boxed_2705_ = leanh::lean_unbox_usize(v_x_2701_);
    leanh::lean_dec(v_x_2701_);
    v_x_29650__boxed_2706_ = leanh::lean_unbox_usize(v_x_2702_);
    leanh::lean_dec(v_x_2702_);
    v_res_2707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_2700_, v_x_29649__boxed_2705_, v_x_29650__boxed_2706_, v_x_2703_, v_x_2704_);
    return v_res_2707_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(
    mut v_x_2708_: *mut leanh::LeanObject,
    mut v_x_2709_: *mut leanh::LeanObject,
    mut v_x_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2711_: u64 = 0;
    let mut v___x_2712_: usize = 0;
    let mut v___x_2713_: usize = 0;
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2711_ = l_Lean_instHashableFVarId_hash(v_x_2709_);
    v___x_2712_ = lean_uint64_to_usize(v___x_2711_);
    v___x_2713_ = 1usize;
    v___x_2714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_2708_, v___x_2712_, v___x_2713_, v_x_2709_, v_x_2710_);
    return v___x_2714_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v_x_2716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: u8 = 0;
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2716_) == 0 {
                    v___x_2717_ = leanh::lean_box(0);
                    return v___x_2717_;
                } else {
                    v_key_2718_ = leanh::lean_ctor_get(v_x_2716_, 0);
                    v_value_2719_ = leanh::lean_ctor_get(v_x_2716_, 1);
                    v_tail_2720_ = leanh::lean_ctor_get(v_x_2716_, 2);
                    v___x_2721_ = l_Lean_ExprStructEq_beq(v_key_2718_, v_a_2715_);
                    if v___x_2721_ == 0 {
                        v_x_2716_ = v_tail_2720_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_2719_);
                        v___x_2723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2723_, 0, v_value_2719_);
                        return v___x_2723_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg___boxed(
    mut v_a_2724_: *mut leanh::LeanObject,
    mut v_x_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2726_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_2724_, v_x_2725_);
    leanh::lean_dec(v_x_2725_);
    leanh::lean_dec_ref(v_a_2724_);
    return v_res_2726_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(
    mut v_m_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: u64 = 0;
    let mut v___x_2732_: u64 = 0;
    let mut v___x_2733_: u64 = 0;
    let mut v_fold_2734_: u64 = 0;
    let mut v___x_2735_: u64 = 0;
    let mut v___x_2736_: u64 = 0;
    let mut v___x_2737_: u64 = 0;
    let mut v___x_2738_: usize = 0;
    let mut v___x_2739_: usize = 0;
    let mut v___x_2740_: usize = 0;
    let mut v___x_2741_: usize = 0;
    let mut v___x_2742_: usize = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2729_ = leanh::lean_ctor_get(v_m_2727_, 1);
    v___x_2730_ = lean_array_get_size(v_buckets_2729_);
    v___x_2731_ = l_Lean_ExprStructEq_hash(v_a_2728_);
    v___x_2732_ = 32u64;
    v___x_2733_ = lean_uint64_shift_right(v___x_2731_, v___x_2732_);
    v_fold_2734_ = lean_uint64_xor(v___x_2731_, v___x_2733_);
    v___x_2735_ = 16u64;
    v___x_2736_ = lean_uint64_shift_right(v_fold_2734_, v___x_2735_);
    v___x_2737_ = lean_uint64_xor(v_fold_2734_, v___x_2736_);
    v___x_2738_ = lean_uint64_to_usize(v___x_2737_);
    v___x_2739_ = lean_usize_of_nat(v___x_2730_);
    v___x_2740_ = 1usize;
    v___x_2741_ = lean_usize_sub(v___x_2739_, v___x_2740_);
    v___x_2742_ = lean_usize_land(v___x_2738_, v___x_2741_);
    v___x_2743_ = lean_array_uget_borrowed(v_buckets_2729_, v___x_2742_);
    v___x_2744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_2728_, v___x_2743_);
    return v___x_2744_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(
    mut v_m_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_2745_, v_a_2746_);
    leanh::lean_dec_ref(v_a_2746_);
    leanh::lean_dec_ref(v_m_2745_);
    return v_res_2747_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(
    mut v_x_2748_: *mut leanh::LeanObject,
    mut v_isExporting_2749_: u8,
    mut v___y_2750_: u8,
    mut v___y_2751_: *mut leanh::LeanObject,
    mut v___y_2752_: *mut leanh::LeanObject,
    mut v___y_2753_: *mut leanh::LeanObject,
    mut v___y_2754_: *mut leanh::LeanObject,
    mut v___y_2755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2759_: u8 = 0;
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_unused_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_a_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v_unused_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_unused_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_unused_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2757_ = lean_st_ref_get(v___y_2755_);
                v_env_2758_ = leanh::lean_ctor_get(v___x_2757_, 0);
                leanh::lean_inc_ref(v_env_2758_);
                leanh::lean_dec(v___x_2757_);
                v_isExporting_2759_ = leanh::lean_ctor_get_uint8(
                    v_env_2758_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_2758_);
                v___x_2760_ = lean_st_ref_take(v___y_2755_);
                v_env_2761_ = leanh::lean_ctor_get(v___x_2760_, 0);
                v_nextMacroScope_2762_ = leanh::lean_ctor_get(v___x_2760_, 1);
                v_ngen_2763_ = leanh::lean_ctor_get(v___x_2760_, 2);
                v_auxDeclNGen_2764_ = leanh::lean_ctor_get(v___x_2760_, 3);
                v_traceState_2765_ = leanh::lean_ctor_get(v___x_2760_, 4);
                v_messages_2766_ = leanh::lean_ctor_get(v___x_2760_, 6);
                v_infoState_2767_ = leanh::lean_ctor_get(v___x_2760_, 7);
                v_snapshotTasks_2768_ = leanh::lean_ctor_get(v___x_2760_, 8);
                v_isSharedCheck_2823_ = (!leanh::lean_is_exclusive(v___x_2760_)) as u8;
                if v_isSharedCheck_2823_ == 0 {
                    v_unused_2824_ = leanh::lean_ctor_get(v___x_2760_, 5);
                    leanh::lean_dec(v_unused_2824_);
                    v___x_2770_ = v___x_2760_;
                    v_isShared_2771_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2768_);
                    leanh::lean_inc(v_infoState_2767_);
                    leanh::lean_inc(v_messages_2766_);
                    leanh::lean_inc(v_traceState_2765_);
                    leanh::lean_inc(v_auxDeclNGen_2764_);
                    leanh::lean_inc(v_ngen_2763_);
                    leanh::lean_inc(v_nextMacroScope_2762_);
                    leanh::lean_inc(v_env_2761_);
                    leanh::lean_dec(v___x_2760_);
                    v___x_2770_ = leanh::lean_box(0);
                    v_isShared_2771_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2772_ = l_Lean_Environment_setExporting(v_env_2761_, v_isExporting_2749_);
                v___x_2773_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
                if v_isShared_2771_ == 0 {
                    leanh::lean_ctor_set(v___x_2770_, 5, v___x_2773_);
                    leanh::lean_ctor_set(v___x_2770_, 0, v___x_2772_);
                    v___x_2775_ = v___x_2770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2822_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_nextMacroScope_2762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_ngen_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_auxDeclNGen_2764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_traceState_2765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 5, v___x_2773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 6, v_messages_2766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 7, v_infoState_2767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 8, v_snapshotTasks_2768_);
                    v___x_2775_ = v_reuseFailAlloc_2822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2776_ = lean_st_ref_set(v___y_2755_, v___x_2775_);
                v___x_2777_ = lean_st_ref_take(v___y_2753_);
                v_mctx_2778_ = leanh::lean_ctor_get(v___x_2777_, 0);
                v_zetaDeltaFVarIds_2779_ = leanh::lean_ctor_get(v___x_2777_, 2);
                v_postponed_2780_ = leanh::lean_ctor_get(v___x_2777_, 3);
                v_diag_2781_ = leanh::lean_ctor_get(v___x_2777_, 4);
                v_isSharedCheck_2820_ = (!leanh::lean_is_exclusive(v___x_2777_)) as u8;
                if v_isSharedCheck_2820_ == 0 {
                    v_unused_2821_ = leanh::lean_ctor_get(v___x_2777_, 1);
                    leanh::lean_dec(v_unused_2821_);
                    v___x_2783_ = v___x_2777_;
                    v_isShared_2784_ = v_isSharedCheck_2820_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2781_);
                    leanh::lean_inc(v_postponed_2780_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2779_);
                    leanh::lean_inc(v_mctx_2778_);
                    leanh::lean_dec(v___x_2777_);
                    v___x_2783_ = leanh::lean_box(0);
                    v_isShared_2784_ = v_isSharedCheck_2820_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2785_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
                if v_isShared_2784_ == 0 {
                    leanh::lean_ctor_set(v___x_2783_, 1, v___x_2785_);
                    v___x_2787_ = v___x_2783_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_mctx_2778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2785_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2819_,
                        2,
                        v_zetaDeltaFVarIds_2779_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_postponed_2780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 4, v_diag_2781_);
                    v___x_2787_ = v_reuseFailAlloc_2819_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2788_ = lean_st_ref_set(v___y_2753_, v___x_2787_);
                v___x_2789_ = leanh::lean_box((v___y_2750_) as usize);
                leanh::lean_inc(v___y_2755_);
                leanh::lean_inc_ref(v___y_2754_);
                leanh::lean_inc(v___y_2753_);
                leanh::lean_inc_ref(v___y_2752_);
                leanh::lean_inc(v___y_2751_);
                v_r_2790_ = leanh::lean_apply_7(
                    v_x_2748_,
                    v___x_2789_,
                    v___y_2751_,
                    v___y_2752_,
                    v___y_2753_,
                    v___y_2754_,
                    v___y_2755_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_2790_) == 0 {
                    v_a_2791_ = leanh::lean_ctor_get(v_r_2790_, 0);
                    v_isSharedCheck_2807_ = (!leanh::lean_is_exclusive(v_r_2790_)) as u8;
                    if v_isSharedCheck_2807_ == 0 {
                        v___x_2793_ = v_r_2790_;
                        v_isShared_2794_ = v_isSharedCheck_2807_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2791_);
                        leanh::lean_dec(v_r_2790_);
                        v___x_2793_ = leanh::lean_box(0);
                        v_isShared_2794_ = v_isSharedCheck_2807_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2808_ = leanh::lean_ctor_get(v_r_2790_, 0);
                    leanh::lean_inc(v_a_2808_);
                    leanh::lean_dec_ref_known(v_r_2790_, 1);
                    v___x_2809_ = leanh::lean_box(0);
                    v___x_2810_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_2755_, v_isExporting_2759_, v___x_2773_, v___y_2753_, v___x_2785_, v___x_2809_);
                    v_isSharedCheck_2817_ = (!leanh::lean_is_exclusive(v___x_2810_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v_unused_2818_ = leanh::lean_ctor_get(v___x_2810_, 0);
                        leanh::lean_dec(v_unused_2818_);
                        v___x_2812_ = v___x_2810_;
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2810_);
                        v___x_2812_ = leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_2791_);
                if v_isShared_2794_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2793_, 1);
                    v___x_2796_ = v___x_2793_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2791_);
                    v___x_2796_ = v_reuseFailAlloc_2806_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2797_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_2755_, v_isExporting_2759_, v___x_2773_, v___y_2753_, v___x_2785_, v___x_2796_);
                leanh::lean_dec_ref(v___x_2796_);
                v_isSharedCheck_2804_ = (!leanh::lean_is_exclusive(v___x_2797_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v_unused_2805_ = leanh::lean_ctor_get(v___x_2797_, 0);
                    leanh::lean_dec(v_unused_2805_);
                    v___x_2799_ = v___x_2797_;
                    v_isShared_2800_ = v_isSharedCheck_2804_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2797_);
                    v___x_2799_ = leanh::lean_box(0);
                    v_isShared_2800_ = v_isSharedCheck_2804_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2800_ == 0 {
                    leanh::lean_ctor_set(v___x_2799_, 0, v_a_2791_);
                    v___x_2802_ = v___x_2799_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2791_);
                    v___x_2802_ = v_reuseFailAlloc_2803_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2802_;
            }
            9 => {
                if v_isShared_2813_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2812_, 1);
                    leanh::lean_ctor_set(v___x_2812_, 0, v_a_2808_);
                    v___x_2815_ = v___x_2812_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2808_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg___boxed(
    mut v_x_2825_: *mut leanh::LeanObject,
    mut v_isExporting_2826_: *mut leanh::LeanObject,
    mut v___y_2827_: *mut leanh::LeanObject,
    mut v___y_2828_: *mut leanh::LeanObject,
    mut v___y_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
    mut v___y_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2834_: u8 = 0;
    let mut v___y_29885__boxed_2835_: u8 = 0;
    let mut v_res_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2834_ = (leanh::lean_unbox(v_isExporting_2826_) as u8);
    v___y_29885__boxed_2835_ = (leanh::lean_unbox(v___y_2827_) as u8);
    v_res_2836_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_2825_, v_isExporting_boxed_2834_, v___y_29885__boxed_2835_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
    leanh::lean_dec(v___y_2832_);
    leanh::lean_dec_ref(v___y_2831_);
    leanh::lean_dec(v___y_2830_);
    leanh::lean_dec_ref(v___y_2829_);
    leanh::lean_dec(v___y_2828_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(
    mut v_x_2837_: *mut leanh::LeanObject,
    mut v_when_2838_: u8,
    mut v___y_2839_: u8,
    mut v___y_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_2838_ == 0 {
        let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2846_ = leanh::lean_box((v___y_2839_) as usize);
        leanh::lean_inc(v___y_2844_);
        leanh::lean_inc_ref(v___y_2843_);
        leanh::lean_inc(v___y_2842_);
        leanh::lean_inc_ref(v___y_2841_);
        leanh::lean_inc(v___y_2840_);
        v___x_2847_ = leanh::lean_apply_7(
            v_x_2837_,
            v___x_2846_,
            v___y_2840_,
            v___y_2841_,
            v___y_2842_,
            v___y_2843_,
            v___y_2844_,
            leanh::lean_box(0),
        );
        return v___x_2847_;
    } else {
        let mut v___x_2848_: u8 = 0;
        let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2848_ = 0;
        v___x_2849_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_2837_, v___x_2848_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
        return v___x_2849_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(
    mut v_x_2850_: *mut leanh::LeanObject,
    mut v_when_2851_: *mut leanh::LeanObject,
    mut v___y_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_2859_: u8 = 0;
    let mut v___y_30018__boxed_2860_: u8 = 0;
    let mut v_res_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_2859_ = (leanh::lean_unbox(v_when_2851_) as u8);
    v___y_30018__boxed_2860_ = (leanh::lean_unbox(v___y_2852_) as u8);
    v_res_2861_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_2850_, v_when_boxed_2859_, v___y_30018__boxed_2860_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
    leanh::lean_dec(v___y_2857_);
    leanh::lean_dec_ref(v___y_2856_);
    leanh::lean_dec(v___y_2855_);
    leanh::lean_dec_ref(v___y_2854_);
    leanh::lean_dec(v___y_2853_);
    return v_res_2861_;
}
pub unsafe fn l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(
    mut v_proof_2862_: *mut leanh::LeanObject,
    mut v___y_2863_: u8,
    mut v___y_2864_: *mut leanh::LeanObject,
    mut v___y_2865_: *mut leanh::LeanObject,
    mut v___y_2866_: *mut leanh::LeanObject,
    mut v___y_2867_: *mut leanh::LeanObject,
    mut v___y_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2868_);
    leanh::lean_inc_ref(v___y_2867_);
    leanh::lean_inc(v___y_2866_);
    leanh::lean_inc_ref(v___y_2865_);
    v___x_2870_ = lean_infer_type(
        v_proof_2862_,
        v___y_2865_,
        v___y_2866_,
        v___y_2867_,
        v___y_2868_,
    );
    return v___x_2870_;
}
pub unsafe fn l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed(
    mut v_proof_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_30047__boxed_2879_: u8 = 0;
    let mut v_res_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_30047__boxed_2879_ = (leanh::lean_unbox(v___y_2872_) as u8);
    v_res_2880_ =
        l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(
            v_proof_2871_,
            v___y_30047__boxed_2879_,
            v___y_2873_,
            v___y_2874_,
            v___y_2875_,
            v___y_2876_,
            v___y_2877_,
        );
    leanh::lean_dec(v___y_2877_);
    leanh::lean_dec_ref(v___y_2876_);
    leanh::lean_dec(v___y_2875_);
    leanh::lean_dec_ref(v___y_2874_);
    leanh::lean_dec(v___y_2873_);
    return v_res_2880_;
}
pub unsafe fn l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(
    mut v_proof_2881_: *mut leanh::LeanObject,
    mut v_cache_2882_: u8,
    mut v_postprocessType_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: u8,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
    mut v___y_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2903_: u8 = 0;
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_proof_2881_);
                v___f_2891_ = leanh::lean_alloc_closure(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2891_, 0, v_proof_2881_);
                v___x_2892_ = 1;
                v___x_2893_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v___f_2891_, v___x_2892_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
                if leanh::lean_obj_tag(v___x_2893_) == 0 {
                    v_a_2894_ = leanh::lean_ctor_get(v___x_2893_, 0);
                    leanh::lean_inc(v_a_2894_);
                    leanh::lean_dec_ref_known(v___x_2893_, 1);
                    v___x_2895_ = l_Lean_Core_betaReduce(v_a_2894_, v___y_2888_, v___y_2889_);
                    if leanh::lean_obj_tag(v___x_2895_) == 0 {
                        v_a_2896_ = leanh::lean_ctor_get(v___x_2895_, 0);
                        leanh::lean_inc(v_a_2896_);
                        leanh::lean_dec_ref_known(v___x_2895_, 1);
                        v___x_2897_ = l_Lean_Meta_zetaReduce(
                            v_a_2896_,
                            v___x_2892_,
                            v___x_2892_,
                            v___x_2892_,
                            v___y_2886_,
                            v___y_2887_,
                            v___y_2888_,
                            v___y_2889_,
                        );
                        if leanh::lean_obj_tag(v___x_2897_) == 0 {
                            v_a_2898_ = leanh::lean_ctor_get(v___x_2897_, 0);
                            leanh::lean_inc(v_a_2898_);
                            leanh::lean_dec_ref_known(v___x_2897_, 1);
                            v___x_2899_ = leanh::lean_box((v___y_2884_) as usize);
                            leanh::lean_inc(v___y_2889_);
                            leanh::lean_inc_ref(v___y_2888_);
                            leanh::lean_inc(v___y_2887_);
                            leanh::lean_inc_ref(v___y_2886_);
                            leanh::lean_inc(v___y_2885_);
                            v___x_2900_ = leanh::lean_apply_8(
                                v_postprocessType_2883_,
                                v_a_2898_,
                                v___x_2899_,
                                v___y_2885_,
                                v___y_2886_,
                                v___y_2887_,
                                v___y_2888_,
                                v___y_2889_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_2900_) == 0 {
                                v_a_2901_ = leanh::lean_ctor_get(v___x_2900_, 0);
                                leanh::lean_inc(v_a_2901_);
                                leanh::lean_dec_ref_known(v___x_2900_, 1);
                                if v_cache_2882_ == 0 {
                                    v___y_2903_ = v_cache_2882_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2906_ = l_Lean_Expr_hasSorry(v_proof_2881_);
                                    if v___x_2906_ == 0 {
                                        v___y_2903_ = v_cache_2882_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_2907_ = 0;
                                        v___y_2903_ = v___x_2907_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_proof_2881_);
                                return v___x_2900_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_postprocessType_2883_);
                            leanh::lean_dec_ref(v_proof_2881_);
                            return v___x_2897_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_postprocessType_2883_);
                        leanh::lean_dec_ref(v_proof_2881_);
                        return v___x_2895_;
                    }
                } else {
                    leanh::lean_dec_ref(v_postprocessType_2883_);
                    leanh::lean_dec_ref(v_proof_2881_);
                    return v___x_2893_;
                }
            }
            1 => {
                v___x_2904_ = leanh::lean_box(0);
                v___x_2905_ = l_Lean_Meta_mkAuxTheorem(
                    v_a_2901_,
                    v_proof_2881_,
                    v___x_2892_,
                    v___x_2904_,
                    v___y_2903_,
                    v___y_2886_,
                    v___y_2887_,
                    v___y_2888_,
                    v___y_2889_,
                );
                return v___x_2905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(
    mut v_proof_2908_: *mut leanh::LeanObject,
    mut v_cache_2909_: *mut leanh::LeanObject,
    mut v_postprocessType_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
    mut v___y_2913_: *mut leanh::LeanObject,
    mut v___y_2914_: *mut leanh::LeanObject,
    mut v___y_2915_: *mut leanh::LeanObject,
    mut v___y_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_boxed_2918_: u8 = 0;
    let mut v___y_30070__boxed_2919_: u8 = 0;
    let mut v_res_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cache_boxed_2918_ = (leanh::lean_unbox(v_cache_2909_) as u8);
    v___y_30070__boxed_2919_ = (leanh::lean_unbox(v___y_2911_) as u8);
    v_res_2920_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(
        v_proof_2908_,
        v_cache_boxed_2918_,
        v_postprocessType_2910_,
        v___y_30070__boxed_2919_,
        v___y_2912_,
        v___y_2913_,
        v___y_2914_,
        v___y_2915_,
        v___y_2916_,
    );
    leanh::lean_dec(v___y_2916_);
    leanh::lean_dec_ref(v___y_2915_);
    leanh::lean_dec(v___y_2914_);
    leanh::lean_dec_ref(v___y_2913_);
    leanh::lean_dec(v___y_2912_);
    return v_res_2920_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(
    mut v_x_2921_: *mut leanh::LeanObject,
    mut v_x_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: u64 = 0;
    let mut v___x_2931_: u64 = 0;
    let mut v___x_2932_: u64 = 0;
    let mut v_fold_2933_: u64 = 0;
    let mut v___x_2934_: u64 = 0;
    let mut v___x_2935_: u64 = 0;
    let mut v___x_2936_: u64 = 0;
    let mut v___x_2937_: usize = 0;
    let mut v___x_2938_: usize = 0;
    let mut v___x_2939_: usize = 0;
    let mut v___x_2940_: usize = 0;
    let mut v___x_2941_: usize = 0;
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2922_) == 0 {
                    return v_x_2921_;
                } else {
                    v_key_2923_ = leanh::lean_ctor_get(v_x_2922_, 0);
                    v_value_2924_ = leanh::lean_ctor_get(v_x_2922_, 1);
                    v_tail_2925_ = leanh::lean_ctor_get(v_x_2922_, 2);
                    v_isSharedCheck_2948_ = (!leanh::lean_is_exclusive(v_x_2922_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v___x_2927_ = v_x_2922_;
                        v_isShared_2928_ = v_isSharedCheck_2948_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2925_);
                        leanh::lean_inc(v_value_2924_);
                        leanh::lean_inc(v_key_2923_);
                        leanh::lean_dec(v_x_2922_);
                        v___x_2927_ = leanh::lean_box(0);
                        v_isShared_2928_ = v_isSharedCheck_2948_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2929_ = lean_array_get_size(v_x_2921_);
                v___x_2930_ = l_Lean_ExprStructEq_hash(v_key_2923_);
                v___x_2931_ = 32u64;
                v___x_2932_ = lean_uint64_shift_right(v___x_2930_, v___x_2931_);
                v_fold_2933_ = lean_uint64_xor(v___x_2930_, v___x_2932_);
                v___x_2934_ = 16u64;
                v___x_2935_ = lean_uint64_shift_right(v_fold_2933_, v___x_2934_);
                v___x_2936_ = lean_uint64_xor(v_fold_2933_, v___x_2935_);
                v___x_2937_ = lean_uint64_to_usize(v___x_2936_);
                v___x_2938_ = lean_usize_of_nat(v___x_2929_);
                v___x_2939_ = 1usize;
                v___x_2940_ = lean_usize_sub(v___x_2938_, v___x_2939_);
                v___x_2941_ = lean_usize_land(v___x_2937_, v___x_2940_);
                v___x_2942_ = lean_array_uget_borrowed(v_x_2921_, v___x_2941_);
                leanh::lean_inc(v___x_2942_);
                if v_isShared_2928_ == 0 {
                    leanh::lean_ctor_set(v___x_2927_, 2, v___x_2942_);
                    v___x_2944_ = v___x_2927_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_key_2923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_value_2924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 2, v___x_2942_);
                    v___x_2944_ = v_reuseFailAlloc_2947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2945_ = lean_array_uset(v_x_2921_, v___x_2941_, v___x_2944_);
                v_x_2921_ = v___x_2945_;
                v_x_2922_ = v_tail_2925_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(
    mut v_i_2949_: *mut leanh::LeanObject,
    mut v_source_2950_: *mut leanh::LeanObject,
    mut v_target_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: u8 = 0;
    let mut v_es_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2952_ = lean_array_get_size(v_source_2950_);
                v___x_2953_ = lean_nat_dec_lt(v_i_2949_, v___x_2952_);
                if v___x_2953_ == 0 {
                    leanh::lean_dec_ref(v_source_2950_);
                    leanh::lean_dec(v_i_2949_);
                    return v_target_2951_;
                } else {
                    v_es_2954_ = lean_array_fget(v_source_2950_, v_i_2949_);
                    v___x_2955_ = leanh::lean_box(0);
                    v_source_2956_ = lean_array_fset(v_source_2950_, v_i_2949_, v___x_2955_);
                    v_target_2957_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_target_2951_, v_es_2954_);
                    v___x_2958_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2959_ = lean_nat_add(v_i_2949_, v___x_2958_);
                    leanh::lean_dec(v_i_2949_);
                    v_i_2949_ = v___x_2959_;
                    v_source_2950_ = v_source_2956_;
                    v_target_2951_ = v_target_2957_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(
    mut v_data_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2962_ = lean_array_get_size(v_data_2961_);
    v___x_2963_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2964_ = lean_nat_mul(v___x_2962_, v___x_2963_);
    v___x_2965_ = leanh::lean_unsigned_to_nat(0);
    v___x_2966_ = leanh::lean_box(0);
    v___x_2967_ = lean_mk_array(v_nbuckets_2964_, v___x_2966_);
    v___x_2968_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v___x_2965_, v_data_2961_, v___x_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_x_2970_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2971_: u8 = 0;
    let mut v_key_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2970_) == 0 {
                    v___x_2971_ = 0;
                    return v___x_2971_;
                } else {
                    v_key_2972_ = leanh::lean_ctor_get(v_x_2970_, 0);
                    v_tail_2973_ = leanh::lean_ctor_get(v_x_2970_, 2);
                    v___x_2974_ = l_Lean_ExprStructEq_beq(v_key_2972_, v_a_2969_);
                    if v___x_2974_ == 0 {
                        v_x_2970_ = v_tail_2973_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2974_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v_x_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2978_: u8 = 0;
    let mut v_r_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_2976_, v_x_2977_);
    leanh::lean_dec(v_x_2977_);
    leanh::lean_dec_ref(v_a_2976_);
    v_r_2979_ = leanh::lean_box((v_res_2978_) as usize);
    return v_r_2979_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(
    mut v_a_2980_: *mut leanh::LeanObject,
    mut v_b_2981_: *mut leanh::LeanObject,
    mut v_x_2982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v___x_2989_: u8 = 0;
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2982_) == 0 {
                    leanh::lean_dec(v_b_2981_);
                    leanh::lean_dec_ref(v_a_2980_);
                    return v_x_2982_;
                } else {
                    v_key_2983_ = leanh::lean_ctor_get(v_x_2982_, 0);
                    v_value_2984_ = leanh::lean_ctor_get(v_x_2982_, 1);
                    v_tail_2985_ = leanh::lean_ctor_get(v_x_2982_, 2);
                    v_isSharedCheck_2997_ = (!leanh::lean_is_exclusive(v_x_2982_)) as u8;
                    if v_isSharedCheck_2997_ == 0 {
                        v___x_2987_ = v_x_2982_;
                        v_isShared_2988_ = v_isSharedCheck_2997_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2985_);
                        leanh::lean_inc(v_value_2984_);
                        leanh::lean_inc(v_key_2983_);
                        leanh::lean_dec(v_x_2982_);
                        v___x_2987_ = leanh::lean_box(0);
                        v_isShared_2988_ = v_isSharedCheck_2997_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2989_ = l_Lean_ExprStructEq_beq(v_key_2983_, v_a_2980_);
                if v___x_2989_ == 0 {
                    v___x_2990_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_2980_, v_b_2981_, v_tail_2985_);
                    if v_isShared_2988_ == 0 {
                        leanh::lean_ctor_set(v___x_2987_, 2, v___x_2990_);
                        v___x_2992_ = v___x_2987_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_key_2983_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_value_2984_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 2, v___x_2990_);
                        v___x_2992_ = v_reuseFailAlloc_2993_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_2984_);
                    leanh::lean_dec(v_key_2983_);
                    if v_isShared_2988_ == 0 {
                        leanh::lean_ctor_set(v___x_2987_, 1, v_b_2981_);
                        leanh::lean_ctor_set(v___x_2987_, 0, v_a_2980_);
                        v___x_2995_ = v___x_2987_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2996_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2980_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_b_2981_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 2, v_tail_2985_);
                        v___x_2995_ = v_reuseFailAlloc_2996_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2992_;
            }
            3 => {
                return v___x_2995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(
    mut v_m_2998_: *mut leanh::LeanObject,
    mut v_a_2999_: *mut leanh::LeanObject,
    mut v_b_3000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u64 = 0;
    let mut v___x_3008_: u64 = 0;
    let mut v___x_3009_: u64 = 0;
    let mut v_fold_3010_: u64 = 0;
    let mut v___x_3011_: u64 = 0;
    let mut v___x_3012_: u64 = 0;
    let mut v___x_3013_: u64 = 0;
    let mut v___x_3014_: usize = 0;
    let mut v___x_3015_: usize = 0;
    let mut v___x_3016_: usize = 0;
    let mut v___x_3017_: usize = 0;
    let mut v___x_3018_: usize = 0;
    let mut v_bkt_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: u8 = 0;
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: u8 = 0;
    let mut v_val_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3001_ = leanh::lean_ctor_get(v_m_2998_, 0);
                v_buckets_3002_ = leanh::lean_ctor_get(v_m_2998_, 1);
                v_isSharedCheck_3045_ = (!leanh::lean_is_exclusive(v_m_2998_)) as u8;
                if v_isSharedCheck_3045_ == 0 {
                    v___x_3004_ = v_m_2998_;
                    v_isShared_3005_ = v_isSharedCheck_3045_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3002_);
                    leanh::lean_inc(v_size_3001_);
                    leanh::lean_dec(v_m_2998_);
                    v___x_3004_ = leanh::lean_box(0);
                    v_isShared_3005_ = v_isSharedCheck_3045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3006_ = lean_array_get_size(v_buckets_3002_);
                v___x_3007_ = l_Lean_ExprStructEq_hash(v_a_2999_);
                v___x_3008_ = 32u64;
                v___x_3009_ = lean_uint64_shift_right(v___x_3007_, v___x_3008_);
                v_fold_3010_ = lean_uint64_xor(v___x_3007_, v___x_3009_);
                v___x_3011_ = 16u64;
                v___x_3012_ = lean_uint64_shift_right(v_fold_3010_, v___x_3011_);
                v___x_3013_ = lean_uint64_xor(v_fold_3010_, v___x_3012_);
                v___x_3014_ = lean_uint64_to_usize(v___x_3013_);
                v___x_3015_ = lean_usize_of_nat(v___x_3006_);
                v___x_3016_ = 1usize;
                v___x_3017_ = lean_usize_sub(v___x_3015_, v___x_3016_);
                v___x_3018_ = lean_usize_land(v___x_3014_, v___x_3017_);
                v_bkt_3019_ = lean_array_uget_borrowed(v_buckets_3002_, v___x_3018_);
                v___x_3020_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_2999_, v_bkt_3019_);
                if v___x_3020_ == 0 {
                    v___x_3021_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3022_ = lean_nat_add(v_size_3001_, v___x_3021_);
                    leanh::lean_dec(v_size_3001_);
                    leanh::lean_inc(v_bkt_3019_);
                    v___x_3023_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3023_, 0, v_a_2999_);
                    leanh::lean_ctor_set(v___x_3023_, 1, v_b_3000_);
                    leanh::lean_ctor_set(v___x_3023_, 2, v_bkt_3019_);
                    v_buckets_x27_3024_ =
                        lean_array_uset(v_buckets_3002_, v___x_3018_, v___x_3023_);
                    v___x_3025_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3026_ = lean_nat_mul(v_size_x27_3022_, v___x_3025_);
                    v___x_3027_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3028_ = lean_nat_div(v___x_3026_, v___x_3027_);
                    leanh::lean_dec(v___x_3026_);
                    v___x_3029_ = lean_array_get_size(v_buckets_x27_3024_);
                    v___x_3030_ = lean_nat_dec_le(v___x_3028_, v___x_3029_);
                    leanh::lean_dec(v___x_3028_);
                    if v___x_3030_ == 0 {
                        v_val_3031_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_buckets_x27_3024_);
                        if v_isShared_3005_ == 0 {
                            leanh::lean_ctor_set(v___x_3004_, 1, v_val_3031_);
                            leanh::lean_ctor_set(v___x_3004_, 0, v_size_x27_3022_);
                            v___x_3033_ = v___x_3004_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3034_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3034_,
                                0,
                                v_size_x27_3022_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_val_3031_);
                            v___x_3033_ = v_reuseFailAlloc_3034_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3005_ == 0 {
                            leanh::lean_ctor_set(v___x_3004_, 1, v_buckets_x27_3024_);
                            leanh::lean_ctor_set(v___x_3004_, 0, v_size_x27_3022_);
                            v___x_3036_ = v___x_3004_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3037_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3037_,
                                0,
                                v_size_x27_3022_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3037_,
                                1,
                                v_buckets_x27_3024_,
                            );
                            v___x_3036_ = v_reuseFailAlloc_3037_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3019_);
                    v___x_3038_ = leanh::lean_box(0);
                    v_buckets_x27_3039_ =
                        lean_array_uset(v_buckets_3002_, v___x_3018_, v___x_3038_);
                    v___x_3040_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_2999_, v_b_3000_, v_bkt_3019_);
                    v___x_3041_ = lean_array_uset(v_buckets_x27_3039_, v___x_3018_, v___x_3040_);
                    if v_isShared_3005_ == 0 {
                        leanh::lean_ctor_set(v___x_3004_, 1, v___x_3041_);
                        v___x_3043_ = v___x_3004_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3044_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_size_3001_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3041_);
                        v___x_3043_ = v_reuseFailAlloc_3044_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3033_;
            }
            3 => {
                return v___x_3036_;
            }
            4 => {
                return v___x_3043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___boxed(
    mut v_e_3047_: *mut leanh::LeanObject,
    mut v_a_3048_: *mut leanh::LeanObject,
    mut v_a_3049_: *mut leanh::LeanObject,
    mut v_a_3050_: *mut leanh::LeanObject,
    mut v_a_3051_: *mut leanh::LeanObject,
    mut v_a_3052_: *mut leanh::LeanObject,
    mut v_a_3053_: *mut leanh::LeanObject,
    mut v_a_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_3055_: u8 = 0;
    let mut v_res_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3055_ = (leanh::lean_unbox(v_a_3048_) as u8);
    v_res_3056_ = l_Lean_Meta_AbstractNestedProofs_visit(
        v_e_3047_,
        v_a_boxed_3055_,
        v_a_3049_,
        v_a_3050_,
        v_a_3051_,
        v_a_3052_,
        v_a_3053_,
    );
    leanh::lean_dec(v_a_3053_);
    leanh::lean_dec_ref(v_a_3052_);
    leanh::lean_dec(v_a_3051_);
    leanh::lean_dec_ref(v_a_3050_);
    leanh::lean_dec(v_a_3049_);
    return v_res_3056_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(
    mut v_as_3057_: *mut leanh::LeanObject,
    mut v_sz_3058_: usize,
    mut v_i_3059_: usize,
    mut v_b_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: u8,
    mut v___y_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
    mut v___y_3064_: *mut leanh::LeanObject,
    mut v___y_3065_: *mut leanh::LeanObject,
    mut v___y_3066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___y_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: u8 = 0;
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localDecl_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIdToDecl_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclToFullName_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3109_: u8 = 0;
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_a_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut v_a_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3082_ = lean_usize_dec_lt(v_i_3059_, v_sz_3058_);
                if v___x_3082_ == 0 {
                    v___x_3083_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3083_, 0, v_b_3060_);
                    return v___x_3083_;
                } else {
                    v_a_3084_ = lean_array_uget_borrowed(v_as_3057_, v_i_3059_);
                    v___x_3085_ = l_Lean_Expr_fvarId_x21(v_a_3084_);
                    leanh::lean_inc(v___x_3085_);
                    v___x_3095_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_3085_,
                        v___y_3063_,
                        v___y_3065_,
                        v___y_3066_,
                    );
                    if leanh::lean_obj_tag(v___x_3095_) == 0 {
                        v_a_3096_ = leanh::lean_ctor_get(v___x_3095_, 0);
                        leanh::lean_inc(v_a_3096_);
                        leanh::lean_dec_ref_known(v___x_3095_, 1);
                        v___x_3097_ = l_Lean_LocalDecl_type(v_a_3096_);
                        v___x_3098_ = l_Lean_Meta_AbstractNestedProofs_visit(
                            v___x_3097_,
                            v___y_3061_,
                            v___y_3062_,
                            v___y_3063_,
                            v___y_3064_,
                            v___y_3065_,
                            v___y_3066_,
                        );
                        if leanh::lean_obj_tag(v___x_3098_) == 0 {
                            v_a_3099_ = leanh::lean_ctor_get(v___x_3098_, 0);
                            leanh::lean_inc(v_a_3099_);
                            leanh::lean_dec_ref_known(v___x_3098_, 1);
                            v___x_3100_ = l_Lean_LocalDecl_setType(v_a_3096_, v_a_3099_);
                            v___x_3101_ = l_Lean_LocalDecl_value_x3f(v___x_3100_, v___x_3082_);
                            if leanh::lean_obj_tag(v___x_3101_) == 0 {
                                v_localDecl_3087_ = v___x_3100_;
                                state = 3;
                                continue;
                            } else {
                                v_val_3102_ = leanh::lean_ctor_get(v___x_3101_, 0);
                                leanh::lean_inc(v_val_3102_);
                                leanh::lean_dec_ref_known(v___x_3101_, 1);
                                v___x_3103_ = l_Lean_Meta_AbstractNestedProofs_visit(
                                    v_val_3102_,
                                    v___y_3061_,
                                    v___y_3062_,
                                    v___y_3063_,
                                    v___y_3064_,
                                    v___y_3065_,
                                    v___y_3066_,
                                );
                                if leanh::lean_obj_tag(v___x_3103_) == 0 {
                                    v_a_3104_ = leanh::lean_ctor_get(v___x_3103_, 0);
                                    leanh::lean_inc(v_a_3104_);
                                    leanh::lean_dec_ref_known(v___x_3103_, 1);
                                    v___x_3105_ = l_Lean_LocalDecl_setValue(v___x_3100_, v_a_3104_);
                                    v_localDecl_3087_ = v___x_3105_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___x_3100_);
                                    leanh::lean_dec(v___x_3085_);
                                    leanh::lean_dec_ref(v_b_3060_);
                                    v_a_3106_ = leanh::lean_ctor_get(v___x_3103_, 0);
                                    v_isSharedCheck_3113_ =
                                        (!leanh::lean_is_exclusive(v___x_3103_)) as u8;
                                    if v_isSharedCheck_3113_ == 0 {
                                        v___x_3108_ = v___x_3103_;
                                        v_isShared_3109_ = v_isSharedCheck_3113_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3106_);
                                        leanh::lean_dec(v___x_3103_);
                                        v___x_3108_ = leanh::lean_box(0);
                                        v_isShared_3109_ = v_isSharedCheck_3113_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_3096_);
                            leanh::lean_dec(v___x_3085_);
                            leanh::lean_dec_ref(v_b_3060_);
                            v_a_3114_ = leanh::lean_ctor_get(v___x_3098_, 0);
                            v_isSharedCheck_3121_ =
                                (!leanh::lean_is_exclusive(v___x_3098_)) as u8;
                            if v_isSharedCheck_3121_ == 0 {
                                v___x_3116_ = v___x_3098_;
                                v_isShared_3117_ = v_isSharedCheck_3121_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3114_);
                                leanh::lean_dec(v___x_3098_);
                                v___x_3116_ = leanh::lean_box(0);
                                v_isShared_3117_ = v_isSharedCheck_3121_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3085_);
                        leanh::lean_dec_ref(v_b_3060_);
                        v_a_3122_ = leanh::lean_ctor_get(v___x_3095_, 0);
                        v_isSharedCheck_3129_ =
                            (!leanh::lean_is_exclusive(v___x_3095_)) as u8;
                        if v_isSharedCheck_3129_ == 0 {
                            v___x_3124_ = v___x_3095_;
                            v_isShared_3125_ = v_isSharedCheck_3129_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3122_);
                            leanh::lean_dec(v___x_3095_);
                            v___x_3124_ = leanh::lean_box(0);
                            v_isShared_3125_ = v_isSharedCheck_3129_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3070_ = 1usize;
                v___x_3071_ = lean_usize_add(v_i_3059_, v___x_3070_);
                v_i_3059_ = v___x_3071_;
                v_b_3060_ = v_a_3069_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3079_, 0, v___y_3077_);
                v___x_3080_ =
                    l_Lean_PersistentArray_set___redArg(v___y_3076_, v___y_3078_, v___x_3079_);
                leanh::lean_dec(v___y_3078_);
                v___x_3081_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3081_, 0, v___y_3075_);
                leanh::lean_ctor_set(v___x_3081_, 1, v___x_3080_);
                leanh::lean_ctor_set(v___x_3081_, 2, v___y_3074_);
                v_a_3069_ = v___x_3081_;
                state = 1;
                continue;
            }
            3 => {
                v_fvarIdToDecl_3088_ = leanh::lean_ctor_get(v_b_3060_, 0);
                v_decls_3089_ = leanh::lean_ctor_get(v_b_3060_, 1);
                v_auxDeclToFullName_3090_ = leanh::lean_ctor_get(v_b_3060_, 2);
                leanh::lean_inc_ref(v_b_3060_);
                v___x_3091_ = lean_local_ctx_find(v_b_3060_, v___x_3085_);
                if leanh::lean_obj_tag(v___x_3091_) == 0 {
                    leanh::lean_dec_ref(v_localDecl_3087_);
                    v_a_3069_ = v_b_3060_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_auxDeclToFullName_3090_);
                    leanh::lean_inc_ref(v_decls_3089_);
                    leanh::lean_inc_ref(v_fvarIdToDecl_3088_);
                    leanh::lean_dec_ref_known(v___x_3091_, 1);
                    leanh::lean_dec_ref(v_b_3060_);
                    v_index_3092_ = leanh::lean_ctor_get(v_localDecl_3087_, 0);
                    leanh::lean_inc(v_index_3092_);
                    v_fvarId_3093_ = leanh::lean_ctor_get(v_localDecl_3087_, 1);
                    leanh::lean_inc_ref(v_localDecl_3087_);
                    leanh::lean_inc(v_fvarId_3093_);
                    v___x_3094_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_fvarIdToDecl_3088_, v_fvarId_3093_, v_localDecl_3087_);
                    v___y_3074_ = v_auxDeclToFullName_3090_;
                    v___y_3075_ = v___x_3094_;
                    v___y_3076_ = v_decls_3089_;
                    v___y_3077_ = v_localDecl_3087_;
                    v___y_3078_ = v_index_3092_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_3109_ == 0 {
                    v___x_3111_ = v___x_3108_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
                    v___x_3111_ = v_reuseFailAlloc_3112_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3111_;
            }
            6 => {
                if v_isShared_3117_ == 0 {
                    v___x_3119_ = v___x_3116_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3120_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
                    v___x_3119_ = v_reuseFailAlloc_3120_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3119_;
            }
            8 => {
                if v_isShared_3125_ == 0 {
                    v___x_3127_ = v___x_3124_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
                    v___x_3127_ = v_reuseFailAlloc_3128_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__0(
    mut v_xs_3130_: *mut leanh::LeanObject,
    mut v_k_3131_: *mut leanh::LeanObject,
    mut v___y_3132_: u8,
    mut v___y_3133_: *mut leanh::LeanObject,
    mut v___y_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3141_: usize = 0;
    let mut v___x_3142_: usize = 0;
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3139_ = leanh::lean_ctor_get(v___y_3134_, 2);
                v_localInstances_3140_ = leanh::lean_ctor_get(v___y_3134_, 3);
                v_sz_3141_ = lean_array_size(v_xs_3130_);
                v___x_3142_ = 0usize;
                leanh::lean_inc_ref(v_lctx_3139_);
                v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_xs_3130_, v_sz_3141_, v___x_3142_, v_lctx_3139_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
                if leanh::lean_obj_tag(v___x_3143_) == 0 {
                    v_a_3144_ = leanh::lean_ctor_get(v___x_3143_, 0);
                    leanh::lean_inc(v_a_3144_);
                    leanh::lean_dec_ref_known(v___x_3143_, 1);
                    leanh::lean_inc_ref(v_localInstances_3140_);
                    v___x_3145_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_a_3144_, v_localInstances_3140_, v_k_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
                    return v___x_3145_;
                } else {
                    leanh::lean_dec_ref(v_k_3131_);
                    v_a_3146_ = leanh::lean_ctor_get(v___x_3143_, 0);
                    v_isSharedCheck_3153_ = (!leanh::lean_is_exclusive(v___x_3143_)) as u8;
                    if v_isSharedCheck_3153_ == 0 {
                        v___x_3148_ = v___x_3143_;
                        v_isShared_3149_ = v_isSharedCheck_3153_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3146_);
                        leanh::lean_dec(v___x_3143_);
                        v___x_3148_ = leanh::lean_box(0);
                        v_isShared_3149_ = v_isSharedCheck_3153_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3149_ == 0 {
                    v___x_3151_ = v___x_3148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3152_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
                    v___x_3151_ = v_reuseFailAlloc_3152_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(
    mut v_xs_3154_: *mut leanh::LeanObject,
    mut v_k_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_30385__boxed_3163_: u8 = 0;
    let mut v_res_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_30385__boxed_3163_ = (leanh::lean_unbox(v___y_3156_) as u8);
    v_res_3164_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(
        v_xs_3154_,
        v_k_3155_,
        v___y_30385__boxed_3163_,
        v___y_3157_,
        v___y_3158_,
        v___y_3159_,
        v___y_3160_,
        v___y_3161_,
    );
    leanh::lean_dec(v___y_3161_);
    leanh::lean_dec_ref(v___y_3160_);
    leanh::lean_dec(v___y_3159_);
    leanh::lean_dec_ref(v___y_3158_);
    leanh::lean_dec(v___y_3157_);
    leanh::lean_dec_ref(v_xs_3154_);
    return v_res_3164_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(
    mut v___y_3165_: *mut leanh::LeanObject,
    mut v___f_3166_: *mut leanh::LeanObject,
    mut v_xs_3167_: *mut leanh::LeanObject,
    mut v_b_3168_: *mut leanh::LeanObject,
    mut v___y_3169_: *mut leanh::LeanObject,
    mut v___y_3170_: *mut leanh::LeanObject,
    mut v___y_3171_: *mut leanh::LeanObject,
    mut v___y_3172_: *mut leanh::LeanObject,
    mut v___y_3173_: *mut leanh::LeanObject,
    mut v___y_3174_: *mut leanh::LeanObject,
    mut v___y_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_30335__boxed_3176_: u8 = 0;
    let mut v___y_30337__boxed_3177_: u8 = 0;
    let mut v_res_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_30335__boxed_3176_ = (leanh::lean_unbox(v___y_3165_) as u8);
    v___y_30337__boxed_3177_ = (leanh::lean_unbox(v___y_3169_) as u8);
    v_res_3178_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(
        v___y_30335__boxed_3176_,
        v___f_3166_,
        v_xs_3167_,
        v_b_3168_,
        v___y_30337__boxed_3177_,
        v___y_3170_,
        v___y_3171_,
        v___y_3172_,
        v___y_3173_,
        v___y_3174_,
    );
    leanh::lean_dec(v___y_3174_);
    leanh::lean_dec_ref(v___y_3173_);
    leanh::lean_dec(v___y_3172_);
    leanh::lean_dec_ref(v___y_3171_);
    leanh::lean_dec(v___y_3170_);
    return v_res_3178_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__5(
    mut v_b_3179_: *mut leanh::LeanObject,
    mut v_xs_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: u8,
    mut v___x_3182_: u8,
    mut v___y_3183_: u8,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
    mut v___y_3187_: *mut leanh::LeanObject,
    mut v___y_3188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = l_Lean_Meta_AbstractNestedProofs_visit(
        v_b_3179_,
        v___y_3183_,
        v___y_3184_,
        v___y_3185_,
        v___y_3186_,
        v___y_3187_,
        v___y_3188_,
    );
    if leanh::lean_obj_tag(v___x_3190_) == 0 {
        let mut v_a_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3192_: u8 = 0;
        let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3191_ = leanh::lean_ctor_get(v___x_3190_, 0);
        leanh::lean_inc(v_a_3191_);
        leanh::lean_dec_ref_known(v___x_3190_, 1);
        v___x_3192_ = 1;
        v___x_3193_ = l_Lean_Meta_mkForallFVars(
            v_xs_3180_,
            v_a_3191_,
            v___y_3181_,
            v___x_3182_,
            v___x_3182_,
            v___x_3192_,
            v___y_3185_,
            v___y_3186_,
            v___y_3187_,
            v___y_3188_,
        );
        return v___x_3193_;
    } else {
        return v___x_3190_;
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(
    mut v_b_3194_: *mut leanh::LeanObject,
    mut v_xs_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___x_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___y_3200_: *mut leanh::LeanObject,
    mut v___y_3201_: *mut leanh::LeanObject,
    mut v___y_3202_: *mut leanh::LeanObject,
    mut v___y_3203_: *mut leanh::LeanObject,
    mut v___y_3204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_30371__boxed_3205_: u8 = 0;
    let mut v___x_30372__boxed_3206_: u8 = 0;
    let mut v___y_30373__boxed_3207_: u8 = 0;
    let mut v_res_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_30371__boxed_3205_ = (leanh::lean_unbox(v___y_3196_) as u8);
    v___x_30372__boxed_3206_ = (leanh::lean_unbox(v___x_3197_) as u8);
    v___y_30373__boxed_3207_ = (leanh::lean_unbox(v___y_3198_) as u8);
    v_res_3208_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(
        v_b_3194_,
        v_xs_3195_,
        v___y_30371__boxed_3205_,
        v___x_30372__boxed_3206_,
        v___y_30373__boxed_3207_,
        v___y_3199_,
        v___y_3200_,
        v___y_3201_,
        v___y_3202_,
        v___y_3203_,
    );
    leanh::lean_dec(v___y_3203_);
    leanh::lean_dec_ref(v___y_3202_);
    leanh::lean_dec(v___y_3201_);
    leanh::lean_dec_ref(v___y_3200_);
    leanh::lean_dec(v___y_3199_);
    leanh::lean_dec_ref(v_xs_3195_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__3(
    mut v___y_3209_: u8,
    mut v___x_3210_: u8,
    mut v___f_3211_: *mut leanh::LeanObject,
    mut v_xs_3212_: *mut leanh::LeanObject,
    mut v_b_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: u8,
    mut v___y_3215_: *mut leanh::LeanObject,
    mut v___y_3216_: *mut leanh::LeanObject,
    mut v___y_3217_: *mut leanh::LeanObject,
    mut v___y_3218_: *mut leanh::LeanObject,
    mut v___y_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3221_ = leanh::lean_box((v___y_3209_) as usize);
    v___x_3222_ = leanh::lean_box((v___x_3210_) as usize);
    leanh::lean_inc_ref(v_xs_3212_);
    v___f_3223_ = leanh::lean_alloc_closure(
        l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    leanh::lean_closure_set(v___f_3223_, 0, v_b_3213_);
    leanh::lean_closure_set(v___f_3223_, 1, v_xs_3212_);
    leanh::lean_closure_set(v___f_3223_, 2, v___x_3221_);
    leanh::lean_closure_set(v___f_3223_, 3, v___x_3222_);
    v___x_3224_ = leanh::lean_box((v___y_3214_) as usize);
    leanh::lean_inc(v___y_3219_);
    leanh::lean_inc_ref(v___y_3218_);
    leanh::lean_inc(v___y_3217_);
    leanh::lean_inc_ref(v___y_3216_);
    leanh::lean_inc(v___y_3215_);
    v___x_3225_ = leanh::lean_apply_9(
        v___f_3211_,
        v_xs_3212_,
        v___f_3223_,
        v___x_3224_,
        v___y_3215_,
        v___y_3216_,
        v___y_3217_,
        v___y_3218_,
        v___y_3219_,
        leanh::lean_box(0),
    );
    return v___x_3225_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(
    mut v___y_3226_: *mut leanh::LeanObject,
    mut v___x_3227_: *mut leanh::LeanObject,
    mut v___f_3228_: *mut leanh::LeanObject,
    mut v_xs_3229_: *mut leanh::LeanObject,
    mut v_b_3230_: *mut leanh::LeanObject,
    mut v___y_3231_: *mut leanh::LeanObject,
    mut v___y_3232_: *mut leanh::LeanObject,
    mut v___y_3233_: *mut leanh::LeanObject,
    mut v___y_3234_: *mut leanh::LeanObject,
    mut v___y_3235_: *mut leanh::LeanObject,
    mut v___y_3236_: *mut leanh::LeanObject,
    mut v___y_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_30346__boxed_3238_: u8 = 0;
    let mut v___x_30347__boxed_3239_: u8 = 0;
    let mut v___y_30349__boxed_3240_: u8 = 0;
    let mut v_res_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_30346__boxed_3238_ = (leanh::lean_unbox(v___y_3226_) as u8);
    v___x_30347__boxed_3239_ = (leanh::lean_unbox(v___x_3227_) as u8);
    v___y_30349__boxed_3240_ = (leanh::lean_unbox(v___y_3231_) as u8);
    v_res_3241_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(
        v___y_30346__boxed_3238_,
        v___x_30347__boxed_3239_,
        v___f_3228_,
        v_xs_3229_,
        v_b_3230_,
        v___y_30349__boxed_3240_,
        v___y_3232_,
        v___y_3233_,
        v___y_3234_,
        v___y_3235_,
        v___y_3236_,
    );
    leanh::lean_dec(v___y_3236_);
    leanh::lean_dec_ref(v___y_3235_);
    leanh::lean_dec(v___y_3234_);
    leanh::lean_dec_ref(v___y_3233_);
    leanh::lean_dec(v___y_3232_);
    return v_res_3241_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(
    mut v_sz_3242_: usize,
    mut v_i_3243_: usize,
    mut v_bs_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: u8,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
    mut v___y_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: usize = 0;
    let mut v___x_3260_: usize = 0;
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3266_: u8 = 0;
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3252_ = lean_usize_dec_lt(v_i_3243_, v_sz_3242_);
                if v___x_3252_ == 0 {
                    v___x_3253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3253_, 0, v_bs_3244_);
                    return v___x_3253_;
                } else {
                    v_v_3254_ = lean_array_uget_borrowed(v_bs_3244_, v_i_3243_);
                    leanh::lean_inc(v_v_3254_);
                    v___x_3255_ = l_Lean_Meta_AbstractNestedProofs_visit(
                        v_v_3254_,
                        v___y_3245_,
                        v___y_3246_,
                        v___y_3247_,
                        v___y_3248_,
                        v___y_3249_,
                        v___y_3250_,
                    );
                    if leanh::lean_obj_tag(v___x_3255_) == 0 {
                        v_a_3256_ = leanh::lean_ctor_get(v___x_3255_, 0);
                        leanh::lean_inc(v_a_3256_);
                        leanh::lean_dec_ref_known(v___x_3255_, 1);
                        v___x_3257_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3258_ = lean_array_uset(v_bs_3244_, v_i_3243_, v___x_3257_);
                        v___x_3259_ = 1usize;
                        v___x_3260_ = lean_usize_add(v_i_3243_, v___x_3259_);
                        v___x_3261_ = lean_array_uset(v_bs_x27_3258_, v_i_3243_, v_a_3256_);
                        v_i_3243_ = v___x_3260_;
                        v_bs_3244_ = v___x_3261_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3244_);
                        v_a_3263_ = leanh::lean_ctor_get(v___x_3255_, 0);
                        v_isSharedCheck_3270_ =
                            (!leanh::lean_is_exclusive(v___x_3255_)) as u8;
                        if v_isSharedCheck_3270_ == 0 {
                            v___x_3265_ = v___x_3255_;
                            v_isShared_3266_ = v_isSharedCheck_3270_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3263_);
                            leanh::lean_dec(v___x_3255_);
                            v___x_3265_ = leanh::lean_box(0);
                            v_isShared_3266_ = v_isSharedCheck_3270_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3266_ == 0 {
                    v___x_3268_ = v___x_3265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
                    v___x_3268_ = v_reuseFailAlloc_3269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(
    mut v_x_3271_: *mut leanh::LeanObject,
    mut v_x_3272_: *mut leanh::LeanObject,
    mut v_x_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: u8,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
    mut v___y_3277_: *mut leanh::LeanObject,
    mut v___y_3278_: *mut leanh::LeanObject,
    mut v___y_3279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3289_: usize = 0;
    let mut v___x_3290_: usize = 0;
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut v_a_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3271_) == 5 {
                    v_fn_3281_ = leanh::lean_ctor_get(v_x_3271_, 0);
                    leanh::lean_inc_ref(v_fn_3281_);
                    v_arg_3282_ = leanh::lean_ctor_get(v_x_3271_, 1);
                    leanh::lean_inc_ref(v_arg_3282_);
                    leanh::lean_dec_ref_known(v_x_3271_, 2);
                    v___x_3283_ = lean_array_set(v_x_3272_, v_x_3273_, v_arg_3282_);
                    v___x_3284_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3285_ = lean_nat_sub(v_x_3273_, v___x_3284_);
                    leanh::lean_dec(v_x_3273_);
                    v_x_3271_ = v_fn_3281_;
                    v_x_3272_ = v___x_3283_;
                    v_x_3273_ = v___x_3285_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_3273_);
                    v___x_3287_ = l_Lean_Meta_AbstractNestedProofs_visit(
                        v_x_3271_,
                        v___y_3274_,
                        v___y_3275_,
                        v___y_3276_,
                        v___y_3277_,
                        v___y_3278_,
                        v___y_3279_,
                    );
                    if leanh::lean_obj_tag(v___x_3287_) == 0 {
                        v_a_3288_ = leanh::lean_ctor_get(v___x_3287_, 0);
                        leanh::lean_inc(v_a_3288_);
                        leanh::lean_dec_ref_known(v___x_3287_, 1);
                        v_sz_3289_ = lean_array_size(v_x_3272_);
                        v___x_3290_ = 0usize;
                        v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_3289_, v___x_3290_, v_x_3272_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
                        if leanh::lean_obj_tag(v___x_3291_) == 0 {
                            v_a_3292_ = leanh::lean_ctor_get(v___x_3291_, 0);
                            v_isSharedCheck_3300_ =
                                (!leanh::lean_is_exclusive(v___x_3291_)) as u8;
                            if v_isSharedCheck_3300_ == 0 {
                                v___x_3294_ = v___x_3291_;
                                v_isShared_3295_ = v_isSharedCheck_3300_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3292_);
                                leanh::lean_dec(v___x_3291_);
                                v___x_3294_ = leanh::lean_box(0);
                                v_isShared_3295_ = v_isSharedCheck_3300_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3288_);
                            v_a_3301_ = leanh::lean_ctor_get(v___x_3291_, 0);
                            v_isSharedCheck_3308_ =
                                (!leanh::lean_is_exclusive(v___x_3291_)) as u8;
                            if v_isSharedCheck_3308_ == 0 {
                                v___x_3303_ = v___x_3291_;
                                v_isShared_3304_ = v_isSharedCheck_3308_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3301_);
                                leanh::lean_dec(v___x_3291_);
                                v___x_3303_ = leanh::lean_box(0);
                                v_isShared_3304_ = v_isSharedCheck_3308_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_3272_);
                        return v___x_3287_;
                    }
                }
            }
            1 => {
                v___x_3296_ = l_Lean_mkAppN(v_a_3288_, v_a_3292_);
                leanh::lean_dec(v_a_3292_);
                if v_isShared_3295_ == 0 {
                    leanh::lean_ctor_set(v___x_3294_, 0, v___x_3296_);
                    v___x_3298_ = v___x_3294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
                    v___x_3298_ = v_reuseFailAlloc_3299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3298_;
            }
            3 => {
                if v_isShared_3304_ == 0 {
                    v___x_3306_ = v___x_3303_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit(
    mut v_e_3309_: *mut leanh::LeanObject,
    mut v_a_3310_: u8,
    mut v_a_3311_: *mut leanh::LeanObject,
    mut v_a_3312_: *mut leanh::LeanObject,
    mut v_a_3313_: *mut leanh::LeanObject,
    mut v_a_3314_: *mut leanh::LeanObject,
    mut v_a_3315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3330_: u8 = 0;
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: u8 = 0;
    let mut v___y_3342_: u8 = 0;
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: usize = 0;
    let mut v___x_3358_: usize = 0;
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: usize = 0;
    let mut v___x_3367_: usize = 0;
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: u8 = 0;
    let mut v___x_3378_: u8 = 0;
    let mut v_a_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_val_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut v_unused_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3326_ = l_Lean_Meta_AbstractNestedProofs_visit___closed__0;
                v___x_3327_ = l_Lean_Core_checkSystem(v___x_3326_, v_a_3314_, v_a_3315_);
                if leanh::lean_obj_tag(v___x_3327_) == 0 {
                    v_isSharedCheck_3394_ = (!leanh::lean_is_exclusive(v___x_3327_)) as u8;
                    if v_isSharedCheck_3394_ == 0 {
                        v_unused_3395_ = leanh::lean_ctor_get(v___x_3327_, 0);
                        leanh::lean_dec(v_unused_3395_);
                        v___x_3329_ = v___x_3327_;
                        v_isShared_3330_ = v_isSharedCheck_3394_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3327_);
                        v___x_3329_ = leanh::lean_box(0);
                        v_isShared_3330_ = v_isSharedCheck_3394_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3309_);
                    v_a_3396_ = leanh::lean_ctor_get(v___x_3327_, 0);
                    v_isSharedCheck_3403_ = (!leanh::lean_is_exclusive(v___x_3327_)) as u8;
                    if v_isSharedCheck_3403_ == 0 {
                        v___x_3398_ = v___x_3327_;
                        v_isShared_3399_ = v_isSharedCheck_3403_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3396_);
                        leanh::lean_dec(v___x_3327_);
                        v___x_3398_ = leanh::lean_box(0);
                        v_isShared_3399_ = v_isSharedCheck_3403_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3319_ = lean_st_ref_take(v_a_3311_);
                leanh::lean_inc_ref(v_a_3318_);
                v___x_3320_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_3319_, v_e_3309_, v_a_3318_);
                v___x_3321_ = lean_st_ref_set(v_a_3311_, v___x_3320_);
                v___x_3322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3322_, 0, v_a_3318_);
                return v___x_3322_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3324_) == 0 {
                    v_a_3325_ = leanh::lean_ctor_get(v___y_3324_, 0);
                    leanh::lean_inc(v_a_3325_);
                    leanh::lean_dec_ref_known(v___y_3324_, 1);
                    v_a_3318_ = v_a_3325_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_3309_);
                    return v___y_3324_;
                }
            }
            3 => {
                v___x_3331_ = l_Lean_Expr_isAtomic(v_e_3309_);
                if v___x_3331_ == 0 {
                    v___x_3332_ = lean_st_ref_get(v_a_3311_);
                    v___x_3333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_3332_, v_e_3309_);
                    leanh::lean_dec(v___x_3332_);
                    if leanh::lean_obj_tag(v___x_3333_) == 0 {
                        leanh::lean_del_object(v___x_3329_);
                        leanh::lean_inc_ref(v_e_3309_);
                        v___x_3334_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(
                            v_e_3309_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_,
                        );
                        if leanh::lean_obj_tag(v___x_3334_) == 0 {
                            v_a_3335_ = leanh::lean_ctor_get(v___x_3334_, 0);
                            leanh::lean_inc(v_a_3335_);
                            leanh::lean_dec_ref_known(v___x_3334_, 1);
                            v___f_3339_ = leanh::lean_alloc_closure(
                                l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                9,
                                0,
                            );
                            v___x_3340_ = 1;
                            v___x_3376_ = (leanh::lean_unbox(v_a_3335_) as u8);
                            if v___x_3376_ == 0 {
                                v___x_3377_ = (leanh::lean_unbox(v_a_3335_) as u8);
                                leanh::lean_dec(v_a_3335_);
                                v___y_3342_ = v___x_3377_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_3335_);
                                v___x_3378_ = l_Lean_Expr_hasSorry(v_e_3309_);
                                if v___x_3378_ == 0 {
                                    leanh::lean_dec_ref(v___f_3339_);
                                    state = 4;
                                    continue;
                                } else {
                                    if v___x_3331_ == 0 {
                                        v___y_3342_ = v___x_3331_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v___f_3339_);
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_3309_);
                            v_a_3379_ = leanh::lean_ctor_get(v___x_3334_, 0);
                            v_isSharedCheck_3386_ =
                                (!leanh::lean_is_exclusive(v___x_3334_)) as u8;
                            if v_isSharedCheck_3386_ == 0 {
                                v___x_3381_ = v___x_3334_;
                                v_isShared_3382_ = v_isSharedCheck_3386_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3379_);
                                leanh::lean_dec(v___x_3334_);
                                v___x_3381_ = leanh::lean_box(0);
                                v_isShared_3382_ = v_isSharedCheck_3386_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3309_);
                        v_val_3387_ = leanh::lean_ctor_get(v___x_3333_, 0);
                        leanh::lean_inc(v_val_3387_);
                        leanh::lean_dec_ref_known(v___x_3333_, 1);
                        if v_isShared_3330_ == 0 {
                            leanh::lean_ctor_set(v___x_3329_, 0, v_val_3387_);
                            v___x_3389_ = v___x_3329_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3390_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_val_3387_);
                            v___x_3389_ = v_reuseFailAlloc_3390_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_3330_ == 0 {
                        leanh::lean_ctor_set(v___x_3329_, 0, v_e_3309_);
                        v___x_3392_ = v___x_3329_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_e_3309_);
                        v___x_3392_ = v_reuseFailAlloc_3393_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3337_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_AbstractNestedProofs_visit___boxed as *mut core::ffi::c_void,
                    8,
                    0,
                );
                leanh::lean_inc_ref(v_e_3309_);
                v___x_3338_ =
                    l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(
                        v_e_3309_,
                        v_a_3310_,
                        v___x_3337_,
                        v_a_3310_,
                        v_a_3311_,
                        v_a_3312_,
                        v_a_3313_,
                        v_a_3314_,
                        v_a_3315_,
                    );
                v___y_3324_ = v___x_3338_;
                state = 2;
                continue;
            }
            5 => match leanh::lean_obj_tag(v_e_3309_) {
                6 => {
                    v___x_3343_ = leanh::lean_box((v___y_3342_) as usize);
                    v___f_3344_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed
                            as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3344_, 0, v___x_3343_);
                    leanh::lean_closure_set(v___f_3344_, 1, v___f_3339_);
                    leanh::lean_inc_ref(v_e_3309_);
                    v___x_3345_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_3309_, v___f_3344_, v___y_3342_, v___x_3340_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                    v___y_3324_ = v___x_3345_;
                    state = 2;
                    continue;
                }
                8 => {
                    v___x_3346_ = leanh::lean_box((v___y_3342_) as usize);
                    v___f_3347_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed
                            as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3347_, 0, v___x_3346_);
                    leanh::lean_closure_set(v___f_3347_, 1, v___f_3339_);
                    leanh::lean_inc_ref(v_e_3309_);
                    v___x_3348_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_3309_, v___f_3347_, v___y_3342_, v___x_3340_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                    v___y_3324_ = v___x_3348_;
                    state = 2;
                    continue;
                }
                7 => {
                    v___x_3349_ = leanh::lean_box((v___y_3342_) as usize);
                    v___x_3350_ = leanh::lean_box((v___x_3340_) as usize);
                    v___f_3351_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed
                            as *mut core::ffi::c_void,
                        12,
                        3,
                    );
                    leanh::lean_closure_set(v___f_3351_, 0, v___x_3349_);
                    leanh::lean_closure_set(v___f_3351_, 1, v___x_3350_);
                    leanh::lean_closure_set(v___f_3351_, 2, v___f_3339_);
                    leanh::lean_inc_ref(v_e_3309_);
                    v___x_3352_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_3309_, v___f_3351_, v___y_3342_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                    v___y_3324_ = v___x_3352_;
                    state = 2;
                    continue;
                }
                10 => {
                    leanh::lean_dec_ref(v___f_3339_);
                    v_data_3353_ = leanh::lean_ctor_get(v_e_3309_, 0);
                    v_expr_3354_ = leanh::lean_ctor_get(v_e_3309_, 1);
                    leanh::lean_inc_ref(v_expr_3354_);
                    v___x_3355_ = l_Lean_Meta_AbstractNestedProofs_visit(
                        v_expr_3354_,
                        v_a_3310_,
                        v_a_3311_,
                        v_a_3312_,
                        v_a_3313_,
                        v_a_3314_,
                        v_a_3315_,
                    );
                    if leanh::lean_obj_tag(v___x_3355_) == 0 {
                        v_a_3356_ = leanh::lean_ctor_get(v___x_3355_, 0);
                        leanh::lean_inc(v_a_3356_);
                        leanh::lean_dec_ref_known(v___x_3355_, 1);
                        v___x_3357_ = lean_ptr_addr(v_expr_3354_);
                        v___x_3358_ = lean_ptr_addr(v_a_3356_);
                        v___x_3359_ = lean_usize_dec_eq(v___x_3357_, v___x_3358_);
                        if v___x_3359_ == 0 {
                            leanh::lean_inc(v_data_3353_);
                            v___x_3360_ = l_Lean_Expr_mdata___override(v_data_3353_, v_a_3356_);
                            v_a_3318_ = v___x_3360_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3356_);
                            leanh::lean_inc_ref(v_e_3309_);
                            v_a_3318_ = v_e_3309_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_3324_ = v___x_3355_;
                        state = 2;
                        continue;
                    }
                }
                11 => {
                    leanh::lean_dec_ref(v___f_3339_);
                    v_typeName_3361_ = leanh::lean_ctor_get(v_e_3309_, 0);
                    v_idx_3362_ = leanh::lean_ctor_get(v_e_3309_, 1);
                    v_struct_3363_ = leanh::lean_ctor_get(v_e_3309_, 2);
                    leanh::lean_inc_ref(v_struct_3363_);
                    v___x_3364_ = l_Lean_Meta_AbstractNestedProofs_visit(
                        v_struct_3363_,
                        v_a_3310_,
                        v_a_3311_,
                        v_a_3312_,
                        v_a_3313_,
                        v_a_3314_,
                        v_a_3315_,
                    );
                    if leanh::lean_obj_tag(v___x_3364_) == 0 {
                        v_a_3365_ = leanh::lean_ctor_get(v___x_3364_, 0);
                        leanh::lean_inc(v_a_3365_);
                        leanh::lean_dec_ref_known(v___x_3364_, 1);
                        v___x_3366_ = lean_ptr_addr(v_struct_3363_);
                        v___x_3367_ = lean_ptr_addr(v_a_3365_);
                        v___x_3368_ = lean_usize_dec_eq(v___x_3366_, v___x_3367_);
                        if v___x_3368_ == 0 {
                            leanh::lean_inc(v_idx_3362_);
                            leanh::lean_inc(v_typeName_3361_);
                            v___x_3369_ = l_Lean_Expr_proj___override(
                                v_typeName_3361_,
                                v_idx_3362_,
                                v_a_3365_,
                            );
                            v_a_3318_ = v___x_3369_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3365_);
                            leanh::lean_inc_ref(v_e_3309_);
                            v_a_3318_ = v_e_3309_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_3324_ = v___x_3364_;
                        state = 2;
                        continue;
                    }
                }
                5 => {
                    leanh::lean_dec_ref(v___f_3339_);
                    v_dummy_3370_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once), _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
                    v_nargs_3371_ = l_Lean_Expr_getAppNumArgs(v_e_3309_);
                    leanh::lean_inc(v_nargs_3371_);
                    v___x_3372_ = lean_mk_array(v_nargs_3371_, v_dummy_3370_);
                    v___x_3373_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3374_ = lean_nat_sub(v_nargs_3371_, v___x_3373_);
                    leanh::lean_dec(v_nargs_3371_);
                    leanh::lean_inc_ref(v_e_3309_);
                    v___x_3375_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_3309_, v___x_3372_, v___x_3374_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                    v___y_3324_ = v___x_3375_;
                    state = 2;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v___f_3339_);
                    leanh::lean_inc_ref(v_e_3309_);
                    v_a_3318_ = v_e_3309_;
                    state = 1;
                    continue;
                }
            },
            6 => {
                if v_isShared_3382_ == 0 {
                    v___x_3384_ = v___x_3381_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3384_;
            }
            8 => {
                return v___x_3389_;
            }
            9 => {
                return v___x_3392_;
            }
            10 => {
                if v_isShared_3399_ == 0 {
                    v___x_3401_ = v___x_3398_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3402_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
                    v___x_3401_ = v_reuseFailAlloc_3402_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__1(
    mut v_b_3404_: *mut leanh::LeanObject,
    mut v_xs_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: u8,
    mut v___y_3407_: u8,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Lean_Meta_AbstractNestedProofs_visit(
        v_b_3404_,
        v___y_3407_,
        v___y_3408_,
        v___y_3409_,
        v___y_3410_,
        v___y_3411_,
        v___y_3412_,
    );
    if leanh::lean_obj_tag(v___x_3414_) == 0 {
        let mut v_a_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3416_: u8 = 0;
        let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3415_ = leanh::lean_ctor_get(v___x_3414_, 0);
        leanh::lean_inc(v_a_3415_);
        leanh::lean_dec_ref_known(v___x_3414_, 1);
        v___x_3416_ = 1;
        v___x_3417_ = l_Lean_Meta_mkLambdaFVars(
            v_xs_3405_,
            v_a_3415_,
            v___y_3406_,
            v___y_3406_,
            v___y_3406_,
            v___y_3406_,
            v___x_3416_,
            v___y_3409_,
            v___y_3410_,
            v___y_3411_,
            v___y_3412_,
        );
        return v___x_3417_;
    } else {
        return v___x_3414_;
    }
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(
    mut v_b_3418_: *mut leanh::LeanObject,
    mut v_xs_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
    mut v___y_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_30358__boxed_3428_: u8 = 0;
    let mut v___y_30359__boxed_3429_: u8 = 0;
    let mut v_res_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_30358__boxed_3428_ = (leanh::lean_unbox(v___y_3420_) as u8);
    v___y_30359__boxed_3429_ = (leanh::lean_unbox(v___y_3421_) as u8);
    v_res_3430_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(
        v_b_3418_,
        v_xs_3419_,
        v___y_30358__boxed_3428_,
        v___y_30359__boxed_3429_,
        v___y_3422_,
        v___y_3423_,
        v___y_3424_,
        v___y_3425_,
        v___y_3426_,
    );
    leanh::lean_dec(v___y_3426_);
    leanh::lean_dec_ref(v___y_3425_);
    leanh::lean_dec(v___y_3424_);
    leanh::lean_dec_ref(v___y_3423_);
    leanh::lean_dec(v___y_3422_);
    leanh::lean_dec_ref(v_xs_3419_);
    return v_res_3430_;
}
pub unsafe fn l_Lean_Meta_AbstractNestedProofs_visit___lam__2(
    mut v___y_3431_: u8,
    mut v___f_3432_: *mut leanh::LeanObject,
    mut v_xs_3433_: *mut leanh::LeanObject,
    mut v_b_3434_: *mut leanh::LeanObject,
    mut v___y_3435_: u8,
    mut v___y_3436_: *mut leanh::LeanObject,
    mut v___y_3437_: *mut leanh::LeanObject,
    mut v___y_3438_: *mut leanh::LeanObject,
    mut v___y_3439_: *mut leanh::LeanObject,
    mut v___y_3440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ = leanh::lean_box((v___y_3431_) as usize);
    leanh::lean_inc_ref(v_xs_3433_);
    v___f_3443_ = leanh::lean_alloc_closure(
        l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed as *mut core::ffi::c_void,
        10,
        3,
    );
    leanh::lean_closure_set(v___f_3443_, 0, v_b_3434_);
    leanh::lean_closure_set(v___f_3443_, 1, v_xs_3433_);
    leanh::lean_closure_set(v___f_3443_, 2, v___x_3442_);
    v___x_3444_ = leanh::lean_box((v___y_3435_) as usize);
    leanh::lean_inc(v___y_3440_);
    leanh::lean_inc_ref(v___y_3439_);
    leanh::lean_inc(v___y_3438_);
    leanh::lean_inc_ref(v___y_3437_);
    leanh::lean_inc(v___y_3436_);
    v___x_3445_ = leanh::lean_apply_9(
        v___f_3432_,
        v_xs_3433_,
        v___f_3443_,
        v___x_3444_,
        v___y_3436_,
        v___y_3437_,
        v___y_3438_,
        v___y_3439_,
        v___y_3440_,
        leanh::lean_box(0),
    );
    return v___x_3445_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(
    mut v_sz_3446_: *mut leanh::LeanObject,
    mut v_i_3447_: *mut leanh::LeanObject,
    mut v_bs_3448_: *mut leanh::LeanObject,
    mut v___y_3449_: *mut leanh::LeanObject,
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
    mut v___y_3453_: *mut leanh::LeanObject,
    mut v___y_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3456_: usize = 0;
    let mut v_i_boxed_3457_: usize = 0;
    let mut v___y_30398__boxed_3458_: u8 = 0;
    let mut v_res_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3456_ = leanh::lean_unbox_usize(v_sz_3446_);
    leanh::lean_dec(v_sz_3446_);
    v_i_boxed_3457_ = leanh::lean_unbox_usize(v_i_3447_);
    leanh::lean_dec(v_i_3447_);
    v___y_30398__boxed_3458_ = (leanh::lean_unbox(v___y_3449_) as u8);
    v_res_3459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_3456_, v_i_boxed_3457_, v_bs_3448_, v___y_30398__boxed_3458_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
    leanh::lean_dec(v___y_3454_);
    leanh::lean_dec_ref(v___y_3453_);
    leanh::lean_dec(v___y_3452_);
    leanh::lean_dec_ref(v___y_3451_);
    leanh::lean_dec(v___y_3450_);
    return v_res_3459_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(
    mut v_x_3460_: *mut leanh::LeanObject,
    mut v_x_3461_: *mut leanh::LeanObject,
    mut v_x_3462_: *mut leanh::LeanObject,
    mut v___y_3463_: *mut leanh::LeanObject,
    mut v___y_3464_: *mut leanh::LeanObject,
    mut v___y_3465_: *mut leanh::LeanObject,
    mut v___y_3466_: *mut leanh::LeanObject,
    mut v___y_3467_: *mut leanh::LeanObject,
    mut v___y_3468_: *mut leanh::LeanObject,
    mut v___y_3469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_30419__boxed_3470_: u8 = 0;
    let mut v_res_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_30419__boxed_3470_ = (leanh::lean_unbox(v___y_3463_) as u8);
    v_res_3471_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(
        v_x_3460_,
        v_x_3461_,
        v_x_3462_,
        v___y_30419__boxed_3470_,
        v___y_3464_,
        v___y_3465_,
        v___y_3466_,
        v___y_3467_,
        v___y_3468_,
    );
    leanh::lean_dec(v___y_3468_);
    leanh::lean_dec_ref(v___y_3467_);
    leanh::lean_dec(v___y_3466_);
    leanh::lean_dec_ref(v___y_3465_);
    leanh::lean_dec(v___y_3464_);
    return v_res_3471_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(
    mut v_as_3472_: *mut leanh::LeanObject,
    mut v_sz_3473_: *mut leanh::LeanObject,
    mut v_i_3474_: *mut leanh::LeanObject,
    mut v_b_3475_: *mut leanh::LeanObject,
    mut v___y_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
    mut v___y_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
    mut v___y_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3483_: usize = 0;
    let mut v_i_boxed_3484_: usize = 0;
    let mut v___y_30442__boxed_3485_: u8 = 0;
    let mut v_res_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3483_ = leanh::lean_unbox_usize(v_sz_3473_);
    leanh::lean_dec(v_sz_3473_);
    v_i_boxed_3484_ = leanh::lean_unbox_usize(v_i_3474_);
    leanh::lean_dec(v_i_3474_);
    v___y_30442__boxed_3485_ = (leanh::lean_unbox(v___y_3476_) as u8);
    v_res_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_as_3472_, v_sz_boxed_3483_, v_i_boxed_3484_, v_b_3475_, v___y_30442__boxed_3485_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
    leanh::lean_dec(v___y_3481_);
    leanh::lean_dec_ref(v___y_3480_);
    leanh::lean_dec(v___y_3479_);
    leanh::lean_dec_ref(v___y_3478_);
    leanh::lean_dec(v___y_3477_);
    leanh::lean_dec_ref(v_as_3472_);
    return v_res_3486_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(
    mut v_00_u03b2_3487_: *mut leanh::LeanObject,
    mut v_m_3488_: *mut leanh::LeanObject,
    mut v_a_3489_: *mut leanh::LeanObject,
    mut v_b_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3491_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_3488_, v_a_3489_, v_b_3490_);
    return v___x_3491_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(
    mut v_00_u03b2_3492_: *mut leanh::LeanObject,
    mut v_m_3493_: *mut leanh::LeanObject,
    mut v_a_3494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_3493_, v_a_3494_);
    return v___x_3495_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(
    mut v_00_u03b2_3496_: *mut leanh::LeanObject,
    mut v_m_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_00_u03b2_3496_, v_m_3497_, v_a_3498_);
    leanh::lean_dec_ref(v_a_3498_);
    leanh::lean_dec_ref(v_m_3497_);
    return v_res_3499_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(
    mut v_00_u03b2_3500_: *mut leanh::LeanObject,
    mut v_x_3501_: *mut leanh::LeanObject,
    mut v_x_3502_: *mut leanh::LeanObject,
    mut v_x_3503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3504_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_x_3501_, v_x_3502_, v_x_3503_);
    return v___x_3504_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(
    mut v_00_u03b2_3505_: *mut leanh::LeanObject,
    mut v_a_3506_: *mut leanh::LeanObject,
    mut v_x_3507_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3508_: u8 = 0;
    v___x_3508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_3506_, v_x_3507_);
    return v___x_3508_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(
    mut v_00_u03b2_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
    mut v_x_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3512_: u8 = 0;
    let mut v_r_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_3509_, v_a_3510_, v_x_3511_);
    leanh::lean_dec(v_x_3511_);
    leanh::lean_dec_ref(v_a_3510_);
    v_r_3513_ = leanh::lean_box((v_res_3512_) as usize);
    return v_r_3513_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(
    mut v_00_u03b2_3514_: *mut leanh::LeanObject,
    mut v_data_3515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3516_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_data_3515_);
    return v___x_3516_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(
    mut v_00_u03b2_3517_: *mut leanh::LeanObject,
    mut v_a_3518_: *mut leanh::LeanObject,
    mut v_b_3519_: *mut leanh::LeanObject,
    mut v_x_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_3518_, v_b_3519_, v_x_3520_);
    return v___x_3521_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(
    mut v_00_u03b2_3522_: *mut leanh::LeanObject,
    mut v_a_3523_: *mut leanh::LeanObject,
    mut v_x_3524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_3523_, v_x_3524_);
    return v___x_3525_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(
    mut v_00_u03b2_3526_: *mut leanh::LeanObject,
    mut v_a_3527_: *mut leanh::LeanObject,
    mut v_x_3528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(v_00_u03b2_3526_, v_a_3527_, v_x_3528_);
    leanh::lean_dec(v_x_3528_);
    leanh::lean_dec_ref(v_a_3527_);
    return v_res_3529_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(
    mut v_00_u03b1_3530_: *mut leanh::LeanObject,
    mut v_x_3531_: *mut leanh::LeanObject,
    mut v_isExporting_3532_: u8,
    mut v___y_3533_: u8,
    mut v___y_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_3531_, v_isExporting_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
    return v___x_3540_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___boxed(
    mut v_00_u03b1_3541_: *mut leanh::LeanObject,
    mut v_x_3542_: *mut leanh::LeanObject,
    mut v_isExporting_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
    mut v___y_3547_: *mut leanh::LeanObject,
    mut v___y_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3551_: u8 = 0;
    let mut v___y_31039__boxed_3552_: u8 = 0;
    let mut v_res_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3551_ = (leanh::lean_unbox(v_isExporting_3543_) as u8);
    v___y_31039__boxed_3552_ = (leanh::lean_unbox(v___y_3544_) as u8);
    v_res_3553_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(v_00_u03b1_3541_, v_x_3542_, v_isExporting_boxed_3551_, v___y_31039__boxed_3552_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
    leanh::lean_dec(v___y_3549_);
    leanh::lean_dec_ref(v___y_3548_);
    leanh::lean_dec(v___y_3547_);
    leanh::lean_dec_ref(v___y_3546_);
    leanh::lean_dec(v___y_3545_);
    return v_res_3553_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(
    mut v_00_u03b1_3554_: *mut leanh::LeanObject,
    mut v_x_3555_: *mut leanh::LeanObject,
    mut v_when_3556_: u8,
    mut v___y_3557_: u8,
    mut v___y_3558_: *mut leanh::LeanObject,
    mut v___y_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3564_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_3555_, v_when_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
    return v___x_3564_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(
    mut v_00_u03b1_3565_: *mut leanh::LeanObject,
    mut v_x_3566_: *mut leanh::LeanObject,
    mut v_when_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
    mut v___y_3572_: *mut leanh::LeanObject,
    mut v___y_3573_: *mut leanh::LeanObject,
    mut v___y_3574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_3575_: u8 = 0;
    let mut v___y_31062__boxed_3576_: u8 = 0;
    let mut v_res_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_3575_ = (leanh::lean_unbox(v_when_3567_) as u8);
    v___y_31062__boxed_3576_ = (leanh::lean_unbox(v___y_3568_) as u8);
    v_res_3577_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(v_00_u03b1_3565_, v_x_3566_, v_when_boxed_3575_, v___y_31062__boxed_3576_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
    leanh::lean_dec(v___y_3573_);
    leanh::lean_dec_ref(v___y_3572_);
    leanh::lean_dec(v___y_3571_);
    leanh::lean_dec_ref(v___y_3570_);
    leanh::lean_dec(v___y_3569_);
    return v_res_3577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(
    mut v_00_u03b2_3578_: *mut leanh::LeanObject,
    mut v_x_3579_: *mut leanh::LeanObject,
    mut v_x_3580_: usize,
    mut v_x_3581_: usize,
    mut v_x_3582_: *mut leanh::LeanObject,
    mut v_x_3583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_3579_, v_x_3580_, v_x_3581_, v_x_3582_, v_x_3583_);
    return v___x_3584_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___boxed(
    mut v_00_u03b2_3585_: *mut leanh::LeanObject,
    mut v_x_3586_: *mut leanh::LeanObject,
    mut v_x_3587_: *mut leanh::LeanObject,
    mut v_x_3588_: *mut leanh::LeanObject,
    mut v_x_3589_: *mut leanh::LeanObject,
    mut v_x_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_31086__boxed_3591_: usize = 0;
    let mut v_x_31087__boxed_3592_: usize = 0;
    let mut v_res_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_31086__boxed_3591_ = leanh::lean_unbox_usize(v_x_3587_);
    leanh::lean_dec(v_x_3587_);
    v_x_31087__boxed_3592_ = leanh::lean_unbox_usize(v_x_3588_);
    leanh::lean_dec(v_x_3588_);
    v_res_3593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(v_00_u03b2_3585_, v_x_3586_, v_x_31086__boxed_3591_, v_x_31087__boxed_3592_, v_x_3589_, v_x_3590_);
    return v_res_3593_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(
    mut v_00_u03b2_3594_: *mut leanh::LeanObject,
    mut v_i_3595_: *mut leanh::LeanObject,
    mut v_source_3596_: *mut leanh::LeanObject,
    mut v_target_3597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v_i_3595_, v_source_3596_, v_target_3597_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15(
    mut v_00_u03b2_3599_: *mut leanh::LeanObject,
    mut v_n_3600_: *mut leanh::LeanObject,
    mut v_k_3601_: *mut leanh::LeanObject,
    mut v_v_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v_n_3600_, v_k_3601_, v_v_3602_);
    return v___x_3603_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(
    mut v_00_u03b2_3604_: *mut leanh::LeanObject,
    mut v_depth_3605_: usize,
    mut v_keys_3606_: *mut leanh::LeanObject,
    mut v_vals_3607_: *mut leanh::LeanObject,
    mut v_heq_3608_: *mut leanh::LeanObject,
    mut v_i_3609_: *mut leanh::LeanObject,
    mut v_entries_3610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3611_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_3605_, v_keys_3606_, v_vals_3607_, v_i_3609_, v_entries_3610_);
    return v___x_3611_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___boxed(
    mut v_00_u03b2_3612_: *mut leanh::LeanObject,
    mut v_depth_3613_: *mut leanh::LeanObject,
    mut v_keys_3614_: *mut leanh::LeanObject,
    mut v_vals_3615_: *mut leanh::LeanObject,
    mut v_heq_3616_: *mut leanh::LeanObject,
    mut v_i_3617_: *mut leanh::LeanObject,
    mut v_entries_3618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3619_: usize = 0;
    let mut v_res_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3619_ = leanh::lean_unbox_usize(v_depth_3613_);
    leanh::lean_dec(v_depth_3613_);
    v_res_3620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(v_00_u03b2_3612_, v_depth_boxed_3619_, v_keys_3614_, v_vals_3615_, v_heq_3616_, v_i_3617_, v_entries_3618_);
    leanh::lean_dec_ref(v_vals_3615_);
    leanh::lean_dec_ref(v_keys_3614_);
    return v_res_3620_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(
    mut v_00_u03b2_3621_: *mut leanh::LeanObject,
    mut v_x_3622_: *mut leanh::LeanObject,
    mut v_x_3623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3624_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_x_3622_, v_x_3623_);
    return v___x_3624_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19(
    mut v_00_u03b2_3625_: *mut leanh::LeanObject,
    mut v_x_3626_: *mut leanh::LeanObject,
    mut v_x_3627_: *mut leanh::LeanObject,
    mut v_x_3628_: *mut leanh::LeanObject,
    mut v_x_3629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3630_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_x_3626_, v_x_3627_, v_x_3628_, v_x_3629_);
    return v___x_3630_;
}
pub unsafe fn _init_l_Lean_Meta_abstractNestedProofs___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = leanh::lean_box(0);
    v___x_3632_ = leanh::lean_unsigned_to_nat(16);
    v___x_3633_ = lean_mk_array(v___x_3632_, v___x_3631_);
    return v___x_3633_;
}
pub unsafe fn _init_l_Lean_Meta_abstractNestedProofs___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3634_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractNestedProofs___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractNestedProofs___closed__0_once),
        _init_l_Lean_Meta_abstractNestedProofs___closed__0,
    );
    v___x_3635_ = leanh::lean_unsigned_to_nat(0);
    v___x_3636_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3636_, 0, v___x_3635_);
    leanh::lean_ctor_set(v___x_3636_, 1, v___x_3634_);
    return v___x_3636_;
}
pub unsafe fn l_Lean_Meta_abstractNestedProofs(
    mut v_e_3637_: *mut leanh::LeanObject,
    mut v_cache_3638_: u8,
    mut v_a_3639_: *mut leanh::LeanObject,
    mut v_a_3640_: *mut leanh::LeanObject,
    mut v_a_3641_: *mut leanh::LeanObject,
    mut v_a_3642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3649_: u8 = 0;
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_a_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3669_: u8 = 0;
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_3637_);
                v___x_3644_ =
                    l_Lean_Meta_isProof(v_e_3637_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_);
                if leanh::lean_obj_tag(v___x_3644_) == 0 {
                    v_a_3645_ = leanh::lean_ctor_get(v___x_3644_, 0);
                    v_isSharedCheck_3665_ = (!leanh::lean_is_exclusive(v___x_3644_)) as u8;
                    if v_isSharedCheck_3665_ == 0 {
                        v___x_3647_ = v___x_3644_;
                        v_isShared_3648_ = v_isSharedCheck_3665_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3645_);
                        leanh::lean_dec(v___x_3644_);
                        v___x_3647_ = leanh::lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3665_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3637_);
                    v_a_3666_ = leanh::lean_ctor_get(v___x_3644_, 0);
                    v_isSharedCheck_3673_ = (!leanh::lean_is_exclusive(v___x_3644_)) as u8;
                    if v_isSharedCheck_3673_ == 0 {
                        v___x_3668_ = v___x_3644_;
                        v_isShared_3669_ = v_isSharedCheck_3673_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3666_);
                        leanh::lean_dec(v___x_3644_);
                        v___x_3668_ = leanh::lean_box(0);
                        v_isShared_3669_ = v_isSharedCheck_3673_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3649_ = (leanh::lean_unbox(v_a_3645_) as u8);
                leanh::lean_dec(v_a_3645_);
                if v___x_3649_ == 0 {
                    leanh::lean_del_object(v___x_3647_);
                    v___x_3650_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_abstractNestedProofs___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_abstractNestedProofs___closed__1_once),
                        _init_l_Lean_Meta_abstractNestedProofs___closed__1,
                    );
                    v___x_3651_ = lean_st_mk_ref(v___x_3650_);
                    v___x_3652_ = l_Lean_Meta_AbstractNestedProofs_visit(
                        v_e_3637_,
                        v_cache_3638_,
                        v___x_3651_,
                        v_a_3639_,
                        v_a_3640_,
                        v_a_3641_,
                        v_a_3642_,
                    );
                    if leanh::lean_obj_tag(v___x_3652_) == 0 {
                        v_a_3653_ = leanh::lean_ctor_get(v___x_3652_, 0);
                        v_isSharedCheck_3661_ =
                            (!leanh::lean_is_exclusive(v___x_3652_)) as u8;
                        if v_isSharedCheck_3661_ == 0 {
                            v___x_3655_ = v___x_3652_;
                            v_isShared_3656_ = v_isSharedCheck_3661_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3653_);
                            leanh::lean_dec(v___x_3652_);
                            v___x_3655_ = leanh::lean_box(0);
                            v_isShared_3656_ = v_isSharedCheck_3661_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3651_);
                        return v___x_3652_;
                    }
                } else {
                    if v_isShared_3648_ == 0 {
                        leanh::lean_ctor_set(v___x_3647_, 0, v_e_3637_);
                        v___x_3663_ = v___x_3647_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_e_3637_);
                        v___x_3663_ = v_reuseFailAlloc_3664_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3657_ = lean_st_ref_get(v___x_3651_);
                leanh::lean_dec(v___x_3651_);
                leanh::lean_dec(v___x_3657_);
                if v_isShared_3656_ == 0 {
                    v___x_3659_ = v___x_3655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3653_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3659_;
            }
            4 => {
                return v___x_3663_;
            }
            5 => {
                if v_isShared_3669_ == 0 {
                    v___x_3671_ = v___x_3668_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
                    v___x_3671_ = v_reuseFailAlloc_3672_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3671_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_abstractNestedProofs___boxed(
    mut v_e_3674_: *mut leanh::LeanObject,
    mut v_cache_3675_: *mut leanh::LeanObject,
    mut v_a_3676_: *mut leanh::LeanObject,
    mut v_a_3677_: *mut leanh::LeanObject,
    mut v_a_3678_: *mut leanh::LeanObject,
    mut v_a_3679_: *mut leanh::LeanObject,
    mut v_a_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_boxed_3681_: u8 = 0;
    let mut v_res_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cache_boxed_3681_ = (leanh::lean_unbox(v_cache_3675_) as u8);
    v_res_3682_ = l_Lean_Meta_abstractNestedProofs(
        v_e_3674_,
        v_cache_boxed_3681_,
        v_a_3676_,
        v_a_3677_,
        v_a_3678_,
        v_a_3679_,
    );
    leanh::lean_dec(v_a_3679_);
    leanh::lean_dec_ref(v_a_3678_);
    leanh::lean_dec(v_a_3677_);
    leanh::lean_dec_ref(v_a_3676_);
    return v_res_3682_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_AbstractNestedProofs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Closure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_AbstractNestedProofs(
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
pub unsafe fn initialize_Lean_Meta_AbstractNestedProofs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Closure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AbstractNestedProofs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_AbstractNestedProofs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_AbstractNestedProofs(builtin);
}
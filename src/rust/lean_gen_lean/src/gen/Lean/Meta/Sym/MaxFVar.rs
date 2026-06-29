// Lean compiler output
// Module: Lean.Meta.Sym.MaxFVar
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_isEmpty___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_instBEqFVarId_beq,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_lastDecl, l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_index,
};
use crate::r#gen::Lean::Meta::Basic::{l_Lean_FVarId_getDecl___redArg, l_Lean_MVarId_getDecl};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_instInhabitedSymM,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value:
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
    m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value:
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
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 77, 97, 120, 70, 86, 97,
            114, 0,
        ],
    };
static mut l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 103, 101, 116, 77, 97,
            120, 70, 86, 97, 114, 63, 0,
        ],
    };
static mut l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(
    mut v_fvarId1_x3f_847_: *mut crate::leanh::LeanObject,
    mut v_fvarId2_x3f_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
    mut v_a_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut v_a_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut v_a_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_884_: u8 = 0;
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_888_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v_unused_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_fvarId1_x3f_847_) == 1 {
                    if crate::leanh::lean_obj_tag(v_fvarId2_x3f_848_) == 1 {
                        v_val_853_ = crate::leanh::lean_ctor_get(v_fvarId1_x3f_847_, 0);
                        v_val_854_ = crate::leanh::lean_ctor_get(v_fvarId2_x3f_848_, 0);
                        v___x_855_ = l_Lean_instBEqFVarId_beq(v_val_853_, v_val_854_);
                        if v___x_855_ == 0 {
                            crate::leanh::lean_inc(v_val_853_);
                            v___x_856_ = l_Lean_FVarId_getDecl___redArg(
                                v_val_853_, v_a_849_, v_a_850_, v_a_851_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_856_) == 0 {
                                v_a_857_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                                crate::leanh::lean_inc(v_a_857_);
                                crate::leanh::lean_dec_ref_known(v___x_856_, 1);
                                crate::leanh::lean_inc(v_val_854_);
                                v___x_858_ = l_Lean_FVarId_getDecl___redArg(
                                    v_val_854_, v_a_849_, v_a_850_, v_a_851_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_858_) == 0 {
                                    v_a_859_ = crate::leanh::lean_ctor_get(v___x_858_, 0);
                                    v_isSharedCheck_872_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_858_)) as u8;
                                    if v_isSharedCheck_872_ == 0 {
                                        v___x_861_ = v___x_858_;
                                        v_isShared_862_ = v_isSharedCheck_872_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_859_);
                                        crate::leanh::lean_dec(v___x_858_);
                                        v___x_861_ = crate::leanh::lean_box(0);
                                        v_isShared_862_ = v_isSharedCheck_872_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_857_);
                                    crate::leanh::lean_dec_ref_known(v_fvarId2_x3f_848_, 1);
                                    crate::leanh::lean_dec_ref_known(v_fvarId1_x3f_847_, 1);
                                    v_a_873_ = crate::leanh::lean_ctor_get(v___x_858_, 0);
                                    v_isSharedCheck_880_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_858_)) as u8;
                                    if v_isSharedCheck_880_ == 0 {
                                        v___x_875_ = v___x_858_;
                                        v_isShared_876_ = v_isSharedCheck_880_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_873_);
                                        crate::leanh::lean_dec(v___x_858_);
                                        v___x_875_ = crate::leanh::lean_box(0);
                                        v_isShared_876_ = v_isSharedCheck_880_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_fvarId2_x3f_848_, 1);
                                crate::leanh::lean_dec_ref_known(v_fvarId1_x3f_847_, 1);
                                v_a_881_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                                v_isSharedCheck_888_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_856_)) as u8;
                                if v_isSharedCheck_888_ == 0 {
                                    v___x_883_ = v___x_856_;
                                    v_isShared_884_ = v_isSharedCheck_888_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_881_);
                                    crate::leanh::lean_dec(v___x_856_);
                                    v___x_883_ = crate::leanh::lean_box(0);
                                    v_isShared_884_ = v_isSharedCheck_888_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            v_isSharedCheck_895_ =
                                (!crate::leanh::lean_is_exclusive(v_fvarId2_x3f_848_)) as u8;
                            if v_isSharedCheck_895_ == 0 {
                                v_unused_896_ = crate::leanh::lean_ctor_get(v_fvarId2_x3f_848_, 0);
                                crate::leanh::lean_dec(v_unused_896_);
                                v___x_890_ = v_fvarId2_x3f_848_;
                                v_isShared_891_ = v_isSharedCheck_895_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_fvarId2_x3f_848_);
                                v___x_890_ = crate::leanh::lean_box(0);
                                v_isShared_891_ = v_isSharedCheck_895_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId2_x3f_848_);
                        v___x_897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_897_, 0, v_fvarId1_x3f_847_);
                        return v___x_897_;
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId1_x3f_847_);
                    v___x_898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_898_, 0, v_fvarId2_x3f_848_);
                    return v___x_898_;
                }
            }
            1 => {
                v___x_863_ = l_Lean_LocalDecl_index(v_a_859_);
                crate::leanh::lean_dec(v_a_859_);
                v___x_864_ = l_Lean_LocalDecl_index(v_a_857_);
                crate::leanh::lean_dec(v_a_857_);
                v___x_865_ = lean_nat_dec_lt(v___x_863_, v___x_864_);
                crate::leanh::lean_dec(v___x_864_);
                crate::leanh::lean_dec(v___x_863_);
                if v___x_865_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_fvarId1_x3f_847_, 1);
                    if v_isShared_862_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_861_, 0, v_fvarId2_x3f_848_);
                        v___x_867_ = v___x_861_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v_fvarId2_x3f_848_);
                        v___x_867_ = v_reuseFailAlloc_868_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_fvarId2_x3f_848_, 1);
                    if v_isShared_862_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_861_, 0, v_fvarId1_x3f_847_);
                        v___x_870_ = v___x_861_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_871_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 0, v_fvarId1_x3f_847_);
                        v___x_870_ = v_reuseFailAlloc_871_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_867_;
            }
            3 => {
                return v___x_870_;
            }
            4 => {
                if v_isShared_876_ == 0 {
                    v___x_878_ = v___x_875_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
                    v___x_878_ = v_reuseFailAlloc_879_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_878_;
            }
            6 => {
                if v_isShared_884_ == 0 {
                    v___x_886_ = v___x_883_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
                    v___x_886_ = v_reuseFailAlloc_887_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_886_;
            }
            8 => {
                if v_isShared_891_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_890_, 0);
                    crate::leanh::lean_ctor_set(v___x_890_, 0, v_fvarId1_x3f_847_);
                    v___x_893_ = v___x_890_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 0, v_fvarId1_x3f_847_);
                    v___x_893_ = v_reuseFailAlloc_894_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(
    mut v_fvarId1_x3f_899_: *mut crate::leanh::LeanObject,
    mut v_fvarId2_x3f_900_: *mut crate::leanh::LeanObject,
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
    mut v_a_903_: *mut crate::leanh::LeanObject,
    mut v_a_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(
        v_fvarId1_x3f_899_,
        v_fvarId2_x3f_900_,
        v_a_901_,
        v_a_902_,
        v_a_903_,
    );
    crate::leanh::lean_dec(v_a_903_);
    crate::leanh::lean_dec_ref(v_a_902_);
    crate::leanh::lean_dec_ref(v_a_901_);
    return v_res_905_;
}
pub unsafe fn l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(
    mut v_fvarId1_x3f_906_: *mut crate::leanh::LeanObject,
    mut v_fvarId2_x3f_907_: *mut crate::leanh::LeanObject,
    mut v_a_908_: *mut crate::leanh::LeanObject,
    mut v_a_909_: *mut crate::leanh::LeanObject,
    mut v_a_910_: *mut crate::leanh::LeanObject,
    mut v_a_911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(
        v_fvarId1_x3f_906_,
        v_fvarId2_x3f_907_,
        v_a_908_,
        v_a_910_,
        v_a_911_,
    );
    return v___x_913_;
}
pub unsafe fn l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(
    mut v_fvarId1_x3f_914_: *mut crate::leanh::LeanObject,
    mut v_fvarId2_x3f_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_a_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(
        v_fvarId1_x3f_914_,
        v_fvarId2_x3f_915_,
        v_a_916_,
        v_a_917_,
        v_a_918_,
        v_a_919_,
    );
    crate::leanh::lean_dec(v_a_919_);
    crate::leanh::lean_dec_ref(v_a_918_);
    crate::leanh::lean_dec(v_a_917_);
    crate::leanh::lean_dec_ref(v_a_916_);
    return v_res_921_;
}
pub unsafe fn l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(
    mut v_e_924_: *mut crate::leanh::LeanObject,
    mut v_k_925_: *mut crate::leanh::LeanObject,
    mut v_a_926_: *mut crate::leanh::LeanObject,
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_934_: u8 = 0;
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_945_: u8 = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_954_: u8 = 0;
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_966_: u8 = 0;
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_978_: u8 = 0;
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut v___x_980_: u8 = 0;
    let mut v___x_981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_980_ = l_Lean_Expr_hasFVar(v_e_924_);
                if v___x_980_ == 0 {
                    v___x_981_ = l_Lean_Expr_hasMVar(v_e_924_);
                    v___y_934_ = v___x_981_;
                    state = 1;
                    continue;
                } else {
                    v___y_934_ = v___x_980_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_934_ == 0 {
                    crate::leanh::lean_dec_ref(v_k_925_);
                    crate::leanh::lean_dec_ref(v_e_924_);
                    v___x_935_ = crate::leanh::lean_box(0);
                    v___x_936_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_935_);
                    return v___x_936_;
                } else {
                    v___x_937_ = lean_st_ref_get(v_a_927_);
                    v_maxFVar_938_ = crate::leanh::lean_ctor_get(v___x_937_, 1);
                    crate::leanh::lean_inc_ref(v_maxFVar_938_);
                    crate::leanh::lean_dec(v___x_937_);
                    v___f_939_ =
                        l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0;
                    v___f_940_ =
                        l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1;
                    crate::leanh::lean_inc_ref(v_e_924_);
                    v___x_941_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                        v___f_939_,
                        v___f_940_,
                        v_maxFVar_938_,
                        v_e_924_,
                    );
                    crate::leanh::lean_dec_ref(v_maxFVar_938_);
                    if crate::leanh::lean_obj_tag(v___x_941_) == 1 {
                        crate::leanh::lean_dec_ref(v_k_925_);
                        crate::leanh::lean_dec_ref(v_e_924_);
                        v_val_942_ = crate::leanh::lean_ctor_get(v___x_941_, 0);
                        v_isSharedCheck_949_ = (!crate::leanh::lean_is_exclusive(v___x_941_)) as u8;
                        if v_isSharedCheck_949_ == 0 {
                            v___x_944_ = v___x_941_;
                            v_isShared_945_ = v_isSharedCheck_949_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_942_);
                            crate::leanh::lean_dec(v___x_941_);
                            v___x_944_ = crate::leanh::lean_box(0);
                            v_isShared_945_ = v_isSharedCheck_949_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_941_);
                        crate::leanh::lean_inc(v_a_931_);
                        crate::leanh::lean_inc_ref(v_a_930_);
                        crate::leanh::lean_inc(v_a_929_);
                        crate::leanh::lean_inc_ref(v_a_928_);
                        crate::leanh::lean_inc(v_a_927_);
                        crate::leanh::lean_inc_ref(v_a_926_);
                        v___x_950_ = crate::leanh::lean_apply_7(
                            v_k_925_,
                            v_a_926_,
                            v_a_927_,
                            v_a_928_,
                            v_a_929_,
                            v_a_930_,
                            v_a_931_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_950_) == 0 {
                            v_a_951_ = crate::leanh::lean_ctor_get(v___x_950_, 0);
                            v_isSharedCheck_979_ =
                                (!crate::leanh::lean_is_exclusive(v___x_950_)) as u8;
                            if v_isSharedCheck_979_ == 0 {
                                v___x_953_ = v___x_950_;
                                v_isShared_954_ = v_isSharedCheck_979_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_951_);
                                crate::leanh::lean_dec(v___x_950_);
                                v___x_953_ = crate::leanh::lean_box(0);
                                v_isShared_954_ = v_isSharedCheck_979_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_924_);
                            return v___x_950_;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_945_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_944_, 0);
                    v___x_947_ = v___x_944_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_942_);
                    v___x_947_ = v_reuseFailAlloc_948_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_947_;
            }
            4 => {
                v___x_955_ = lean_st_ref_take(v_a_927_);
                v_share_956_ = crate::leanh::lean_ctor_get(v___x_955_, 0);
                v_maxFVar_957_ = crate::leanh::lean_ctor_get(v___x_955_, 1);
                v_proofInstInfo_958_ = crate::leanh::lean_ctor_get(v___x_955_, 2);
                v_inferType_959_ = crate::leanh::lean_ctor_get(v___x_955_, 3);
                v_getLevel_960_ = crate::leanh::lean_ctor_get(v___x_955_, 4);
                v_congrInfo_961_ = crate::leanh::lean_ctor_get(v___x_955_, 5);
                v_defEqI_962_ = crate::leanh::lean_ctor_get(v___x_955_, 6);
                v_extensions_963_ = crate::leanh::lean_ctor_get(v___x_955_, 7);
                v_issues_964_ = crate::leanh::lean_ctor_get(v___x_955_, 8);
                v_canon_965_ = crate::leanh::lean_ctor_get(v___x_955_, 9);
                v_debug_966_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_955_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_978_ = (!crate::leanh::lean_is_exclusive(v___x_955_)) as u8;
                if v_isSharedCheck_978_ == 0 {
                    v___x_968_ = v___x_955_;
                    v_isShared_969_ = v_isSharedCheck_978_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_965_);
                    crate::leanh::lean_inc(v_issues_964_);
                    crate::leanh::lean_inc(v_extensions_963_);
                    crate::leanh::lean_inc(v_defEqI_962_);
                    crate::leanh::lean_inc(v_congrInfo_961_);
                    crate::leanh::lean_inc(v_getLevel_960_);
                    crate::leanh::lean_inc(v_inferType_959_);
                    crate::leanh::lean_inc(v_proofInstInfo_958_);
                    crate::leanh::lean_inc(v_maxFVar_957_);
                    crate::leanh::lean_inc(v_share_956_);
                    crate::leanh::lean_dec(v___x_955_);
                    v___x_968_ = crate::leanh::lean_box(0);
                    v_isShared_969_ = v_isSharedCheck_978_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_951_);
                v___x_970_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_939_,
                    v___f_940_,
                    v_maxFVar_957_,
                    v_e_924_,
                    v_a_951_,
                );
                if v_isShared_969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_968_, 1, v___x_970_);
                    v___x_972_ = v___x_968_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_977_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 0, v_share_956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 2, v_proofInstInfo_958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 3, v_inferType_959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 4, v_getLevel_960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 5, v_congrInfo_961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 6, v_defEqI_962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 7, v_extensions_963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 8, v_issues_964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 9, v_canon_965_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_977_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_966_,
                    );
                    v___x_972_ = v_reuseFailAlloc_977_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_973_ = lean_st_ref_set(v_a_927_, v___x_972_);
                if v_isShared_954_ == 0 {
                    v___x_975_ = v___x_953_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_976_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_951_);
                    v___x_975_ = v_reuseFailAlloc_976_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(
    mut v_e_982_: *mut crate::leanh::LeanObject,
    mut v_k_983_: *mut crate::leanh::LeanObject,
    mut v_a_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
    mut v_a_986_: *mut crate::leanh::LeanObject,
    mut v_a_987_: *mut crate::leanh::LeanObject,
    mut v_a_988_: *mut crate::leanh::LeanObject,
    mut v_a_989_: *mut crate::leanh::LeanObject,
    mut v_a_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(
        v_e_982_, v_k_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_,
    );
    crate::leanh::lean_dec(v_a_989_);
    crate::leanh::lean_dec_ref(v_a_988_);
    crate::leanh::lean_dec(v_a_987_);
    crate::leanh::lean_dec_ref(v_a_986_);
    crate::leanh::lean_dec(v_a_985_);
    crate::leanh::lean_dec_ref(v_a_984_);
    return v_res_991_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = l_Lean_Meta_Sym_instInhabitedSymM(crate::leanh::lean_box(0));
    return v___x_992_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(
    mut v_msg_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
    mut v___y_995_: *mut crate::leanh::LeanObject,
    mut v___y_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718__overap_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0,
    );
    v___x_4718__overap_1002_ = lean_panic_fn_borrowed(v___x_1001_, v_msg_993_);
    crate::leanh::lean_inc(v___y_999_);
    crate::leanh::lean_inc_ref(v___y_998_);
    crate::leanh::lean_inc(v___y_997_);
    crate::leanh::lean_inc_ref(v___y_996_);
    crate::leanh::lean_inc(v___y_995_);
    crate::leanh::lean_inc_ref(v___y_994_);
    v___x_1003_ = crate::leanh::lean_apply_7(
        v___x_4718__overap_1002_,
        v___y_994_,
        v___y_995_,
        v___y_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
        crate::leanh::lean_box(0),
    );
    return v___x_1003_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(
    mut v_msg_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
    mut v___y_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1012_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(
        v_msg_1004_,
        v___y_1005_,
        v___y_1006_,
        v___y_1007_,
        v___y_1008_,
        v___y_1009_,
        v___y_1010_,
    );
    crate::leanh::lean_dec(v___y_1010_);
    crate::leanh::lean_dec_ref(v___y_1009_);
    crate::leanh::lean_dec(v___y_1008_);
    crate::leanh::lean_dec_ref(v___y_1007_);
    crate::leanh::lean_dec(v___y_1006_);
    crate::leanh::lean_dec_ref(v___y_1005_);
    return v_res_1012_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_x_1013_: *mut crate::leanh::LeanObject,
    mut v_x_1014_: *mut crate::leanh::LeanObject,
    mut v_x_1015_: *mut crate::leanh::LeanObject,
    mut v_x_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1021_: u8 = 0;
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1017_ = crate::leanh::lean_ctor_get(v_x_1013_, 0);
                v_vs_1018_ = crate::leanh::lean_ctor_get(v_x_1013_, 1);
                v_isSharedCheck_1042_ = (!crate::leanh::lean_is_exclusive(v_x_1013_)) as u8;
                if v_isSharedCheck_1042_ == 0 {
                    v___x_1020_ = v_x_1013_;
                    v_isShared_1021_ = v_isSharedCheck_1042_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1018_);
                    crate::leanh::lean_inc(v_ks_1017_);
                    crate::leanh::lean_dec(v_x_1013_);
                    v___x_1020_ = crate::leanh::lean_box(0);
                    v_isShared_1021_ = v_isSharedCheck_1042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1022_ = lean_array_get_size(v_ks_1017_);
                v___x_1023_ = lean_nat_dec_lt(v_x_1014_, v___x_1022_);
                if v___x_1023_ == 0 {
                    crate::leanh::lean_dec(v_x_1014_);
                    v___x_1024_ = lean_array_push(v_ks_1017_, v_x_1015_);
                    v___x_1025_ = lean_array_push(v_vs_1018_, v_x_1016_);
                    if v_isShared_1021_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1020_, 1, v___x_1025_);
                        crate::leanh::lean_ctor_set(v___x_1020_, 0, v___x_1024_);
                        v___x_1027_ = v___x_1020_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1028_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1024_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1025_);
                        v___x_1027_ = v_reuseFailAlloc_1028_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1029_ = lean_array_fget_borrowed(v_ks_1017_, v_x_1014_);
                    v___x_1030_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1015_,
                            v_k_x27_1029_,
                        );
                    if v___x_1030_ == 0 {
                        if v_isShared_1021_ == 0 {
                            v___x_1032_ = v___x_1020_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1036_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_ks_1017_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_vs_1018_);
                            v___x_1032_ = v_reuseFailAlloc_1036_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1037_ = lean_array_fset(v_ks_1017_, v_x_1014_, v_x_1015_);
                        v___x_1038_ = lean_array_fset(v_vs_1018_, v_x_1014_, v_x_1016_);
                        crate::leanh::lean_dec(v_x_1014_);
                        if v_isShared_1021_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1020_, 1, v___x_1038_);
                            crate::leanh::lean_ctor_set(v___x_1020_, 0, v___x_1037_);
                            v___x_1040_ = v___x_1020_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1041_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1037_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1038_);
                            v___x_1040_ = v_reuseFailAlloc_1041_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1027_;
            }
            3 => {
                v___x_1033_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1034_ = lean_nat_add(v_x_1014_, v___x_1033_);
                crate::leanh::lean_dec(v_x_1014_);
                v_x_1013_ = v___x_1032_;
                v_x_1014_ = v___x_1034_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_n_1043_: *mut crate::leanh::LeanObject,
    mut v_k_1044_: *mut crate::leanh::LeanObject,
    mut v_v_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1047_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1043_, v___x_1046_, v_k_1044_, v_v_1045_);
    return v___x_1047_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1048_: usize = 0;
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: usize = 0;
    v___x_1048_ = 5usize;
    v___x_1049_ = 1usize;
    v___x_1050_ = lean_usize_shift_left(v___x_1049_, v___x_1048_);
    return v___x_1050_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1051_: usize = 0;
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: usize = 0;
    v___x_1051_ = 1usize;
    v___x_1052_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_1053_ = lean_usize_sub(v___x_1052_, v___x_1051_);
    return v___x_1053_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1054_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(
    mut v_x_1055_: *mut crate::leanh::LeanObject,
    mut v_x_1056_: usize,
    mut v_x_1057_: usize,
    mut v_x_1058_: *mut crate::leanh::LeanObject,
    mut v_x_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: usize = 0;
    let mut v___x_1062_: usize = 0;
    let mut v___x_1063_: usize = 0;
    let mut v___x_1064_: usize = 0;
    let mut v_j_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v_v_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1085_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1091_: u8 = 0;
    let mut v_node_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1096_: usize = 0;
    let mut v___x_1097_: usize = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1104_: u8 = 0;
    let mut v_unused_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1115_: u8 = 0;
    let mut v_ks_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: usize = 0;
    let mut v___x_1122_: u8 = 0;
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: u8 = 0;
    let mut v_reuseFailAlloc_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1055_) == 0 {
                    v_es_1060_ = crate::leanh::lean_ctor_get(v_x_1055_, 0);
                    v___x_1061_ = 5usize;
                    v___x_1062_ = 1usize;
                    v___x_1063_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1064_ = lean_usize_land(v_x_1056_, v___x_1063_);
                    v_j_1065_ = lean_usize_to_nat(v___x_1064_);
                    v___x_1066_ = lean_array_get_size(v_es_1060_);
                    v___x_1067_ = lean_nat_dec_lt(v_j_1065_, v___x_1066_);
                    if v___x_1067_ == 0 {
                        crate::leanh::lean_dec(v_j_1065_);
                        crate::leanh::lean_dec(v_x_1059_);
                        crate::leanh::lean_dec_ref(v_x_1058_);
                        return v_x_1055_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1060_);
                        v_isSharedCheck_1104_ = (!crate::leanh::lean_is_exclusive(v_x_1055_)) as u8;
                        if v_isSharedCheck_1104_ == 0 {
                            v_unused_1105_ = crate::leanh::lean_ctor_get(v_x_1055_, 0);
                            crate::leanh::lean_dec(v_unused_1105_);
                            v___x_1069_ = v_x_1055_;
                            v_isShared_1070_ = v_isSharedCheck_1104_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1055_);
                            v___x_1069_ = crate::leanh::lean_box(0);
                            v_isShared_1070_ = v_isSharedCheck_1104_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1106_ = crate::leanh::lean_ctor_get(v_x_1055_, 0);
                    v_vs_1107_ = crate::leanh::lean_ctor_get(v_x_1055_, 1);
                    v_isSharedCheck_1127_ = (!crate::leanh::lean_is_exclusive(v_x_1055_)) as u8;
                    if v_isSharedCheck_1127_ == 0 {
                        v___x_1109_ = v_x_1055_;
                        v_isShared_1110_ = v_isSharedCheck_1127_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1107_);
                        crate::leanh::lean_inc(v_ks_1106_);
                        crate::leanh::lean_dec(v_x_1055_);
                        v___x_1109_ = crate::leanh::lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1127_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1071_ = lean_array_fget(v_es_1060_, v_j_1065_);
                v___x_1072_ = crate::leanh::lean_box(0);
                v_xs_x27_1073_ = lean_array_fset(v_es_1060_, v_j_1065_, v___x_1072_);
                match crate::leanh::lean_obj_tag(v_v_1071_) {
                    0 => {
                        v_key_1080_ = crate::leanh::lean_ctor_get(v_v_1071_, 0);
                        v_val_1081_ = crate::leanh::lean_ctor_get(v_v_1071_, 1);
                        v_isSharedCheck_1091_ = (!crate::leanh::lean_is_exclusive(v_v_1071_)) as u8;
                        if v_isSharedCheck_1091_ == 0 {
                            v___x_1083_ = v_v_1071_;
                            v_isShared_1084_ = v_isSharedCheck_1091_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1081_);
                            crate::leanh::lean_inc(v_key_1080_);
                            crate::leanh::lean_dec(v_v_1071_);
                            v___x_1083_ = crate::leanh::lean_box(0);
                            v_isShared_1084_ = v_isSharedCheck_1091_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1092_ = crate::leanh::lean_ctor_get(v_v_1071_, 0);
                        v_isSharedCheck_1102_ = (!crate::leanh::lean_is_exclusive(v_v_1071_)) as u8;
                        if v_isSharedCheck_1102_ == 0 {
                            v___x_1094_ = v_v_1071_;
                            v_isShared_1095_ = v_isSharedCheck_1102_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1092_);
                            crate::leanh::lean_dec(v_v_1071_);
                            v___x_1094_ = crate::leanh::lean_box(0);
                            v_isShared_1095_ = v_isSharedCheck_1102_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1103_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1103_, 0, v_x_1058_);
                        crate::leanh::lean_ctor_set(v___x_1103_, 1, v_x_1059_);
                        v___y_1075_ = v___x_1103_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1076_ = lean_array_fset(v_xs_x27_1073_, v_j_1065_, v___y_1075_);
                crate::leanh::lean_dec(v_j_1065_);
                if v_isShared_1070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1069_, 0, v___x_1076_);
                    v___x_1078_ = v___x_1069_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1078_;
            }
            4 => {
                v___x_1085_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1058_,
                        v_key_1080_,
                    );
                if v___x_1085_ == 0 {
                    crate::leanh::lean_del_object(v___x_1083_);
                    v___x_1086_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1080_,
                        v_val_1081_,
                        v_x_1058_,
                        v_x_1059_,
                    );
                    v___x_1087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1087_, 0, v___x_1086_);
                    v___y_1075_ = v___x_1087_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1081_);
                    crate::leanh::lean_dec(v_key_1080_);
                    if v_isShared_1084_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1083_, 1, v_x_1059_);
                        crate::leanh::lean_ctor_set(v___x_1083_, 0, v_x_1058_);
                        v___x_1089_ = v___x_1083_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_x_1058_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_x_1059_);
                        v___x_1089_ = v_reuseFailAlloc_1090_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1075_ = v___x_1089_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1096_ = lean_usize_shift_right(v_x_1056_, v___x_1061_);
                v___x_1097_ = lean_usize_add(v_x_1057_, v___x_1062_);
                v___x_1098_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_1092_, v___x_1096_, v___x_1097_, v_x_1058_, v_x_1059_);
                if v_isShared_1095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1098_);
                    v___x_1100_ = v___x_1094_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
                    v___x_1100_ = v_reuseFailAlloc_1101_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1075_ = v___x_1100_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1110_ == 0 {
                    v___x_1112_ = v___x_1109_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1126_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_ks_1106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_vs_1107_);
                    v___x_1112_ = v_reuseFailAlloc_1126_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1113_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_1112_, v_x_1058_, v_x_1059_);
                v___x_1121_ = 7usize;
                v___x_1122_ = lean_usize_dec_le(v___x_1121_, v_x_1057_);
                if v___x_1122_ == 0 {
                    v___x_1123_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1113_);
                    v___x_1124_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1125_ = lean_nat_dec_lt(v___x_1123_, v___x_1124_);
                    crate::leanh::lean_dec(v___x_1123_);
                    v___y_1115_ = v___x_1125_;
                    state = 10;
                    continue;
                } else {
                    v___y_1115_ = v___x_1122_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1115_ == 0 {
                    v_ks_1116_ = crate::leanh::lean_ctor_get(v_newNode_1113_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1116_);
                    v_vs_1117_ = crate::leanh::lean_ctor_get(v_newNode_1113_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1117_);
                    crate::leanh::lean_dec_ref(v_newNode_1113_);
                    v___x_1118_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1119_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2);
                    v___x_1120_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_1057_, v_ks_1116_, v_vs_1117_, v___x_1118_, v___x_1119_);
                    crate::leanh::lean_dec_ref(v_vs_1117_);
                    crate::leanh::lean_dec_ref(v_ks_1116_);
                    return v___x_1120_;
                } else {
                    return v_newNode_1113_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(
    mut v_depth_1128_: usize,
    mut v_keys_1129_: *mut crate::leanh::LeanObject,
    mut v_vals_1130_: *mut crate::leanh::LeanObject,
    mut v_i_1131_: *mut crate::leanh::LeanObject,
    mut v_entries_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u8 = 0;
    let mut v_k_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u64 = 0;
    let mut v_h_1138_: usize = 0;
    let mut v___x_1139_: usize = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: usize = 0;
    let mut v_h_1144_: usize = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1133_ = lean_array_get_size(v_keys_1129_);
                v___x_1134_ = lean_nat_dec_lt(v_i_1131_, v___x_1133_);
                if v___x_1134_ == 0 {
                    crate::leanh::lean_dec(v_i_1131_);
                    return v_entries_1132_;
                } else {
                    v_k_1135_ = lean_array_fget_borrowed(v_keys_1129_, v_i_1131_);
                    v_v_1136_ = lean_array_fget_borrowed(v_vals_1130_, v_i_1131_);
                    v___x_1137_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1135_);
                    v_h_1138_ = lean_uint64_to_usize(v___x_1137_);
                    v___x_1139_ = 5usize;
                    v___x_1140_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1141_ = 1usize;
                    v___x_1142_ = lean_usize_sub(v_depth_1128_, v___x_1141_);
                    v___x_1143_ = lean_usize_mul(v___x_1139_, v___x_1142_);
                    v_h_1144_ = lean_usize_shift_right(v_h_1138_, v___x_1143_);
                    v___x_1145_ = lean_nat_add(v_i_1131_, v___x_1140_);
                    crate::leanh::lean_dec(v_i_1131_);
                    crate::leanh::lean_inc(v_v_1136_);
                    crate::leanh::lean_inc(v_k_1135_);
                    v___x_1146_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_1132_, v_h_1144_, v_depth_1128_, v_k_1135_, v_v_1136_);
                    v_i_1131_ = v___x_1145_;
                    v_entries_1132_ = v___x_1146_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_depth_1148_: *mut crate::leanh::LeanObject,
    mut v_keys_1149_: *mut crate::leanh::LeanObject,
    mut v_vals_1150_: *mut crate::leanh::LeanObject,
    mut v_i_1151_: *mut crate::leanh::LeanObject,
    mut v_entries_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1153_: usize = 0;
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1153_ = crate::leanh::lean_unbox_usize(v_depth_1148_);
    crate::leanh::lean_dec(v_depth_1148_);
    v_res_1154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1153_, v_keys_1149_, v_vals_1150_, v_i_1151_, v_entries_1152_);
    crate::leanh::lean_dec_ref(v_vals_1150_);
    crate::leanh::lean_dec_ref(v_keys_1149_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_1155_: *mut crate::leanh::LeanObject,
    mut v_x_1156_: *mut crate::leanh::LeanObject,
    mut v_x_1157_: *mut crate::leanh::LeanObject,
    mut v_x_1158_: *mut crate::leanh::LeanObject,
    mut v_x_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5211__boxed_1160_: usize = 0;
    let mut v_x_5212__boxed_1161_: usize = 0;
    let mut v_res_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5211__boxed_1160_ = crate::leanh::lean_unbox_usize(v_x_1156_);
    crate::leanh::lean_dec(v_x_1156_);
    v_x_5212__boxed_1161_ = crate::leanh::lean_unbox_usize(v_x_1157_);
    crate::leanh::lean_dec(v_x_1157_);
    v_res_1162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_1155_, v_x_5211__boxed_1160_, v_x_5212__boxed_1161_, v_x_1158_, v_x_1159_);
    return v_res_1162_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(
    mut v_x_1163_: *mut crate::leanh::LeanObject,
    mut v_x_1164_: *mut crate::leanh::LeanObject,
    mut v_x_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1166_: u64 = 0;
    let mut v___x_1167_: usize = 0;
    let mut v___x_1168_: usize = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1166_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1164_);
    v___x_1167_ = lean_uint64_to_usize(v___x_1166_);
    v___x_1168_ = 1usize;
    v___x_1169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_1163_, v___x_1167_, v___x_1168_, v_x_1164_, v_x_1165_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(
    mut v_keys_1170_: *mut crate::leanh::LeanObject,
    mut v_vals_1171_: *mut crate::leanh::LeanObject,
    mut v_i_1172_: *mut crate::leanh::LeanObject,
    mut v_k_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1174_ = lean_array_get_size(v_keys_1170_);
                v___x_1175_ = lean_nat_dec_lt(v_i_1172_, v___x_1174_);
                if v___x_1175_ == 0 {
                    crate::leanh::lean_dec(v_i_1172_);
                    v___x_1176_ = crate::leanh::lean_box(0);
                    return v___x_1176_;
                } else {
                    v_k_x27_1177_ = lean_array_fget_borrowed(v_keys_1170_, v_i_1172_);
                    v___x_1178_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1173_,
                            v_k_x27_1177_,
                        );
                    if v___x_1178_ == 0 {
                        v___x_1179_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1180_ = lean_nat_add(v_i_1172_, v___x_1179_);
                        crate::leanh::lean_dec(v_i_1172_);
                        v_i_1172_ = v___x_1180_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1182_ = lean_array_fget_borrowed(v_vals_1171_, v_i_1172_);
                        crate::leanh::lean_dec(v_i_1172_);
                        crate::leanh::lean_inc(v___x_1182_);
                        v___x_1183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
                        return v___x_1183_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_keys_1184_: *mut crate::leanh::LeanObject,
    mut v_vals_1185_: *mut crate::leanh::LeanObject,
    mut v_i_1186_: *mut crate::leanh::LeanObject,
    mut v_k_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1188_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_1184_, v_vals_1185_, v_i_1186_, v_k_1187_);
    crate::leanh::lean_dec_ref(v_k_1187_);
    crate::leanh::lean_dec_ref(v_vals_1185_);
    crate::leanh::lean_dec_ref(v_keys_1184_);
    return v_res_1188_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(
    mut v_x_1189_: *mut crate::leanh::LeanObject,
    mut v_x_1190_: usize,
    mut v_x_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: usize = 0;
    let mut v___x_1195_: usize = 0;
    let mut v___x_1196_: usize = 0;
    let mut v_j_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: usize = 0;
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1189_) == 0 {
                    v_es_1192_ = crate::leanh::lean_ctor_get(v_x_1189_, 0);
                    v___x_1193_ = crate::leanh::lean_box(2);
                    v___x_1194_ = 5usize;
                    v___x_1195_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1196_ = lean_usize_land(v_x_1190_, v___x_1195_);
                    v_j_1197_ = lean_usize_to_nat(v___x_1196_);
                    v___x_1198_ = lean_array_get_borrowed(v___x_1193_, v_es_1192_, v_j_1197_);
                    crate::leanh::lean_dec(v_j_1197_);
                    match crate::leanh::lean_obj_tag(v___x_1198_) {
                        0 => {
                            v_key_1199_ = crate::leanh::lean_ctor_get(v___x_1198_, 0);
                            v_val_1200_ = crate::leanh::lean_ctor_get(v___x_1198_, 1);
                            v___x_1201_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1191_, v_key_1199_);
                            if v___x_1201_ == 0 {
                                v___x_1202_ = crate::leanh::lean_box(0);
                                return v___x_1202_;
                            } else {
                                crate::leanh::lean_inc(v_val_1200_);
                                v___x_1203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1203_, 0, v_val_1200_);
                                return v___x_1203_;
                            }
                        }
                        1 => {
                            v_node_1204_ = crate::leanh::lean_ctor_get(v___x_1198_, 0);
                            v___x_1205_ = lean_usize_shift_right(v_x_1190_, v___x_1194_);
                            v_x_1189_ = v_node_1204_;
                            v_x_1190_ = v___x_1205_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1207_ = crate::leanh::lean_box(0);
                            return v___x_1207_;
                        }
                    }
                } else {
                    v_ks_1208_ = crate::leanh::lean_ctor_get(v_x_1189_, 0);
                    v_vs_1209_ = crate::leanh::lean_ctor_get(v_x_1189_, 1);
                    v___x_1210_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1211_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_1208_, v_vs_1209_, v___x_1210_, v_x_1191_);
                    return v___x_1211_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_1212_: *mut crate::leanh::LeanObject,
    mut v_x_1213_: *mut crate::leanh::LeanObject,
    mut v_x_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5411__boxed_1215_: usize = 0;
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5411__boxed_1215_ = crate::leanh::lean_unbox_usize(v_x_1213_);
    crate::leanh::lean_dec(v_x_1213_);
    v_res_1216_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_1212_, v_x_5411__boxed_1215_, v_x_1214_);
    crate::leanh::lean_dec_ref(v_x_1214_);
    crate::leanh::lean_dec_ref(v_x_1212_);
    return v_res_1216_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(
    mut v_x_1217_: *mut crate::leanh::LeanObject,
    mut v_x_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: u64 = 0;
    let mut v___x_1220_: usize = 0;
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1218_);
    v___x_1220_ = lean_uint64_to_usize(v___x_1219_);
    v___x_1221_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_1217_, v___x_1220_, v_x_1218_);
    return v___x_1221_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(
    mut v_x_1222_: *mut crate::leanh::LeanObject,
    mut v_x_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(
            v_x_1222_, v_x_1223_,
        );
    crate::leanh::lean_dec_ref(v_x_1223_);
    crate::leanh::lean_dec_ref(v_x_1222_);
    return v_res_1224_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1228_ = l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2;
    v___x_1229_ = crate::leanh::lean_unsigned_to_nat(37);
    v___x_1230_ = crate::leanh::lean_unsigned_to_nat(52);
    v___x_1231_ = l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1;
    v___x_1232_ = l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0;
    v___x_1233_ = l_mkPanicMessageWithDecl(
        v___x_1232_,
        v___x_1231_,
        v___x_1230_,
        v___x_1229_,
        v___x_1228_,
    );
    return v___x_1233_;
}
pub unsafe fn l_Lean_Meta_Sym_getMaxFVar_x3f(
    mut v_e_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
    mut v_a_1236_: *mut crate::leanh::LeanObject,
    mut v_a_1237_: *mut crate::leanh::LeanObject,
    mut v_a_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1259_: u8 = 0;
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_a_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1286_: u8 = 0;
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v___y_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1315_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut v___y_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1367_: u8 = 0;
    let mut v___y_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1385_: u8 = 0;
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_fvarId_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1404_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1440_: u8 = 0;
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1444_: u8 = 0;
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: u8 = 0;
    let mut v_fn_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: u8 = 0;
    let mut v_binderType_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: u8 = 0;
    let mut v_expr_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1506_: u8 = 0;
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1515_: u8 = 0;
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1519_: u8 = 0;
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1536_: u8 = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1539_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut v___x_1550_: u8 = 0;
    let mut v___x_1551_: u8 = 0;
    let mut v_struct_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1554_: u8 = 0;
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1584_: u8 = 0;
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: u8 = 0;
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_1234_) {
                1 => {
                    v_fvarId_1399_ = crate::leanh::lean_ctor_get(v_e_1234_, 0);
                    crate::leanh::lean_inc(v_fvarId_1399_);
                    crate::leanh::lean_dec_ref_known(v_e_1234_, 1);
                    v___x_1400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1400_, 0, v_fvarId_1399_);
                    v___x_1401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1401_, 0, v___x_1400_);
                    return v___x_1401_;
                }
                2 => {
                    v_mvarId_1402_ = crate::leanh::lean_ctor_get(v_e_1234_, 0);
                    v___x_1445_ = l_Lean_Expr_hasFVar(v_e_1234_);
                    if v___x_1445_ == 0 {
                        v___x_1446_ = l_Lean_Expr_hasMVar(v_e_1234_);
                        v___y_1404_ = v___x_1446_;
                        state = 23;
                        continue;
                    } else {
                        v___y_1404_ = v___x_1445_;
                        state = 23;
                        continue;
                    }
                }
                5 => {
                    v_fn_1447_ = crate::leanh::lean_ctor_get(v_e_1234_, 0);
                    v_arg_1448_ = crate::leanh::lean_ctor_get(v_e_1234_, 1);
                    v___x_1469_ = l_Lean_Expr_hasFVar(v_e_1234_);
                    if v___x_1469_ == 0 {
                        v___x_1470_ = l_Lean_Expr_hasMVar(v_e_1234_);
                        v___y_1450_ = v___x_1470_;
                        state = 30;
                        continue;
                    } else {
                        v___y_1450_ = v___x_1469_;
                        state = 30;
                        continue;
                    }
                }
                6 => {
                    v_binderType_1471_ = crate::leanh::lean_ctor_get(v_e_1234_, 1);
                    v_body_1472_ = crate::leanh::lean_ctor_get(v_e_1234_, 2);
                    crate::leanh::lean_inc_ref(v_body_1472_);
                    crate::leanh::lean_inc_ref(v_binderType_1471_);
                    v_d_1358_ = v_binderType_1471_;
                    v_b_1359_ = v_body_1472_;
                    v___y_1360_ = v_a_1235_;
                    v___y_1361_ = v_a_1236_;
                    v___y_1362_ = v_a_1237_;
                    v___y_1363_ = v_a_1238_;
                    v___y_1364_ = v_a_1239_;
                    v___y_1365_ = v_a_1240_;
                    state = 17;
                    continue;
                }
                7 => {
                    v_binderType_1473_ = crate::leanh::lean_ctor_get(v_e_1234_, 1);
                    v_body_1474_ = crate::leanh::lean_ctor_get(v_e_1234_, 2);
                    crate::leanh::lean_inc_ref(v_body_1474_);
                    crate::leanh::lean_inc_ref(v_binderType_1473_);
                    v_d_1358_ = v_binderType_1473_;
                    v_b_1359_ = v_body_1474_;
                    v___y_1360_ = v_a_1235_;
                    v___y_1361_ = v_a_1236_;
                    v___y_1362_ = v_a_1237_;
                    v___y_1363_ = v_a_1238_;
                    v___y_1364_ = v_a_1239_;
                    v___y_1365_ = v_a_1240_;
                    state = 17;
                    continue;
                }
                8 => {
                    v_type_1475_ = crate::leanh::lean_ctor_get(v_e_1234_, 1);
                    v_value_1476_ = crate::leanh::lean_ctor_get(v_e_1234_, 2);
                    v_body_1477_ = crate::leanh::lean_ctor_get(v_e_1234_, 3);
                    v___x_1502_ = l_Lean_Expr_hasFVar(v_e_1234_);
                    if v___x_1502_ == 0 {
                        v___x_1503_ = l_Lean_Expr_hasMVar(v_e_1234_);
                        v___y_1479_ = v___x_1503_;
                        state = 33;
                        continue;
                    } else {
                        v___y_1479_ = v___x_1502_;
                        state = 33;
                        continue;
                    }
                }
                10 => {
                    v_expr_1504_ = crate::leanh::lean_ctor_get(v_e_1234_, 1);
                    crate::leanh::lean_inc_ref(v_expr_1504_);
                    crate::leanh::lean_dec_ref_known(v_e_1234_, 2);
                    v___x_1550_ = l_Lean_Expr_hasFVar(v_expr_1504_);
                    if v___x_1550_ == 0 {
                        v___x_1551_ = l_Lean_Expr_hasMVar(v_expr_1504_);
                        v___y_1506_ = v___x_1551_;
                        state = 36;
                        continue;
                    } else {
                        v___y_1506_ = v___x_1550_;
                        state = 36;
                        continue;
                    }
                }
                11 => {
                    v_struct_1552_ = crate::leanh::lean_ctor_get(v_e_1234_, 2);
                    v___x_1598_ = l_Lean_Expr_hasFVar(v_e_1234_);
                    if v___x_1598_ == 0 {
                        v___x_1599_ = l_Lean_Expr_hasMVar(v_e_1234_);
                        v___y_1554_ = v___x_1599_;
                        state = 43;
                        continue;
                    } else {
                        v___y_1554_ = v___x_1598_;
                        state = 43;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_1234_);
                    v___x_1600_ = crate::leanh::lean_box(0);
                    v___x_1601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1601_, 0, v___x_1600_);
                    return v___x_1601_;
                }
            },
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1243_) == 0 {
                    v_a_1244_ = crate::leanh::lean_ctor_get(v___y_1243_, 0);
                    v_isSharedCheck_1272_ = (!crate::leanh::lean_is_exclusive(v___y_1243_)) as u8;
                    if v_isSharedCheck_1272_ == 0 {
                        v___x_1246_ = v___y_1243_;
                        v_isShared_1247_ = v_isSharedCheck_1272_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1244_);
                        crate::leanh::lean_dec(v___y_1243_);
                        v___x_1246_ = crate::leanh::lean_box(0);
                        v_isShared_1247_ = v_isSharedCheck_1272_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1234_);
                    return v___y_1243_;
                }
            }
            2 => {
                v___x_1248_ = lean_st_ref_take(v_a_1236_);
                v_share_1249_ = crate::leanh::lean_ctor_get(v___x_1248_, 0);
                v_maxFVar_1250_ = crate::leanh::lean_ctor_get(v___x_1248_, 1);
                v_proofInstInfo_1251_ = crate::leanh::lean_ctor_get(v___x_1248_, 2);
                v_inferType_1252_ = crate::leanh::lean_ctor_get(v___x_1248_, 3);
                v_getLevel_1253_ = crate::leanh::lean_ctor_get(v___x_1248_, 4);
                v_congrInfo_1254_ = crate::leanh::lean_ctor_get(v___x_1248_, 5);
                v_defEqI_1255_ = crate::leanh::lean_ctor_get(v___x_1248_, 6);
                v_extensions_1256_ = crate::leanh::lean_ctor_get(v___x_1248_, 7);
                v_issues_1257_ = crate::leanh::lean_ctor_get(v___x_1248_, 8);
                v_canon_1258_ = crate::leanh::lean_ctor_get(v___x_1248_, 9);
                v_debug_1259_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1248_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1271_ = (!crate::leanh::lean_is_exclusive(v___x_1248_)) as u8;
                if v_isSharedCheck_1271_ == 0 {
                    v___x_1261_ = v___x_1248_;
                    v_isShared_1262_ = v_isSharedCheck_1271_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1258_);
                    crate::leanh::lean_inc(v_issues_1257_);
                    crate::leanh::lean_inc(v_extensions_1256_);
                    crate::leanh::lean_inc(v_defEqI_1255_);
                    crate::leanh::lean_inc(v_congrInfo_1254_);
                    crate::leanh::lean_inc(v_getLevel_1253_);
                    crate::leanh::lean_inc(v_inferType_1252_);
                    crate::leanh::lean_inc(v_proofInstInfo_1251_);
                    crate::leanh::lean_inc(v_maxFVar_1250_);
                    crate::leanh::lean_inc(v_share_1249_);
                    crate::leanh::lean_dec(v___x_1248_);
                    v___x_1261_ = crate::leanh::lean_box(0);
                    v_isShared_1262_ = v_isSharedCheck_1271_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_1244_);
                v___x_1263_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_1250_, v_e_1234_, v_a_1244_);
                if v_isShared_1262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1261_, 1, v___x_1263_);
                    v___x_1265_ = v___x_1261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_share_1249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_proofInstInfo_1251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_inferType_1252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_getLevel_1253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 5, v_congrInfo_1254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_defEqI_1255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_extensions_1256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_issues_1257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 9, v_canon_1258_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1270_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1259_,
                    );
                    v___x_1265_ = v_reuseFailAlloc_1270_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1266_ = lean_st_ref_set(v_a_1236_, v___x_1265_);
                if v_isShared_1247_ == 0 {
                    v___x_1268_ = v___x_1246_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1244_);
                    v___x_1268_ = v_reuseFailAlloc_1269_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1268_;
            }
            6 => {
                v___x_1275_ = lean_st_ref_take(v_a_1236_);
                v_share_1276_ = crate::leanh::lean_ctor_get(v___x_1275_, 0);
                v_maxFVar_1277_ = crate::leanh::lean_ctor_get(v___x_1275_, 1);
                v_proofInstInfo_1278_ = crate::leanh::lean_ctor_get(v___x_1275_, 2);
                v_inferType_1279_ = crate::leanh::lean_ctor_get(v___x_1275_, 3);
                v_getLevel_1280_ = crate::leanh::lean_ctor_get(v___x_1275_, 4);
                v_congrInfo_1281_ = crate::leanh::lean_ctor_get(v___x_1275_, 5);
                v_defEqI_1282_ = crate::leanh::lean_ctor_get(v___x_1275_, 6);
                v_extensions_1283_ = crate::leanh::lean_ctor_get(v___x_1275_, 7);
                v_issues_1284_ = crate::leanh::lean_ctor_get(v___x_1275_, 8);
                v_canon_1285_ = crate::leanh::lean_ctor_get(v___x_1275_, 9);
                v_debug_1286_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1275_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v___x_1275_)) as u8;
                if v_isSharedCheck_1296_ == 0 {
                    v___x_1288_ = v___x_1275_;
                    v_isShared_1289_ = v_isSharedCheck_1296_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1285_);
                    crate::leanh::lean_inc(v_issues_1284_);
                    crate::leanh::lean_inc(v_extensions_1283_);
                    crate::leanh::lean_inc(v_defEqI_1282_);
                    crate::leanh::lean_inc(v_congrInfo_1281_);
                    crate::leanh::lean_inc(v_getLevel_1280_);
                    crate::leanh::lean_inc(v_inferType_1279_);
                    crate::leanh::lean_inc(v_proofInstInfo_1278_);
                    crate::leanh::lean_inc(v_maxFVar_1277_);
                    crate::leanh::lean_inc(v_share_1276_);
                    crate::leanh::lean_dec(v___x_1275_);
                    v___x_1288_ = crate::leanh::lean_box(0);
                    v_isShared_1289_ = v_isSharedCheck_1296_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc(v_a_1274_);
                v___x_1290_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_1277_, v_e_1234_, v_a_1274_);
                if v_isShared_1289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1288_, 1, v___x_1290_);
                    v___x_1292_ = v___x_1288_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_share_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_proofInstInfo_1278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_inferType_1279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_getLevel_1280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 5, v_congrInfo_1281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 6, v_defEqI_1282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 7, v_extensions_1283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 8, v_issues_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 9, v_canon_1285_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1295_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1286_,
                    );
                    v___x_1292_ = v_reuseFailAlloc_1295_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1293_ = lean_st_ref_set(v_a_1236_, v___x_1292_);
                v___x_1294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1294_, 0, v_a_1274_);
                return v___x_1294_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v___y_1299_) == 0 {
                    v_a_1300_ = crate::leanh::lean_ctor_get(v___y_1299_, 0);
                    v_isSharedCheck_1328_ = (!crate::leanh::lean_is_exclusive(v___y_1299_)) as u8;
                    if v_isSharedCheck_1328_ == 0 {
                        v___x_1302_ = v___y_1299_;
                        v_isShared_1303_ = v_isSharedCheck_1328_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1300_);
                        crate::leanh::lean_dec(v___y_1299_);
                        v___x_1302_ = crate::leanh::lean_box(0);
                        v_isShared_1303_ = v_isSharedCheck_1328_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1234_);
                    return v___y_1299_;
                }
            }
            10 => {
                v___x_1304_ = lean_st_ref_take(v___y_1298_);
                v_share_1305_ = crate::leanh::lean_ctor_get(v___x_1304_, 0);
                v_maxFVar_1306_ = crate::leanh::lean_ctor_get(v___x_1304_, 1);
                v_proofInstInfo_1307_ = crate::leanh::lean_ctor_get(v___x_1304_, 2);
                v_inferType_1308_ = crate::leanh::lean_ctor_get(v___x_1304_, 3);
                v_getLevel_1309_ = crate::leanh::lean_ctor_get(v___x_1304_, 4);
                v_congrInfo_1310_ = crate::leanh::lean_ctor_get(v___x_1304_, 5);
                v_defEqI_1311_ = crate::leanh::lean_ctor_get(v___x_1304_, 6);
                v_extensions_1312_ = crate::leanh::lean_ctor_get(v___x_1304_, 7);
                v_issues_1313_ = crate::leanh::lean_ctor_get(v___x_1304_, 8);
                v_canon_1314_ = crate::leanh::lean_ctor_get(v___x_1304_, 9);
                v_debug_1315_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1304_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1327_ = (!crate::leanh::lean_is_exclusive(v___x_1304_)) as u8;
                if v_isSharedCheck_1327_ == 0 {
                    v___x_1317_ = v___x_1304_;
                    v_isShared_1318_ = v_isSharedCheck_1327_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1314_);
                    crate::leanh::lean_inc(v_issues_1313_);
                    crate::leanh::lean_inc(v_extensions_1312_);
                    crate::leanh::lean_inc(v_defEqI_1311_);
                    crate::leanh::lean_inc(v_congrInfo_1310_);
                    crate::leanh::lean_inc(v_getLevel_1309_);
                    crate::leanh::lean_inc(v_inferType_1308_);
                    crate::leanh::lean_inc(v_proofInstInfo_1307_);
                    crate::leanh::lean_inc(v_maxFVar_1306_);
                    crate::leanh::lean_inc(v_share_1305_);
                    crate::leanh::lean_dec(v___x_1304_);
                    v___x_1317_ = crate::leanh::lean_box(0);
                    v_isShared_1318_ = v_isSharedCheck_1327_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc(v_a_1300_);
                v___x_1319_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_1306_, v_e_1234_, v_a_1300_);
                if v_isShared_1318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1317_, 1, v___x_1319_);
                    v___x_1321_ = v___x_1317_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1326_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_share_1305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_proofInstInfo_1307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 3, v_inferType_1308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 4, v_getLevel_1309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 5, v_congrInfo_1310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 6, v_defEqI_1311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 7, v_extensions_1312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 8, v_issues_1313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 9, v_canon_1314_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1326_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1315_,
                    );
                    v___x_1321_ = v_reuseFailAlloc_1326_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1322_ = lean_st_ref_set(v___y_1298_, v___x_1321_);
                if v_isShared_1303_ == 0 {
                    v___x_1324_ = v___x_1302_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1300_);
                    v___x_1324_ = v_reuseFailAlloc_1325_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1324_;
            }
            14 => {
                if v___y_1338_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1337_);
                    crate::leanh::lean_dec_ref(v___y_1331_);
                    crate::leanh::lean_dec_ref(v_e_1234_);
                    v___x_1339_ = crate::leanh::lean_box(0);
                    v___x_1340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1340_, 0, v___x_1339_);
                    return v___x_1340_;
                } else {
                    v___x_1341_ = lean_st_ref_get(v___y_1330_);
                    v_maxFVar_1342_ = crate::leanh::lean_ctor_get(v___x_1341_, 1);
                    crate::leanh::lean_inc_ref(v_maxFVar_1342_);
                    crate::leanh::lean_dec(v___x_1341_);
                    v___x_1343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_1342_, v_e_1234_);
                    crate::leanh::lean_dec_ref(v_maxFVar_1342_);
                    if crate::leanh::lean_obj_tag(v___x_1343_) == 1 {
                        crate::leanh::lean_dec_ref(v___y_1337_);
                        crate::leanh::lean_dec_ref(v___y_1331_);
                        crate::leanh::lean_dec_ref(v_e_1234_);
                        v_val_1344_ = crate::leanh::lean_ctor_get(v___x_1343_, 0);
                        v_isSharedCheck_1351_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1343_)) as u8;
                        if v_isSharedCheck_1351_ == 0 {
                            v___x_1346_ = v___x_1343_;
                            v_isShared_1347_ = v_isSharedCheck_1351_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1344_);
                            crate::leanh::lean_dec(v___x_1343_);
                            v___x_1346_ = crate::leanh::lean_box(0);
                            v_isShared_1347_ = v_isSharedCheck_1351_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1343_);
                        v___x_1352_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                            v___y_1337_,
                            v___y_1336_,
                            v___y_1330_,
                            v___y_1335_,
                            v___y_1332_,
                            v___y_1334_,
                            v___y_1333_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1352_) == 0 {
                            v_a_1353_ = crate::leanh::lean_ctor_get(v___x_1352_, 0);
                            crate::leanh::lean_inc(v_a_1353_);
                            crate::leanh::lean_dec_ref_known(v___x_1352_, 1);
                            v___x_1354_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                                v___y_1331_,
                                v___y_1336_,
                                v___y_1330_,
                                v___y_1335_,
                                v___y_1332_,
                                v___y_1334_,
                                v___y_1333_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1354_) == 0 {
                                v_a_1355_ = crate::leanh::lean_ctor_get(v___x_1354_, 0);
                                crate::leanh::lean_inc(v_a_1355_);
                                crate::leanh::lean_dec_ref_known(v___x_1354_, 1);
                                v___x_1356_ =
                                    l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(
                                        v_a_1353_,
                                        v_a_1355_,
                                        v___y_1335_,
                                        v___y_1334_,
                                        v___y_1333_,
                                    );
                                v___y_1298_ = v___y_1330_;
                                v___y_1299_ = v___x_1356_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1353_);
                                v___y_1298_ = v___y_1330_;
                                v___y_1299_ = v___x_1354_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_1331_);
                            v___y_1298_ = v___y_1330_;
                            v___y_1299_ = v___x_1352_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_1347_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1346_, 0);
                    v___x_1349_ = v___x_1346_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_val_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1350_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1349_;
            }
            17 => {
                v___x_1366_ = l_Lean_Expr_hasFVar(v_e_1234_);
                if v___x_1366_ == 0 {
                    v___x_1367_ = l_Lean_Expr_hasMVar(v_e_1234_);
                    v___y_1330_ = v___y_1361_;
                    v___y_1331_ = v_b_1359_;
                    v___y_1332_ = v___y_1363_;
                    v___y_1333_ = v___y_1365_;
                    v___y_1334_ = v___y_1364_;
                    v___y_1335_ = v___y_1362_;
                    v___y_1336_ = v___y_1360_;
                    v___y_1337_ = v_d_1358_;
                    v___y_1338_ = v___x_1367_;
                    state = 14;
                    continue;
                } else {
                    v___y_1330_ = v___y_1361_;
                    v___y_1331_ = v_b_1359_;
                    v___y_1332_ = v___y_1363_;
                    v___y_1333_ = v___y_1365_;
                    v___y_1334_ = v___y_1364_;
                    v___y_1335_ = v___y_1362_;
                    v___y_1336_ = v___y_1360_;
                    v___y_1337_ = v_d_1358_;
                    v___y_1338_ = v___x_1366_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if crate::leanh::lean_obj_tag(v___y_1369_) == 0 {
                    v_a_1370_ = crate::leanh::lean_ctor_get(v___y_1369_, 0);
                    v_isSharedCheck_1398_ = (!crate::leanh::lean_is_exclusive(v___y_1369_)) as u8;
                    if v_isSharedCheck_1398_ == 0 {
                        v___x_1372_ = v___y_1369_;
                        v_isShared_1373_ = v_isSharedCheck_1398_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1370_);
                        crate::leanh::lean_dec(v___y_1369_);
                        v___x_1372_ = crate::leanh::lean_box(0);
                        v_isShared_1373_ = v_isSharedCheck_1398_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1234_);
                    return v___y_1369_;
                }
            }
            19 => {
                v___x_1374_ = lean_st_ref_take(v_a_1236_);
                v_share_1375_ = crate::leanh::lean_ctor_get(v___x_1374_, 0);
                v_maxFVar_1376_ = crate::leanh::lean_ctor_get(v___x_1374_, 1);
                v_proofInstInfo_1377_ = crate::leanh::lean_ctor_get(v___x_1374_, 2);
                v_inferType_1378_ = crate::leanh::lean_ctor_get(v___x_1374_, 3);
                v_getLevel_1379_ = crate::leanh::lean_ctor_get(v___x_1374_, 4);
                v_congrInfo_1380_ = crate::leanh::lean_ctor_get(v___x_1374_, 5);
                v_defEqI_1381_ = crate::leanh::lean_ctor_get(v___x_1374_, 6);
                v_extensions_1382_ = crate::leanh::lean_ctor_get(v___x_1374_, 7);
                v_issues_1383_ = crate::leanh::lean_ctor_get(v___x_1374_, 8);
                v_canon_1384_ = crate::leanh::lean_ctor_get(v___x_1374_, 9);
                v_debug_1385_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1374_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1397_ = (!crate::leanh::lean_is_exclusive(v___x_1374_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v___x_1387_ = v___x_1374_;
                    v_isShared_1388_ = v_isSharedCheck_1397_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1384_);
                    crate::leanh::lean_inc(v_issues_1383_);
                    crate::leanh::lean_inc(v_extensions_1382_);
                    crate::leanh::lean_inc(v_defEqI_1381_);
                    crate::leanh::lean_inc(v_congrInfo_1380_);
                    crate::leanh::lean_inc(v_getLevel_1379_);
                    crate::leanh::lean_inc(v_inferType_1378_);
                    crate::leanh::lean_inc(v_proofInstInfo_1377_);
                    crate::leanh::lean_inc(v_maxFVar_1376_);
                    crate::leanh::lean_inc(v_share_1375_);
                    crate::leanh::lean_dec(v___x_1374_);
                    v___x_1387_ = crate::leanh::lean_box(0);
                    v_isShared_1388_ = v_isSharedCheck_1397_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                crate::leanh::lean_inc(v_a_1370_);
                v___x_1389_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_1376_, v_e_1234_, v_a_1370_);
                if v_isShared_1388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1387_, 1, v___x_1389_);
                    v___x_1391_ = v___x_1387_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_share_1375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_proofInstInfo_1377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_inferType_1378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_getLevel_1379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 5, v_congrInfo_1380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 6, v_defEqI_1381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 7, v_extensions_1382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 8, v_issues_1383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 9, v_canon_1384_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1396_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1385_,
                    );
                    v___x_1391_ = v_reuseFailAlloc_1396_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1392_ = lean_st_ref_set(v_a_1236_, v___x_1391_);
                if v_isShared_1373_ == 0 {
                    v___x_1394_ = v___x_1372_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1370_);
                    v___x_1394_ = v_reuseFailAlloc_1395_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1394_;
            }
            23 => {
                if v___y_1404_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_1234_, 1);
                    v___x_1405_ = crate::leanh::lean_box(0);
                    v___x_1406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
                    return v___x_1406_;
                } else {
                    v___x_1407_ = lean_st_ref_get(v_a_1236_);
                    v_maxFVar_1408_ = crate::leanh::lean_ctor_get(v___x_1407_, 1);
                    crate::leanh::lean_inc_ref(v_maxFVar_1408_);
                    crate::leanh::lean_dec(v___x_1407_);
                    v___x_1409_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_1408_, v_e_1234_);
                    crate::leanh::lean_dec_ref(v_maxFVar_1408_);
                    if crate::leanh::lean_obj_tag(v___x_1409_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_e_1234_, 1);
                        v_val_1410_ = crate::leanh::lean_ctor_get(v___x_1409_, 0);
                        v_isSharedCheck_1417_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1409_)) as u8;
                        if v_isSharedCheck_1417_ == 0 {
                            v___x_1412_ = v___x_1409_;
                            v_isShared_1413_ = v_isSharedCheck_1417_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1410_);
                            crate::leanh::lean_dec(v___x_1409_);
                            v___x_1412_ = crate::leanh::lean_box(0);
                            v_isShared_1413_ = v_isSharedCheck_1417_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1409_);
                        crate::leanh::lean_inc(v_mvarId_1402_);
                        v___x_1418_ = l_Lean_MVarId_getDecl(
                            v_mvarId_1402_,
                            v_a_1237_,
                            v_a_1238_,
                            v_a_1239_,
                            v_a_1240_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1418_) == 0 {
                            v_a_1419_ = crate::leanh::lean_ctor_get(v___x_1418_, 0);
                            crate::leanh::lean_inc(v_a_1419_);
                            crate::leanh::lean_dec_ref_known(v___x_1418_, 1);
                            v_lctx_1420_ = crate::leanh::lean_ctor_get(v_a_1419_, 1);
                            crate::leanh::lean_inc_ref(v_lctx_1420_);
                            crate::leanh::lean_dec(v_a_1419_);
                            v_decls_1421_ = crate::leanh::lean_ctor_get(v_lctx_1420_, 1);
                            v___x_1422_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_1421_);
                            if v___x_1422_ == 0 {
                                v___x_1423_ = l_Lean_LocalContext_lastDecl(v_lctx_1420_);
                                crate::leanh::lean_dec_ref(v_lctx_1420_);
                                if crate::leanh::lean_obj_tag(v___x_1423_) == 1 {
                                    v_val_1424_ = crate::leanh::lean_ctor_get(v___x_1423_, 0);
                                    v_isSharedCheck_1432_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1423_)) as u8;
                                    if v_isSharedCheck_1432_ == 0 {
                                        v___x_1426_ = v___x_1423_;
                                        v_isShared_1427_ = v_isSharedCheck_1432_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_1424_);
                                        crate::leanh::lean_dec(v___x_1423_);
                                        v___x_1426_ = crate::leanh::lean_box(0);
                                        v_isShared_1427_ = v_isSharedCheck_1432_;
                                        state = 26;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_1423_);
                                    v___x_1433_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once
                                        ),
                                        _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3,
                                    );
                                    v___x_1434_ =
                                        l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(
                                            v___x_1433_,
                                            v_a_1235_,
                                            v_a_1236_,
                                            v_a_1237_,
                                            v_a_1238_,
                                            v_a_1239_,
                                            v_a_1240_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_1434_) == 0 {
                                        v_a_1435_ = crate::leanh::lean_ctor_get(v___x_1434_, 0);
                                        crate::leanh::lean_inc(v_a_1435_);
                                        crate::leanh::lean_dec_ref_known(v___x_1434_, 1);
                                        v_a_1274_ = v_a_1435_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_e_1234_, 1);
                                        return v___x_1434_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_lctx_1420_);
                                v___x_1436_ = crate::leanh::lean_box(0);
                                v_a_1274_ = v___x_1436_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_1234_, 1);
                            v_a_1437_ = crate::leanh::lean_ctor_get(v___x_1418_, 0);
                            v_isSharedCheck_1444_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1418_)) as u8;
                            if v_isSharedCheck_1444_ == 0 {
                                v___x_1439_ = v___x_1418_;
                                v_isShared_1440_ = v_isSharedCheck_1444_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1437_);
                                crate::leanh::lean_dec(v___x_1418_);
                                v___x_1439_ = crate::leanh::lean_box(0);
                                v_isShared_1440_ = v_isSharedCheck_1444_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                }
            }
            24 => {
                if v_isShared_1413_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1412_, 0);
                    v___x_1415_ = v___x_1412_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_val_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1416_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1415_;
            }
            26 => {
                v___x_1428_ = l_Lean_LocalDecl_fvarId(v_val_1424_);
                crate::leanh::lean_dec(v_val_1424_);
                if v_isShared_1427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1428_);
                    v___x_1430_ = v___x_1426_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
                    v___x_1430_ = v_reuseFailAlloc_1431_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v_a_1274_ = v___x_1430_;
                state = 6;
                continue;
            }
            28 => {
                if v_isShared_1440_ == 0 {
                    v___x_1442_ = v___x_1439_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
                    v___x_1442_ = v_reuseFailAlloc_1443_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1442_;
            }
            30 => {
                if v___y_1450_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_1234_, 2);
                    v___x_1451_ = crate::leanh::lean_box(0);
                    v___x_1452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1452_, 0, v___x_1451_);
                    return v___x_1452_;
                } else {
                    v___x_1453_ = lean_st_ref_get(v_a_1236_);
                    v_maxFVar_1454_ = crate::leanh::lean_ctor_get(v___x_1453_, 1);
                    crate::leanh::lean_inc_ref(v_maxFVar_1454_);
                    crate::leanh::lean_dec(v___x_1453_);
                    v___x_1455_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_1454_, v_e_1234_);
                    crate::leanh::lean_dec_ref(v_maxFVar_1454_);
                    if crate::leanh::lean_obj_tag(v___x_1455_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_e_1234_, 2);
                        v_val_1456_ = crate::leanh::lean_ctor_get(v___x_1455_, 0);
                        v_isSharedCheck_1463_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1455_)) as u8;
                        if v_isSharedCheck_1463_ == 0 {
                            v___x_1458_ = v___x_1455_;
                            v_isShared_1459_ = v_isSharedCheck_1463_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1456_);
                            crate::leanh::lean_dec(v___x_1455_);
                            v___x_1458_ = crate::leanh::lean_box(0);
                            v_isShared_1459_ = v_isSharedCheck_1463_;
                            state = 31;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1455_);
                        crate::leanh::lean_inc_ref(v_fn_1447_);
                        v___x_1464_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                            v_fn_1447_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_,
                            v_a_1240_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1464_) == 0 {
                            v_a_1465_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                            crate::leanh::lean_inc(v_a_1465_);
                            crate::leanh::lean_dec_ref_known(v___x_1464_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1448_);
                            v___x_1466_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                                v_arg_1448_,
                                v_a_1235_,
                                v_a_1236_,
                                v_a_1237_,
                                v_a_1238_,
                                v_a_1239_,
                                v_a_1240_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1466_) == 0 {
                                v_a_1467_ = crate::leanh::lean_ctor_get(v___x_1466_, 0);
                                crate::leanh::lean_inc(v_a_1467_);
                                crate::leanh::lean_dec_ref_known(v___x_1466_, 1);
                                v___x_1468_ =
                                    l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(
                                        v_a_1465_, v_a_1467_, v_a_1237_, v_a_1239_, v_a_1240_,
                                    );
                                v___y_1369_ = v___x_1468_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1465_);
                                v___y_1369_ = v___x_1466_;
                                state = 18;
                                continue;
                            }
                        } else {
                            v___y_1369_ = v___x_1464_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            31 => {
                if v_isShared_1459_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1458_, 0);
                    v___x_1461_ = v___x_1458_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_val_1456_);
                    v___x_1461_ = v_reuseFailAlloc_1462_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1461_;
            }
            33 => {
                if v___y_1479_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_1234_, 4);
                    v___x_1480_ = crate::leanh::lean_box(0);
                    v___x_1481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1481_, 0, v___x_1480_);
                    return v___x_1481_;
                } else {
                    v___x_1482_ = lean_st_ref_get(v_a_1236_);
                    v_maxFVar_1483_ = crate::leanh::lean_ctor_get(v___x_1482_, 1);
                    crate::leanh::lean_inc_ref(v_maxFVar_1483_);
                    crate::leanh::lean_dec(v___x_1482_);
                    v___x_1484_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_1483_, v_e_1234_);
                    crate::leanh::lean_dec_ref(v_maxFVar_1483_);
                    if crate::leanh::lean_obj_tag(v___x_1484_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_e_1234_, 4);
                        v_val_1485_ = crate::leanh::lean_ctor_get(v___x_1484_, 0);
                        v_isSharedCheck_1492_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1484_)) as u8;
                        if v_isSharedCheck_1492_ == 0 {
                            v___x_1487_ = v___x_1484_;
                            v_isShared_1488_ = v_isSharedCheck_1492_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1485_);
                            crate::leanh::lean_dec(v___x_1484_);
                            v___x_1487_ = crate::leanh::lean_box(0);
                            v_isShared_1488_ = v_isSharedCheck_1492_;
                            state = 34;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1484_);
                        crate::leanh::lean_inc_ref(v_type_1475_);
                        v___x_1493_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                            v_type_1475_,
                            v_a_1235_,
                            v_a_1236_,
                            v_a_1237_,
                            v_a_1238_,
                            v_a_1239_,
                            v_a_1240_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1493_) == 0 {
                            v_a_1494_ = crate::leanh::lean_ctor_get(v___x_1493_, 0);
                            crate::leanh::lean_inc(v_a_1494_);
                            crate::leanh::lean_dec_ref_known(v___x_1493_, 1);
                            crate::leanh::lean_inc_ref(v_value_1476_);
                            v___x_1495_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                                v_value_1476_,
                                v_a_1235_,
                                v_a_1236_,
                                v_a_1237_,
                                v_a_1238_,
                                v_a_1239_,
                                v_a_1240_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1495_) == 0 {
                                v_a_1496_ = crate::leanh::lean_ctor_get(v___x_1495_, 0);
                                crate::leanh::lean_inc(v_a_1496_);
                                crate::leanh::lean_dec_ref_known(v___x_1495_, 1);
                                v___x_1497_ =
                                    l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(
                                        v_a_1494_, v_a_1496_, v_a_1237_, v_a_1239_, v_a_1240_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_1497_) == 0 {
                                    v_a_1498_ = crate::leanh::lean_ctor_get(v___x_1497_, 0);
                                    crate::leanh::lean_inc(v_a_1498_);
                                    crate::leanh::lean_dec_ref_known(v___x_1497_, 1);
                                    crate::leanh::lean_inc_ref(v_body_1477_);
                                    v___x_1499_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                                        v_body_1477_,
                                        v_a_1235_,
                                        v_a_1236_,
                                        v_a_1237_,
                                        v_a_1238_,
                                        v_a_1239_,
                                        v_a_1240_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1499_) == 0 {
                                        v_a_1500_ = crate::leanh::lean_ctor_get(v___x_1499_, 0);
                                        crate::leanh::lean_inc(v_a_1500_);
                                        crate::leanh::lean_dec_ref_known(v___x_1499_, 1);
                                        v___x_1501_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_1498_, v_a_1500_, v_a_1237_, v_a_1239_, v_a_1240_);
                                        v___y_1243_ = v___x_1501_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_1498_);
                                        v___y_1243_ = v___x_1499_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_1243_ = v___x_1497_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1494_);
                                v___y_1243_ = v___x_1495_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_1243_ = v___x_1493_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            34 => {
                if v_isShared_1488_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1487_, 0);
                    v___x_1490_ = v___x_1487_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_val_1485_);
                    v___x_1490_ = v_reuseFailAlloc_1491_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1490_;
            }
            36 => {
                if v___y_1506_ == 0 {
                    crate::leanh::lean_dec_ref(v_expr_1504_);
                    v___x_1507_ = crate::leanh::lean_box(0);
                    v___x_1508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1508_, 0, v___x_1507_);
                    return v___x_1508_;
                } else {
                    v___x_1509_ = lean_st_ref_get(v_a_1236_);
                    v_maxFVar_1510_ = crate::leanh::lean_ctor_get(v___x_1509_, 1);
                    crate::leanh::lean_inc_ref(v_maxFVar_1510_);
                    crate::leanh::lean_dec(v___x_1509_);
                    v___x_1511_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_1510_, v_expr_1504_);
                    crate::leanh::lean_dec_ref(v_maxFVar_1510_);
                    if crate::leanh::lean_obj_tag(v___x_1511_) == 1 {
                        crate::leanh::lean_dec_ref(v_expr_1504_);
                        v_val_1512_ = crate::leanh::lean_ctor_get(v___x_1511_, 0);
                        v_isSharedCheck_1519_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1511_)) as u8;
                        if v_isSharedCheck_1519_ == 0 {
                            v___x_1514_ = v___x_1511_;
                            v_isShared_1515_ = v_isSharedCheck_1519_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1512_);
                            crate::leanh::lean_dec(v___x_1511_);
                            v___x_1514_ = crate::leanh::lean_box(0);
                            v_isShared_1515_ = v_isSharedCheck_1519_;
                            state = 37;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1511_);
                        crate::leanh::lean_inc_ref(v_expr_1504_);
                        v___x_1520_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                            v_expr_1504_,
                            v_a_1235_,
                            v_a_1236_,
                            v_a_1237_,
                            v_a_1238_,
                            v_a_1239_,
                            v_a_1240_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1520_) == 0 {
                            v_a_1521_ = crate::leanh::lean_ctor_get(v___x_1520_, 0);
                            v_isSharedCheck_1549_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1520_)) as u8;
                            if v_isSharedCheck_1549_ == 0 {
                                v___x_1523_ = v___x_1520_;
                                v_isShared_1524_ = v_isSharedCheck_1549_;
                                state = 39;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1521_);
                                crate::leanh::lean_dec(v___x_1520_);
                                v___x_1523_ = crate::leanh::lean_box(0);
                                v_isShared_1524_ = v_isSharedCheck_1549_;
                                state = 39;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_expr_1504_);
                            return v___x_1520_;
                        }
                    }
                }
            }
            37 => {
                if v_isShared_1515_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1514_, 0);
                    v___x_1517_ = v___x_1514_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_val_1512_);
                    v___x_1517_ = v_reuseFailAlloc_1518_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1517_;
            }
            39 => {
                v___x_1525_ = lean_st_ref_take(v_a_1236_);
                v_share_1526_ = crate::leanh::lean_ctor_get(v___x_1525_, 0);
                v_maxFVar_1527_ = crate::leanh::lean_ctor_get(v___x_1525_, 1);
                v_proofInstInfo_1528_ = crate::leanh::lean_ctor_get(v___x_1525_, 2);
                v_inferType_1529_ = crate::leanh::lean_ctor_get(v___x_1525_, 3);
                v_getLevel_1530_ = crate::leanh::lean_ctor_get(v___x_1525_, 4);
                v_congrInfo_1531_ = crate::leanh::lean_ctor_get(v___x_1525_, 5);
                v_defEqI_1532_ = crate::leanh::lean_ctor_get(v___x_1525_, 6);
                v_extensions_1533_ = crate::leanh::lean_ctor_get(v___x_1525_, 7);
                v_issues_1534_ = crate::leanh::lean_ctor_get(v___x_1525_, 8);
                v_canon_1535_ = crate::leanh::lean_ctor_get(v___x_1525_, 9);
                v_debug_1536_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1525_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1548_ = (!crate::leanh::lean_is_exclusive(v___x_1525_)) as u8;
                if v_isSharedCheck_1548_ == 0 {
                    v___x_1538_ = v___x_1525_;
                    v_isShared_1539_ = v_isSharedCheck_1548_;
                    state = 40;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1535_);
                    crate::leanh::lean_inc(v_issues_1534_);
                    crate::leanh::lean_inc(v_extensions_1533_);
                    crate::leanh::lean_inc(v_defEqI_1532_);
                    crate::leanh::lean_inc(v_congrInfo_1531_);
                    crate::leanh::lean_inc(v_getLevel_1530_);
                    crate::leanh::lean_inc(v_inferType_1529_);
                    crate::leanh::lean_inc(v_proofInstInfo_1528_);
                    crate::leanh::lean_inc(v_maxFVar_1527_);
                    crate::leanh::lean_inc(v_share_1526_);
                    crate::leanh::lean_dec(v___x_1525_);
                    v___x_1538_ = crate::leanh::lean_box(0);
                    v_isShared_1539_ = v_isSharedCheck_1548_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                crate::leanh::lean_inc(v_a_1521_);
                v___x_1540_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_1527_, v_expr_1504_, v_a_1521_);
                if v_isShared_1539_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1538_, 1, v___x_1540_);
                    v___x_1542_ = v___x_1538_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_share_1526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_proofInstInfo_1528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_inferType_1529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_getLevel_1530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 5, v_congrInfo_1531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 6, v_defEqI_1532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 7, v_extensions_1533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 8, v_issues_1534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 9, v_canon_1535_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1547_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1536_,
                    );
                    v___x_1542_ = v_reuseFailAlloc_1547_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v___x_1543_ = lean_st_ref_set(v_a_1236_, v___x_1542_);
                if v_isShared_1524_ == 0 {
                    v___x_1545_ = v___x_1523_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1521_);
                    v___x_1545_ = v_reuseFailAlloc_1546_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1545_;
            }
            43 => {
                if v___y_1554_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_1234_, 3);
                    v___x_1555_ = crate::leanh::lean_box(0);
                    v___x_1556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1556_, 0, v___x_1555_);
                    return v___x_1556_;
                } else {
                    v___x_1557_ = lean_st_ref_get(v_a_1236_);
                    v_maxFVar_1558_ = crate::leanh::lean_ctor_get(v___x_1557_, 1);
                    crate::leanh::lean_inc_ref(v_maxFVar_1558_);
                    crate::leanh::lean_dec(v___x_1557_);
                    v___x_1559_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_1558_, v_e_1234_);
                    crate::leanh::lean_dec_ref(v_maxFVar_1558_);
                    if crate::leanh::lean_obj_tag(v___x_1559_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_e_1234_, 3);
                        v_val_1560_ = crate::leanh::lean_ctor_get(v___x_1559_, 0);
                        v_isSharedCheck_1567_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1559_)) as u8;
                        if v_isSharedCheck_1567_ == 0 {
                            v___x_1562_ = v___x_1559_;
                            v_isShared_1563_ = v_isSharedCheck_1567_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1560_);
                            crate::leanh::lean_dec(v___x_1559_);
                            v___x_1562_ = crate::leanh::lean_box(0);
                            v_isShared_1563_ = v_isSharedCheck_1567_;
                            state = 44;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1559_);
                        crate::leanh::lean_inc_ref(v_struct_1552_);
                        v___x_1568_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
                            v_struct_1552_,
                            v_a_1235_,
                            v_a_1236_,
                            v_a_1237_,
                            v_a_1238_,
                            v_a_1239_,
                            v_a_1240_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1568_) == 0 {
                            v_a_1569_ = crate::leanh::lean_ctor_get(v___x_1568_, 0);
                            v_isSharedCheck_1597_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1568_)) as u8;
                            if v_isSharedCheck_1597_ == 0 {
                                v___x_1571_ = v___x_1568_;
                                v_isShared_1572_ = v_isSharedCheck_1597_;
                                state = 46;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1569_);
                                crate::leanh::lean_dec(v___x_1568_);
                                v___x_1571_ = crate::leanh::lean_box(0);
                                v_isShared_1572_ = v_isSharedCheck_1597_;
                                state = 46;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_1234_, 3);
                            return v___x_1568_;
                        }
                    }
                }
            }
            44 => {
                if v_isShared_1563_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1562_, 0);
                    v___x_1565_ = v___x_1562_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_val_1560_);
                    v___x_1565_ = v_reuseFailAlloc_1566_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_1565_;
            }
            46 => {
                v___x_1573_ = lean_st_ref_take(v_a_1236_);
                v_share_1574_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                v_maxFVar_1575_ = crate::leanh::lean_ctor_get(v___x_1573_, 1);
                v_proofInstInfo_1576_ = crate::leanh::lean_ctor_get(v___x_1573_, 2);
                v_inferType_1577_ = crate::leanh::lean_ctor_get(v___x_1573_, 3);
                v_getLevel_1578_ = crate::leanh::lean_ctor_get(v___x_1573_, 4);
                v_congrInfo_1579_ = crate::leanh::lean_ctor_get(v___x_1573_, 5);
                v_defEqI_1580_ = crate::leanh::lean_ctor_get(v___x_1573_, 6);
                v_extensions_1581_ = crate::leanh::lean_ctor_get(v___x_1573_, 7);
                v_issues_1582_ = crate::leanh::lean_ctor_get(v___x_1573_, 8);
                v_canon_1583_ = crate::leanh::lean_ctor_get(v___x_1573_, 9);
                v_debug_1584_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1573_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1596_ = (!crate::leanh::lean_is_exclusive(v___x_1573_)) as u8;
                if v_isSharedCheck_1596_ == 0 {
                    v___x_1586_ = v___x_1573_;
                    v_isShared_1587_ = v_isSharedCheck_1596_;
                    state = 47;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1583_);
                    crate::leanh::lean_inc(v_issues_1582_);
                    crate::leanh::lean_inc(v_extensions_1581_);
                    crate::leanh::lean_inc(v_defEqI_1580_);
                    crate::leanh::lean_inc(v_congrInfo_1579_);
                    crate::leanh::lean_inc(v_getLevel_1578_);
                    crate::leanh::lean_inc(v_inferType_1577_);
                    crate::leanh::lean_inc(v_proofInstInfo_1576_);
                    crate::leanh::lean_inc(v_maxFVar_1575_);
                    crate::leanh::lean_inc(v_share_1574_);
                    crate::leanh::lean_dec(v___x_1573_);
                    v___x_1586_ = crate::leanh::lean_box(0);
                    v_isShared_1587_ = v_isSharedCheck_1596_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                crate::leanh::lean_inc(v_a_1569_);
                v___x_1588_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_1575_, v_e_1234_, v_a_1569_);
                if v_isShared_1587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1588_);
                    v___x_1590_ = v___x_1586_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_share_1574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_proofInstInfo_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_inferType_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_getLevel_1578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 5, v_congrInfo_1579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 6, v_defEqI_1580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 7, v_extensions_1581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 8, v_issues_1582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 9, v_canon_1583_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1595_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1584_,
                    );
                    v___x_1590_ = v_reuseFailAlloc_1595_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                v___x_1591_ = lean_st_ref_set(v_a_1236_, v___x_1590_);
                if v_isShared_1572_ == 0 {
                    v___x_1593_ = v___x_1571_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1569_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(
    mut v_e_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1610_ = l_Lean_Meta_Sym_getMaxFVar_x3f(
        v_e_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_,
    );
    crate::leanh::lean_dec(v_a_1608_);
    crate::leanh::lean_dec_ref(v_a_1607_);
    crate::leanh::lean_dec(v_a_1606_);
    crate::leanh::lean_dec_ref(v_a_1605_);
    crate::leanh::lean_dec(v_a_1604_);
    crate::leanh::lean_dec_ref(v_a_1603_);
    return v_res_1610_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(
    mut v_00_u03b2_1611_: *mut crate::leanh::LeanObject,
    mut v_x_1612_: *mut crate::leanh::LeanObject,
    mut v_x_1613_: *mut crate::leanh::LeanObject,
    mut v_x_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(
            v_x_1612_, v_x_1613_, v_x_1614_,
        );
    return v___x_1615_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(
    mut v_00_u03b2_1616_: *mut crate::leanh::LeanObject,
    mut v_x_1617_: *mut crate::leanh::LeanObject,
    mut v_x_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1619_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(
            v_x_1617_, v_x_1618_,
        );
    return v___x_1619_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(
    mut v_00_u03b2_1620_: *mut crate::leanh::LeanObject,
    mut v_x_1621_: *mut crate::leanh::LeanObject,
    mut v_x_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(
        v_00_u03b2_1620_,
        v_x_1621_,
        v_x_1622_,
    );
    crate::leanh::lean_dec_ref(v_x_1622_);
    crate::leanh::lean_dec_ref(v_x_1621_);
    return v_res_1623_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(
    mut v_00_u03b2_1624_: *mut crate::leanh::LeanObject,
    mut v_x_1625_: *mut crate::leanh::LeanObject,
    mut v_x_1626_: usize,
    mut v_x_1627_: usize,
    mut v_x_1628_: *mut crate::leanh::LeanObject,
    mut v_x_1629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_1625_, v_x_1626_, v_x_1627_, v_x_1628_, v_x_1629_);
    return v___x_1630_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1631_: *mut crate::leanh::LeanObject,
    mut v_x_1632_: *mut crate::leanh::LeanObject,
    mut v_x_1633_: *mut crate::leanh::LeanObject,
    mut v_x_1634_: *mut crate::leanh::LeanObject,
    mut v_x_1635_: *mut crate::leanh::LeanObject,
    mut v_x_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6109__boxed_1637_: usize = 0;
    let mut v_x_6110__boxed_1638_: usize = 0;
    let mut v_res_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6109__boxed_1637_ = crate::leanh::lean_unbox_usize(v_x_1633_);
    crate::leanh::lean_dec(v_x_1633_);
    v_x_6110__boxed_1638_ = crate::leanh::lean_unbox_usize(v_x_1634_);
    crate::leanh::lean_dec(v_x_1634_);
    v_res_1639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_1631_, v_x_1632_, v_x_6109__boxed_1637_, v_x_6110__boxed_1638_, v_x_1635_, v_x_1636_);
    return v_res_1639_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(
    mut v_00_u03b2_1640_: *mut crate::leanh::LeanObject,
    mut v_x_1641_: *mut crate::leanh::LeanObject,
    mut v_x_1642_: usize,
    mut v_x_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_1641_, v_x_1642_, v_x_1643_);
    return v___x_1644_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_1645_: *mut crate::leanh::LeanObject,
    mut v_x_1646_: *mut crate::leanh::LeanObject,
    mut v_x_1647_: *mut crate::leanh::LeanObject,
    mut v_x_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6126__boxed_1649_: usize = 0;
    let mut v_res_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6126__boxed_1649_ = crate::leanh::lean_unbox_usize(v_x_1647_);
    crate::leanh::lean_dec(v_x_1647_);
    v_res_1650_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_1645_, v_x_1646_, v_x_6126__boxed_1649_, v_x_1648_);
    crate::leanh::lean_dec_ref(v_x_1648_);
    crate::leanh::lean_dec_ref(v_x_1646_);
    return v_res_1650_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1651_: *mut crate::leanh::LeanObject,
    mut v_n_1652_: *mut crate::leanh::LeanObject,
    mut v_k_1653_: *mut crate::leanh::LeanObject,
    mut v_v_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_1652_, v_k_1653_, v_v_1654_);
    return v___x_1655_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1656_: *mut crate::leanh::LeanObject,
    mut v_depth_1657_: usize,
    mut v_keys_1658_: *mut crate::leanh::LeanObject,
    mut v_vals_1659_: *mut crate::leanh::LeanObject,
    mut v_heq_1660_: *mut crate::leanh::LeanObject,
    mut v_i_1661_: *mut crate::leanh::LeanObject,
    mut v_entries_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_1657_, v_keys_1658_, v_vals_1659_, v_i_1661_, v_entries_1662_);
    return v___x_1663_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_1664_: *mut crate::leanh::LeanObject,
    mut v_depth_1665_: *mut crate::leanh::LeanObject,
    mut v_keys_1666_: *mut crate::leanh::LeanObject,
    mut v_vals_1667_: *mut crate::leanh::LeanObject,
    mut v_heq_1668_: *mut crate::leanh::LeanObject,
    mut v_i_1669_: *mut crate::leanh::LeanObject,
    mut v_entries_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1671_: usize = 0;
    let mut v_res_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1671_ = crate::leanh::lean_unbox_usize(v_depth_1665_);
    crate::leanh::lean_dec(v_depth_1665_);
    v_res_1672_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_1664_, v_depth_boxed_1671_, v_keys_1666_, v_vals_1667_, v_heq_1668_, v_i_1669_, v_entries_1670_);
    crate::leanh::lean_dec_ref(v_vals_1667_);
    crate::leanh::lean_dec_ref(v_keys_1666_);
    return v_res_1672_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(
    mut v_00_u03b2_1673_: *mut crate::leanh::LeanObject,
    mut v_keys_1674_: *mut crate::leanh::LeanObject,
    mut v_vals_1675_: *mut crate::leanh::LeanObject,
    mut v_heq_1676_: *mut crate::leanh::LeanObject,
    mut v_i_1677_: *mut crate::leanh::LeanObject,
    mut v_k_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1679_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_1674_, v_vals_1675_, v_i_1677_, v_k_1678_);
    return v___x_1679_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_1680_: *mut crate::leanh::LeanObject,
    mut v_keys_1681_: *mut crate::leanh::LeanObject,
    mut v_vals_1682_: *mut crate::leanh::LeanObject,
    mut v_heq_1683_: *mut crate::leanh::LeanObject,
    mut v_i_1684_: *mut crate::leanh::LeanObject,
    mut v_k_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_1680_, v_keys_1681_, v_vals_1682_, v_heq_1683_, v_i_1684_, v_k_1685_);
    crate::leanh::lean_dec_ref(v_k_1685_);
    crate::leanh::lean_dec_ref(v_vals_1682_);
    crate::leanh::lean_dec_ref(v_keys_1681_);
    return v_res_1686_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1687_: *mut crate::leanh::LeanObject,
    mut v_x_1688_: *mut crate::leanh::LeanObject,
    mut v_x_1689_: *mut crate::leanh::LeanObject,
    mut v_x_1690_: *mut crate::leanh::LeanObject,
    mut v_x_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1688_, v_x_1689_, v_x_1690_, v_x_1691_);
    return v___x_1692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_MaxFVar(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_MaxFVar(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_MaxFVar(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_MaxFVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_MaxFVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_MaxFVar(builtin);
}

// Lean compiler output
// Module: Lean.Compiler.LCNF.Closure
// Imports: Lean.Util.ForEachExprWhere Lean.Compiler.LCNF.CompilerM
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_mk_array,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_mod,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg,
    l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg, l_Lean_Compiler_LCNF_findParam_x3f___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_hash, l_Lean_Expr_isFVar___boxed,
    l_Lean_FVarIdSet_insert, l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash,
};
use crate::r#gen::Lean::Util::ForEachExprWhere::{
    initialize_Lean_Util_ForEachExprWhere, l_Lean_ForEachExprWhere_initCache,
    runtime_initialize_Lean_Util_ForEachExprWhere,
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0: usize = 0;
pub static l_Lean_Compiler_LCNF_Closure_collectType___closed__0_value:
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
    m_fun: l_Lean_Expr_isFVar___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Closure_collectType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67,
        108, 111, 115, 117, 114, 101, 46, 99, 111, 108, 108, 101, 99, 116, 70, 86, 97, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67,
        108, 111, 115, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1474_: *mut leanh::LeanObject,
    mut v_x_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u64 = 0;
    let mut v___x_1484_: u64 = 0;
    let mut v___x_1485_: u64 = 0;
    let mut v_fold_1486_: u64 = 0;
    let mut v___x_1487_: u64 = 0;
    let mut v___x_1488_: u64 = 0;
    let mut v___x_1489_: u64 = 0;
    let mut v___x_1490_: usize = 0;
    let mut v___x_1491_: usize = 0;
    let mut v___x_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1475_) == 0 {
                    return v_x_1474_;
                } else {
                    v_key_1476_ = leanh::lean_ctor_get(v_x_1475_, 0);
                    v_value_1477_ = leanh::lean_ctor_get(v_x_1475_, 1);
                    v_tail_1478_ = leanh::lean_ctor_get(v_x_1475_, 2);
                    v_isSharedCheck_1501_ = (!leanh::lean_is_exclusive(v_x_1475_)) as u8;
                    if v_isSharedCheck_1501_ == 0 {
                        v___x_1480_ = v_x_1475_;
                        v_isShared_1481_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1478_);
                        leanh::lean_inc(v_value_1477_);
                        leanh::lean_inc(v_key_1476_);
                        leanh::lean_dec(v_x_1475_);
                        v___x_1480_ = leanh::lean_box(0);
                        v_isShared_1481_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1482_ = lean_array_get_size(v_x_1474_);
                v___x_1483_ = l_Lean_instHashableFVarId_hash(v_key_1476_);
                v___x_1484_ = 32u64;
                v___x_1485_ = lean_uint64_shift_right(v___x_1483_, v___x_1484_);
                v_fold_1486_ = lean_uint64_xor(v___x_1483_, v___x_1485_);
                v___x_1487_ = 16u64;
                v___x_1488_ = lean_uint64_shift_right(v_fold_1486_, v___x_1487_);
                v___x_1489_ = lean_uint64_xor(v_fold_1486_, v___x_1488_);
                v___x_1490_ = lean_uint64_to_usize(v___x_1489_);
                v___x_1491_ = lean_usize_of_nat(v___x_1482_);
                v___x_1492_ = 1usize;
                v___x_1493_ = lean_usize_sub(v___x_1491_, v___x_1492_);
                v___x_1494_ = lean_usize_land(v___x_1490_, v___x_1493_);
                v___x_1495_ = lean_array_uget_borrowed(v_x_1474_, v___x_1494_);
                leanh::lean_inc(v___x_1495_);
                if v_isShared_1481_ == 0 {
                    leanh::lean_ctor_set(v___x_1480_, 2, v___x_1495_);
                    v___x_1497_ = v___x_1480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_key_1476_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_value_1477_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 2, v___x_1495_);
                    v___x_1497_ = v_reuseFailAlloc_1500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1498_ = lean_array_uset(v_x_1474_, v___x_1494_, v___x_1497_);
                v_x_1474_ = v___x_1498_;
                v_x_1475_ = v_tail_1478_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(
    mut v_i_1502_: *mut leanh::LeanObject,
    mut v_source_1503_: *mut leanh::LeanObject,
    mut v_target_1504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v_es_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1505_ = lean_array_get_size(v_source_1503_);
                v___x_1506_ = lean_nat_dec_lt(v_i_1502_, v___x_1505_);
                if v___x_1506_ == 0 {
                    leanh::lean_dec_ref(v_source_1503_);
                    leanh::lean_dec(v_i_1502_);
                    return v_target_1504_;
                } else {
                    v_es_1507_ = lean_array_fget(v_source_1503_, v_i_1502_);
                    v___x_1508_ = leanh::lean_box(0);
                    v_source_1509_ = lean_array_fset(v_source_1503_, v_i_1502_, v___x_1508_);
                    v_target_1510_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1504_, v_es_1507_);
                    v___x_1511_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1512_ = lean_nat_add(v_i_1502_, v___x_1511_);
                    leanh::lean_dec(v_i_1502_);
                    v_i_1502_ = v___x_1512_;
                    v_source_1503_ = v_source_1509_;
                    v_target_1504_ = v_target_1510_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(
    mut v_data_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = lean_array_get_size(v_data_1514_);
    v___x_1516_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1517_ = lean_nat_mul(v___x_1515_, v___x_1516_);
    v___x_1518_ = leanh::lean_unsigned_to_nat(0);
    v___x_1519_ = leanh::lean_box(0);
    v___x_1520_ = lean_mk_array(v_nbuckets_1517_, v___x_1519_);
    v___x_1521_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(v___x_1518_, v_data_1514_, v___x_1520_);
    return v___x_1521_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(
    mut v_a_1522_: *mut leanh::LeanObject,
    mut v_x_1523_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1524_: u8 = 0;
    let mut v_key_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1523_) == 0 {
                    v___x_1524_ = 0;
                    return v___x_1524_;
                } else {
                    v_key_1525_ = leanh::lean_ctor_get(v_x_1523_, 0);
                    v_tail_1526_ = leanh::lean_ctor_get(v_x_1523_, 2);
                    v___x_1527_ = l_Lean_instBEqFVarId_beq(v_key_1525_, v_a_1522_);
                    if v___x_1527_ == 0 {
                        v_x_1523_ = v_tail_1526_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1527_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg___boxed(
    mut v_a_1529_: *mut leanh::LeanObject,
    mut v_x_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1531_: u8 = 0;
    let mut v_r_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_1529_, v_x_1530_);
    leanh::lean_dec(v_x_1530_);
    leanh::lean_dec(v_a_1529_);
    v_r_1532_ = leanh::lean_box((v_res_1531_) as usize);
    return v_r_1532_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(
    mut v_m_1533_: *mut leanh::LeanObject,
    mut v_a_1534_: *mut leanh::LeanObject,
    mut v_b_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u64 = 0;
    let mut v___x_1540_: u64 = 0;
    let mut v___x_1541_: u64 = 0;
    let mut v_fold_1542_: u64 = 0;
    let mut v___x_1543_: u64 = 0;
    let mut v___x_1544_: u64 = 0;
    let mut v___x_1545_: u64 = 0;
    let mut v___x_1546_: usize = 0;
    let mut v___x_1547_: usize = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: usize = 0;
    let mut v___x_1550_: usize = 0;
    let mut v_bkt_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v_val_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut v_unused_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1536_ = leanh::lean_ctor_get(v_m_1533_, 0);
                v_buckets_1537_ = leanh::lean_ctor_get(v_m_1533_, 1);
                v___x_1538_ = lean_array_get_size(v_buckets_1537_);
                v___x_1539_ = l_Lean_instHashableFVarId_hash(v_a_1534_);
                v___x_1540_ = 32u64;
                v___x_1541_ = lean_uint64_shift_right(v___x_1539_, v___x_1540_);
                v_fold_1542_ = lean_uint64_xor(v___x_1539_, v___x_1541_);
                v___x_1543_ = 16u64;
                v___x_1544_ = lean_uint64_shift_right(v_fold_1542_, v___x_1543_);
                v___x_1545_ = lean_uint64_xor(v_fold_1542_, v___x_1544_);
                v___x_1546_ = lean_uint64_to_usize(v___x_1545_);
                v___x_1547_ = lean_usize_of_nat(v___x_1538_);
                v___x_1548_ = 1usize;
                v___x_1549_ = lean_usize_sub(v___x_1547_, v___x_1548_);
                v___x_1550_ = lean_usize_land(v___x_1546_, v___x_1549_);
                v_bkt_1551_ = lean_array_uget_borrowed(v_buckets_1537_, v___x_1550_);
                v___x_1552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_1534_, v_bkt_1551_);
                if v___x_1552_ == 0 {
                    leanh::lean_inc_ref(v_buckets_1537_);
                    leanh::lean_inc(v_size_1536_);
                    v_isSharedCheck_1573_ = (!leanh::lean_is_exclusive(v_m_1533_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v_unused_1574_ = leanh::lean_ctor_get(v_m_1533_, 1);
                        leanh::lean_dec(v_unused_1574_);
                        v_unused_1575_ = leanh::lean_ctor_get(v_m_1533_, 0);
                        leanh::lean_dec(v_unused_1575_);
                        v___x_1554_ = v_m_1533_;
                        v_isShared_1555_ = v_isSharedCheck_1573_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_1533_);
                        v___x_1554_ = leanh::lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1573_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_1535_);
                    leanh::lean_dec(v_a_1534_);
                    return v_m_1533_;
                }
            }
            1 => {
                v___x_1556_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1557_ = lean_nat_add(v_size_1536_, v___x_1556_);
                leanh::lean_dec(v_size_1536_);
                leanh::lean_inc(v_bkt_1551_);
                v___x_1558_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1558_, 0, v_a_1534_);
                leanh::lean_ctor_set(v___x_1558_, 1, v_b_1535_);
                leanh::lean_ctor_set(v___x_1558_, 2, v_bkt_1551_);
                v_buckets_x27_1559_ = lean_array_uset(v_buckets_1537_, v___x_1550_, v___x_1558_);
                v___x_1560_ = leanh::lean_unsigned_to_nat(4);
                v___x_1561_ = lean_nat_mul(v_size_x27_1557_, v___x_1560_);
                v___x_1562_ = leanh::lean_unsigned_to_nat(3);
                v___x_1563_ = lean_nat_div(v___x_1561_, v___x_1562_);
                leanh::lean_dec(v___x_1561_);
                v___x_1564_ = lean_array_get_size(v_buckets_x27_1559_);
                v___x_1565_ = lean_nat_dec_le(v___x_1563_, v___x_1564_);
                leanh::lean_dec(v___x_1563_);
                if v___x_1565_ == 0 {
                    v_val_1566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_buckets_x27_1559_);
                    if v_isShared_1555_ == 0 {
                        leanh::lean_ctor_set(v___x_1554_, 1, v_val_1566_);
                        leanh::lean_ctor_set(v___x_1554_, 0, v_size_x27_1557_);
                        v___x_1568_ = v___x_1554_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1569_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_size_x27_1557_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_val_1566_);
                        v___x_1568_ = v_reuseFailAlloc_1569_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1555_ == 0 {
                        leanh::lean_ctor_set(v___x_1554_, 1, v_buckets_x27_1559_);
                        leanh::lean_ctor_set(v___x_1554_, 0, v_size_x27_1557_);
                        v___x_1571_ = v___x_1554_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1572_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_size_x27_1557_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_buckets_x27_1559_);
                        v___x_1571_ = v_reuseFailAlloc_1572_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1568_;
            }
            3 => {
                return v___x_1571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_markVisited___redArg(
    mut v_fvarId_1576_: *mut leanh::LeanObject,
    mut v_a_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1579_ = lean_st_ref_take(v_a_1577_);
                v_visited_1580_ = leanh::lean_ctor_get(v___x_1579_, 0);
                v_params_1581_ = leanh::lean_ctor_get(v___x_1579_, 1);
                v_decls_1582_ = leanh::lean_ctor_get(v___x_1579_, 2);
                v_isSharedCheck_1593_ = (!leanh::lean_is_exclusive(v___x_1579_)) as u8;
                if v_isSharedCheck_1593_ == 0 {
                    v___x_1584_ = v___x_1579_;
                    v_isShared_1585_ = v_isSharedCheck_1593_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_decls_1582_);
                    leanh::lean_inc(v_params_1581_);
                    leanh::lean_inc(v_visited_1580_);
                    leanh::lean_dec(v___x_1579_);
                    v___x_1584_ = leanh::lean_box(0);
                    v_isShared_1585_ = v_isSharedCheck_1593_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1586_ = leanh::lean_box(0);
                v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_visited_1580_, v_fvarId_1576_, v___x_1586_);
                if v_isShared_1585_ == 0 {
                    leanh::lean_ctor_set(v___x_1584_, 0, v___x_1587_);
                    v___x_1589_ = v___x_1584_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_params_1581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_decls_1582_);
                    v___x_1589_ = v_reuseFailAlloc_1592_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1590_ = lean_st_ref_set(v_a_1577_, v___x_1589_);
                v___x_1591_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1591_, 0, v___x_1586_);
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_markVisited___redArg___boxed(
    mut v_fvarId_1594_: *mut leanh::LeanObject,
    mut v_a_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1597_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_1594_, v_a_1595_);
    leanh::lean_dec(v_a_1595_);
    return v_res_1597_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_markVisited(
    mut v_fvarId_1598_: *mut leanh::LeanObject,
    mut v_a_1599_: *mut leanh::LeanObject,
    mut v_a_1600_: *mut leanh::LeanObject,
    mut v_a_1601_: *mut leanh::LeanObject,
    mut v_a_1602_: *mut leanh::LeanObject,
    mut v_a_1603_: *mut leanh::LeanObject,
    mut v_a_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_1598_, v_a_1600_);
    return v___x_1606_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_markVisited___boxed(
    mut v_fvarId_1607_: *mut leanh::LeanObject,
    mut v_a_1608_: *mut leanh::LeanObject,
    mut v_a_1609_: *mut leanh::LeanObject,
    mut v_a_1610_: *mut leanh::LeanObject,
    mut v_a_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
    mut v_a_1613_: *mut leanh::LeanObject,
    mut v_a_1614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1615_ = l_Lean_Compiler_LCNF_Closure_markVisited(
        v_fvarId_1607_,
        v_a_1608_,
        v_a_1609_,
        v_a_1610_,
        v_a_1611_,
        v_a_1612_,
        v_a_1613_,
    );
    leanh::lean_dec(v_a_1613_);
    leanh::lean_dec_ref(v_a_1612_);
    leanh::lean_dec(v_a_1611_);
    leanh::lean_dec_ref(v_a_1610_);
    leanh::lean_dec(v_a_1609_);
    leanh::lean_dec_ref(v_a_1608_);
    return v_res_1615_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0(
    mut v_00_u03b2_1616_: *mut leanh::LeanObject,
    mut v_m_1617_: *mut leanh::LeanObject,
    mut v_a_1618_: *mut leanh::LeanObject,
    mut v_b_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_m_1617_, v_a_1618_, v_b_1619_);
    return v___x_1620_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(
    mut v_00_u03b2_1621_: *mut leanh::LeanObject,
    mut v_a_1622_: *mut leanh::LeanObject,
    mut v_x_1623_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1624_: u8 = 0;
    v___x_1624_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_1622_, v_x_1623_);
    return v___x_1624_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___boxed(
    mut v_00_u03b2_1625_: *mut leanh::LeanObject,
    mut v_a_1626_: *mut leanh::LeanObject,
    mut v_x_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1628_: u8 = 0;
    let mut v_r_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(v_00_u03b2_1625_, v_a_1626_, v_x_1627_);
    leanh::lean_dec(v_x_1627_);
    leanh::lean_dec(v_a_1626_);
    v_r_1629_ = leanh::lean_box((v_res_1628_) as usize);
    return v_r_1629_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1(
    mut v_00_u03b2_1630_: *mut leanh::LeanObject,
    mut v_data_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_data_1631_);
    return v___x_1632_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1633_: *mut leanh::LeanObject,
    mut v_i_1634_: *mut leanh::LeanObject,
    mut v_source_1635_: *mut leanh::LeanObject,
    mut v_target_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(v_i_1634_, v_source_1635_, v_target_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1638_: *mut leanh::LeanObject,
    mut v_x_1639_: *mut leanh::LeanObject,
    mut v_x_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1639_, v_x_1640_);
    return v___x_1641_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1642_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(
    mut v_msg_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
    mut v___y_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1660_: u8 = 0;
    let mut v_toFunctor_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___f_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v_toFunctor_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___f_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_22543__overap_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut v_unused_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v_unused_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_unused_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v_unused_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1655_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0);
                v___x_1656_ = l_StateRefT_x27_instMonad___redArg(v___x_1655_);
                v_toApplicative_1657_ = leanh::lean_ctor_get(v___x_1656_, 0);
                v_isSharedCheck_1720_ = (!leanh::lean_is_exclusive(v___x_1656_)) as u8;
                if v_isSharedCheck_1720_ == 0 {
                    v_unused_1721_ = leanh::lean_ctor_get(v___x_1656_, 1);
                    leanh::lean_dec(v_unused_1721_);
                    v___x_1659_ = v___x_1656_;
                    v_isShared_1660_ = v_isSharedCheck_1720_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1657_);
                    leanh::lean_dec(v___x_1656_);
                    v___x_1659_ = leanh::lean_box(0);
                    v_isShared_1660_ = v_isSharedCheck_1720_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1661_ = leanh::lean_ctor_get(v_toApplicative_1657_, 0);
                v_toSeq_1662_ = leanh::lean_ctor_get(v_toApplicative_1657_, 2);
                v_toSeqLeft_1663_ = leanh::lean_ctor_get(v_toApplicative_1657_, 3);
                v_toSeqRight_1664_ = leanh::lean_ctor_get(v_toApplicative_1657_, 4);
                v_isSharedCheck_1718_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1657_)) as u8;
                if v_isSharedCheck_1718_ == 0 {
                    v_unused_1719_ = leanh::lean_ctor_get(v_toApplicative_1657_, 1);
                    leanh::lean_dec(v_unused_1719_);
                    v___x_1666_ = v_toApplicative_1657_;
                    v_isShared_1667_ = v_isSharedCheck_1718_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1664_);
                    leanh::lean_inc(v_toSeqLeft_1663_);
                    leanh::lean_inc(v_toSeq_1662_);
                    leanh::lean_inc(v_toFunctor_1661_);
                    leanh::lean_dec(v_toApplicative_1657_);
                    v___x_1666_ = leanh::lean_box(0);
                    v_isShared_1667_ = v_isSharedCheck_1718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1668_ =
                    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1;
                v___f_1669_ =
                    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2;
                leanh::lean_inc_ref(v_toFunctor_1661_);
                v___f_1670_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1670_, 0, v_toFunctor_1661_);
                v___f_1671_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1671_, 0, v_toFunctor_1661_);
                v___x_1672_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1672_, 0, v___f_1670_);
                leanh::lean_ctor_set(v___x_1672_, 1, v___f_1671_);
                v___f_1673_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1673_, 0, v_toSeqRight_1664_);
                v___f_1674_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1674_, 0, v_toSeqLeft_1663_);
                v___f_1675_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1675_, 0, v_toSeq_1662_);
                if v_isShared_1667_ == 0 {
                    leanh::lean_ctor_set(v___x_1666_, 4, v___f_1673_);
                    leanh::lean_ctor_set(v___x_1666_, 3, v___f_1674_);
                    leanh::lean_ctor_set(v___x_1666_, 2, v___f_1675_);
                    leanh::lean_ctor_set(v___x_1666_, 1, v___f_1668_);
                    leanh::lean_ctor_set(v___x_1666_, 0, v___x_1672_);
                    v___x_1677_ = v___x_1666_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___f_1668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 2, v___f_1675_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 3, v___f_1674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 4, v___f_1673_);
                    v___x_1677_ = v_reuseFailAlloc_1717_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1660_ == 0 {
                    leanh::lean_ctor_set(v___x_1659_, 1, v___f_1669_);
                    leanh::lean_ctor_set(v___x_1659_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1659_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___f_1669_);
                    v___x_1679_ = v_reuseFailAlloc_1716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1680_ = l_StateRefT_x27_instMonad___redArg(v___x_1679_);
                v_toApplicative_1681_ = leanh::lean_ctor_get(v___x_1680_, 0);
                v_isSharedCheck_1714_ = (!leanh::lean_is_exclusive(v___x_1680_)) as u8;
                if v_isSharedCheck_1714_ == 0 {
                    v_unused_1715_ = leanh::lean_ctor_get(v___x_1680_, 1);
                    leanh::lean_dec(v_unused_1715_);
                    v___x_1683_ = v___x_1680_;
                    v_isShared_1684_ = v_isSharedCheck_1714_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1681_);
                    leanh::lean_dec(v___x_1680_);
                    v___x_1683_ = leanh::lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1714_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1685_ = leanh::lean_ctor_get(v_toApplicative_1681_, 0);
                v_toSeq_1686_ = leanh::lean_ctor_get(v_toApplicative_1681_, 2);
                v_toSeqLeft_1687_ = leanh::lean_ctor_get(v_toApplicative_1681_, 3);
                v_toSeqRight_1688_ = leanh::lean_ctor_get(v_toApplicative_1681_, 4);
                v_isSharedCheck_1712_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1681_)) as u8;
                if v_isSharedCheck_1712_ == 0 {
                    v_unused_1713_ = leanh::lean_ctor_get(v_toApplicative_1681_, 1);
                    leanh::lean_dec(v_unused_1713_);
                    v___x_1690_ = v_toApplicative_1681_;
                    v_isShared_1691_ = v_isSharedCheck_1712_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1688_);
                    leanh::lean_inc(v_toSeqLeft_1687_);
                    leanh::lean_inc(v_toSeq_1686_);
                    leanh::lean_inc(v_toFunctor_1685_);
                    leanh::lean_dec(v_toApplicative_1681_);
                    v___x_1690_ = leanh::lean_box(0);
                    v_isShared_1691_ = v_isSharedCheck_1712_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1692_ =
                    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3;
                v___f_1693_ =
                    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4;
                leanh::lean_inc_ref(v_toFunctor_1685_);
                v___f_1694_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1694_, 0, v_toFunctor_1685_);
                v___f_1695_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1695_, 0, v_toFunctor_1685_);
                v___x_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1696_, 0, v___f_1694_);
                leanh::lean_ctor_set(v___x_1696_, 1, v___f_1695_);
                v___f_1697_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1697_, 0, v_toSeqRight_1688_);
                v___f_1698_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1698_, 0, v_toSeqLeft_1687_);
                v___f_1699_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1699_, 0, v_toSeq_1686_);
                if v_isShared_1691_ == 0 {
                    leanh::lean_ctor_set(v___x_1690_, 4, v___f_1697_);
                    leanh::lean_ctor_set(v___x_1690_, 3, v___f_1698_);
                    leanh::lean_ctor_set(v___x_1690_, 2, v___f_1699_);
                    leanh::lean_ctor_set(v___x_1690_, 1, v___f_1692_);
                    leanh::lean_ctor_set(v___x_1690_, 0, v___x_1696_);
                    v___x_1701_ = v___x_1690_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1711_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___f_1692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 2, v___f_1699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 3, v___f_1698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 4, v___f_1697_);
                    v___x_1701_ = v_reuseFailAlloc_1711_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1684_ == 0 {
                    leanh::lean_ctor_set(v___x_1683_, 1, v___f_1693_);
                    leanh::lean_ctor_set(v___x_1683_, 0, v___x_1701_);
                    v___x_1703_ = v___x_1683_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___f_1693_);
                    v___x_1703_ = v_reuseFailAlloc_1710_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1704_ = l_StateRefT_x27_instMonad___redArg(v___x_1703_);
                v___x_1705_ = leanh::lean_box(0);
                v___x_1706_ = l_instInhabitedOfMonad___redArg(v___x_1704_, v___x_1705_);
                v___f_1707_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1707_, 0, v___x_1706_);
                v___x_22543__overap_1708_ = lean_panic_fn_borrowed(v___f_1707_, v_msg_1647_);
                leanh::lean_dec_ref(v___f_1707_);
                leanh::lean_inc(v___y_1653_);
                leanh::lean_inc_ref(v___y_1652_);
                leanh::lean_inc(v___y_1651_);
                leanh::lean_inc_ref(v___y_1650_);
                leanh::lean_inc(v___y_1649_);
                leanh::lean_inc_ref(v___y_1648_);
                v___x_1709_ = leanh::lean_apply_7(
                    v___x_22543__overap_1708_,
                    v___y_1648_,
                    v___y_1649_,
                    v___y_1650_,
                    v___y_1651_,
                    v___y_1652_,
                    v___y_1653_,
                    leanh::lean_box(0),
                );
                return v___x_1709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___boxed(
    mut v_msg_1722_: *mut leanh::LeanObject,
    mut v___y_1723_: *mut leanh::LeanObject,
    mut v___y_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1730_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(
        v_msg_1722_,
        v___y_1723_,
        v___y_1724_,
        v___y_1725_,
        v___y_1726_,
        v___y_1727_,
        v___y_1728_,
    );
    leanh::lean_dec(v___y_1728_);
    leanh::lean_dec_ref(v___y_1727_);
    leanh::lean_dec(v___y_1726_);
    leanh::lean_dec_ref(v___y_1725_);
    leanh::lean_dec(v___y_1724_);
    leanh::lean_dec_ref(v___y_1723_);
    return v_res_1730_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(
    mut v_a_1731_: *mut leanh::LeanObject,
    mut v_x_1732_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1733_: u8 = 0;
    let mut v_key_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1732_) == 0 {
                    v___x_1733_ = 0;
                    return v___x_1733_;
                } else {
                    v_key_1734_ = leanh::lean_ctor_get(v_x_1732_, 0);
                    v_tail_1735_ = leanh::lean_ctor_get(v_x_1732_, 2);
                    v___x_1736_ = lean_expr_eqv(v_key_1734_, v_a_1731_);
                    if v___x_1736_ == 0 {
                        v_x_1732_ = v_tail_1735_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1736_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg___boxed(
    mut v_a_1738_: *mut leanh::LeanObject,
    mut v_x_1739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1740_: u8 = 0;
    let mut v_r_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_1738_, v_x_1739_);
    leanh::lean_dec(v_x_1739_);
    leanh::lean_dec_ref(v_a_1738_);
    v_r_1741_ = leanh::lean_box((v_res_1740_) as usize);
    return v_r_1741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(
    mut v_m_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u64 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v___x_1748_: u64 = 0;
    let mut v_fold_1749_: u64 = 0;
    let mut v___x_1750_: u64 = 0;
    let mut v___x_1751_: u64 = 0;
    let mut v___x_1752_: u64 = 0;
    let mut v___x_1753_: usize = 0;
    let mut v___x_1754_: usize = 0;
    let mut v___x_1755_: usize = 0;
    let mut v___x_1756_: usize = 0;
    let mut v___x_1757_: usize = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    v_buckets_1744_ = leanh::lean_ctor_get(v_m_1742_, 1);
    v___x_1745_ = lean_array_get_size(v_buckets_1744_);
    v___x_1746_ = l_Lean_Expr_hash(v_a_1743_);
    v___x_1747_ = 32u64;
    v___x_1748_ = lean_uint64_shift_right(v___x_1746_, v___x_1747_);
    v_fold_1749_ = lean_uint64_xor(v___x_1746_, v___x_1748_);
    v___x_1750_ = 16u64;
    v___x_1751_ = lean_uint64_shift_right(v_fold_1749_, v___x_1750_);
    v___x_1752_ = lean_uint64_xor(v_fold_1749_, v___x_1751_);
    v___x_1753_ = lean_uint64_to_usize(v___x_1752_);
    v___x_1754_ = lean_usize_of_nat(v___x_1745_);
    v___x_1755_ = 1usize;
    v___x_1756_ = lean_usize_sub(v___x_1754_, v___x_1755_);
    v___x_1757_ = lean_usize_land(v___x_1753_, v___x_1756_);
    v___x_1758_ = lean_array_uget_borrowed(v_buckets_1744_, v___x_1757_);
    v___x_1759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_1743_, v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg___boxed(
    mut v_m_1760_: *mut leanh::LeanObject,
    mut v_a_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1762_: u8 = 0;
    let mut v_r_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_1760_, v_a_1761_);
    leanh::lean_dec_ref(v_a_1761_);
    leanh::lean_dec_ref(v_m_1760_);
    v_r_1763_ = leanh::lean_box((v_res_1762_) as usize);
    return v_r_1763_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(
    mut v_x_1764_: *mut leanh::LeanObject,
    mut v_x_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: u64 = 0;
    let mut v___x_1774_: u64 = 0;
    let mut v___x_1775_: u64 = 0;
    let mut v_fold_1776_: u64 = 0;
    let mut v___x_1777_: u64 = 0;
    let mut v___x_1778_: u64 = 0;
    let mut v___x_1779_: u64 = 0;
    let mut v___x_1780_: usize = 0;
    let mut v___x_1781_: usize = 0;
    let mut v___x_1782_: usize = 0;
    let mut v___x_1783_: usize = 0;
    let mut v___x_1784_: usize = 0;
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1765_) == 0 {
                    return v_x_1764_;
                } else {
                    v_key_1766_ = leanh::lean_ctor_get(v_x_1765_, 0);
                    v_value_1767_ = leanh::lean_ctor_get(v_x_1765_, 1);
                    v_tail_1768_ = leanh::lean_ctor_get(v_x_1765_, 2);
                    v_isSharedCheck_1791_ = (!leanh::lean_is_exclusive(v_x_1765_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1770_ = v_x_1765_;
                        v_isShared_1771_ = v_isSharedCheck_1791_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1768_);
                        leanh::lean_inc(v_value_1767_);
                        leanh::lean_inc(v_key_1766_);
                        leanh::lean_dec(v_x_1765_);
                        v___x_1770_ = leanh::lean_box(0);
                        v_isShared_1771_ = v_isSharedCheck_1791_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1772_ = lean_array_get_size(v_x_1764_);
                v___x_1773_ = l_Lean_Expr_hash(v_key_1766_);
                v___x_1774_ = 32u64;
                v___x_1775_ = lean_uint64_shift_right(v___x_1773_, v___x_1774_);
                v_fold_1776_ = lean_uint64_xor(v___x_1773_, v___x_1775_);
                v___x_1777_ = 16u64;
                v___x_1778_ = lean_uint64_shift_right(v_fold_1776_, v___x_1777_);
                v___x_1779_ = lean_uint64_xor(v_fold_1776_, v___x_1778_);
                v___x_1780_ = lean_uint64_to_usize(v___x_1779_);
                v___x_1781_ = lean_usize_of_nat(v___x_1772_);
                v___x_1782_ = 1usize;
                v___x_1783_ = lean_usize_sub(v___x_1781_, v___x_1782_);
                v___x_1784_ = lean_usize_land(v___x_1780_, v___x_1783_);
                v___x_1785_ = lean_array_uget_borrowed(v_x_1764_, v___x_1784_);
                leanh::lean_inc(v___x_1785_);
                if v_isShared_1771_ == 0 {
                    leanh::lean_ctor_set(v___x_1770_, 2, v___x_1785_);
                    v___x_1787_ = v___x_1770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_key_1766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_value_1767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 2, v___x_1785_);
                    v___x_1787_ = v_reuseFailAlloc_1790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1788_ = lean_array_uset(v_x_1764_, v___x_1784_, v___x_1787_);
                v_x_1764_ = v___x_1788_;
                v_x_1765_ = v_tail_1768_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(
    mut v_i_1792_: *mut leanh::LeanObject,
    mut v_source_1793_: *mut leanh::LeanObject,
    mut v_target_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v_es_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1795_ = lean_array_get_size(v_source_1793_);
                v___x_1796_ = lean_nat_dec_lt(v_i_1792_, v___x_1795_);
                if v___x_1796_ == 0 {
                    leanh::lean_dec_ref(v_source_1793_);
                    leanh::lean_dec(v_i_1792_);
                    return v_target_1794_;
                } else {
                    v_es_1797_ = lean_array_fget(v_source_1793_, v_i_1792_);
                    v___x_1798_ = leanh::lean_box(0);
                    v_source_1799_ = lean_array_fset(v_source_1793_, v_i_1792_, v___x_1798_);
                    v_target_1800_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_target_1794_, v_es_1797_);
                    v___x_1801_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1802_ = lean_nat_add(v_i_1792_, v___x_1801_);
                    leanh::lean_dec(v_i_1792_);
                    v_i_1792_ = v___x_1802_;
                    v_source_1793_ = v_source_1799_;
                    v_target_1794_ = v_target_1800_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(
    mut v_data_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = lean_array_get_size(v_data_1804_);
    v___x_1806_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1807_ = lean_nat_mul(v___x_1805_, v___x_1806_);
    v___x_1808_ = leanh::lean_unsigned_to_nat(0);
    v___x_1809_ = leanh::lean_box(0);
    v___x_1810_ = lean_mk_array(v_nbuckets_1807_, v___x_1809_);
    v___x_1811_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v___x_1808_, v_data_1804_, v___x_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(
    mut v_m_1812_: *mut leanh::LeanObject,
    mut v_a_1813_: *mut leanh::LeanObject,
    mut v_b_1814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u64 = 0;
    let mut v___x_1819_: u64 = 0;
    let mut v___x_1820_: u64 = 0;
    let mut v_fold_1821_: u64 = 0;
    let mut v___x_1822_: u64 = 0;
    let mut v___x_1823_: u64 = 0;
    let mut v___x_1824_: u64 = 0;
    let mut v___x_1825_: usize = 0;
    let mut v___x_1826_: usize = 0;
    let mut v___x_1827_: usize = 0;
    let mut v___x_1828_: usize = 0;
    let mut v___x_1829_: usize = 0;
    let mut v_bkt_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v_val_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1852_: u8 = 0;
    let mut v_unused_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1815_ = leanh::lean_ctor_get(v_m_1812_, 0);
                v_buckets_1816_ = leanh::lean_ctor_get(v_m_1812_, 1);
                v___x_1817_ = lean_array_get_size(v_buckets_1816_);
                v___x_1818_ = l_Lean_Expr_hash(v_a_1813_);
                v___x_1819_ = 32u64;
                v___x_1820_ = lean_uint64_shift_right(v___x_1818_, v___x_1819_);
                v_fold_1821_ = lean_uint64_xor(v___x_1818_, v___x_1820_);
                v___x_1822_ = 16u64;
                v___x_1823_ = lean_uint64_shift_right(v_fold_1821_, v___x_1822_);
                v___x_1824_ = lean_uint64_xor(v_fold_1821_, v___x_1823_);
                v___x_1825_ = lean_uint64_to_usize(v___x_1824_);
                v___x_1826_ = lean_usize_of_nat(v___x_1817_);
                v___x_1827_ = 1usize;
                v___x_1828_ = lean_usize_sub(v___x_1826_, v___x_1827_);
                v___x_1829_ = lean_usize_land(v___x_1825_, v___x_1828_);
                v_bkt_1830_ = lean_array_uget_borrowed(v_buckets_1816_, v___x_1829_);
                v___x_1831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_1813_, v_bkt_1830_);
                if v___x_1831_ == 0 {
                    leanh::lean_inc_ref(v_buckets_1816_);
                    leanh::lean_inc(v_size_1815_);
                    v_isSharedCheck_1852_ = (!leanh::lean_is_exclusive(v_m_1812_)) as u8;
                    if v_isSharedCheck_1852_ == 0 {
                        v_unused_1853_ = leanh::lean_ctor_get(v_m_1812_, 1);
                        leanh::lean_dec(v_unused_1853_);
                        v_unused_1854_ = leanh::lean_ctor_get(v_m_1812_, 0);
                        leanh::lean_dec(v_unused_1854_);
                        v___x_1833_ = v_m_1812_;
                        v_isShared_1834_ = v_isSharedCheck_1852_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_1812_);
                        v___x_1833_ = leanh::lean_box(0);
                        v_isShared_1834_ = v_isSharedCheck_1852_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_1814_);
                    leanh::lean_dec_ref(v_a_1813_);
                    return v_m_1812_;
                }
            }
            1 => {
                v___x_1835_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1836_ = lean_nat_add(v_size_1815_, v___x_1835_);
                leanh::lean_dec(v_size_1815_);
                leanh::lean_inc(v_bkt_1830_);
                v___x_1837_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1837_, 0, v_a_1813_);
                leanh::lean_ctor_set(v___x_1837_, 1, v_b_1814_);
                leanh::lean_ctor_set(v___x_1837_, 2, v_bkt_1830_);
                v_buckets_x27_1838_ = lean_array_uset(v_buckets_1816_, v___x_1829_, v___x_1837_);
                v___x_1839_ = leanh::lean_unsigned_to_nat(4);
                v___x_1840_ = lean_nat_mul(v_size_x27_1836_, v___x_1839_);
                v___x_1841_ = leanh::lean_unsigned_to_nat(3);
                v___x_1842_ = lean_nat_div(v___x_1840_, v___x_1841_);
                leanh::lean_dec(v___x_1840_);
                v___x_1843_ = lean_array_get_size(v_buckets_x27_1838_);
                v___x_1844_ = lean_nat_dec_le(v___x_1842_, v___x_1843_);
                leanh::lean_dec(v___x_1842_);
                if v___x_1844_ == 0 {
                    v_val_1845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_buckets_x27_1838_);
                    if v_isShared_1834_ == 0 {
                        leanh::lean_ctor_set(v___x_1833_, 1, v_val_1845_);
                        leanh::lean_ctor_set(v___x_1833_, 0, v_size_x27_1836_);
                        v___x_1847_ = v___x_1833_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1848_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_size_x27_1836_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_val_1845_);
                        v___x_1847_ = v_reuseFailAlloc_1848_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1834_ == 0 {
                        leanh::lean_ctor_set(v___x_1833_, 1, v_buckets_x27_1838_);
                        leanh::lean_ctor_set(v___x_1833_, 0, v_size_x27_1836_);
                        v___x_1850_ = v___x_1833_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1851_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_size_x27_1836_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_buckets_x27_1838_);
                        v___x_1850_ = v_reuseFailAlloc_1851_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1847_;
            }
            3 => {
                return v___x_1850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(
    mut v_e_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1858_ = lean_st_ref_get(v_a_1856_);
                v_checked_1859_ = leanh::lean_ctor_get(v___x_1858_, 1);
                leanh::lean_inc_ref(v_checked_1859_);
                leanh::lean_dec(v___x_1858_);
                v___x_1860_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_checked_1859_, v_e_1855_);
                leanh::lean_dec_ref(v_checked_1859_);
                if v___x_1860_ == 0 {
                    v___x_1861_ = lean_st_ref_take(v_a_1856_);
                    v_visited_1862_ = leanh::lean_ctor_get(v___x_1861_, 0);
                    v_checked_1863_ = leanh::lean_ctor_get(v___x_1861_, 1);
                    v_isSharedCheck_1875_ = (!leanh::lean_is_exclusive(v___x_1861_)) as u8;
                    if v_isSharedCheck_1875_ == 0 {
                        v___x_1865_ = v___x_1861_;
                        v_isShared_1866_ = v_isSharedCheck_1875_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_checked_1863_);
                        leanh::lean_inc(v_visited_1862_);
                        leanh::lean_dec(v___x_1861_);
                        v___x_1865_ = leanh::lean_box(0);
                        v_isShared_1866_ = v_isSharedCheck_1875_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1855_);
                    v___x_1876_ = leanh::lean_box((v___x_1860_) as usize);
                    v___x_1877_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1877_, 0, v___x_1876_);
                    return v___x_1877_;
                }
            }
            1 => {
                v___x_1867_ = leanh::lean_box(0);
                v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_checked_1863_, v_e_1855_, v___x_1867_);
                if v_isShared_1866_ == 0 {
                    leanh::lean_ctor_set(v___x_1865_, 1, v___x_1868_);
                    v___x_1870_ = v___x_1865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_visited_1862_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1868_);
                    v___x_1870_ = v_reuseFailAlloc_1874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1871_ = lean_st_ref_set(v_a_1856_, v___x_1870_);
                v___x_1872_ = leanh::lean_box((v___x_1860_) as usize);
                v___x_1873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                return v___x_1873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg___boxed(
    mut v_e_1878_: *mut leanh::LeanObject,
    mut v_a_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1881_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_1878_, v_a_1879_);
    leanh::lean_dec(v_a_1879_);
    return v_res_1881_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0()
-> usize {
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: usize = 0;
    let mut v___x_1884_: usize = 0;
    v___x_1882_ = 1usize;
    v___x_1883_ = 8192usize;
    v___x_1884_ = lean_usize_sub(v___x_1883_, v___x_1882_);
    return v___x_1884_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(
    mut v_e_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: usize = 0;
    let mut v___x_1891_: usize = 0;
    let mut v___x_1892_: usize = 0;
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: usize = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1888_ = lean_st_ref_get(v_a_1886_);
                v_visited_1889_ = leanh::lean_ctor_get(v___x_1888_, 0);
                leanh::lean_inc_ref(v_visited_1889_);
                leanh::lean_dec(v___x_1888_);
                v___x_1890_ = lean_ptr_addr(v_e_1885_);
                v___x_1891_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0_once), _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0);
                v___x_1892_ = lean_usize_mod(v___x_1890_, v___x_1891_);
                v___x_1893_ = lean_array_uget(v_visited_1889_, v___x_1892_);
                leanh::lean_dec_ref(v_visited_1889_);
                v___x_1894_ = lean_ptr_addr(v___x_1893_);
                leanh::lean_dec(v___x_1893_);
                v___x_1895_ = lean_usize_dec_eq(v___x_1894_, v___x_1890_);
                if v___x_1895_ == 0 {
                    v___x_1896_ = lean_st_ref_take(v_a_1886_);
                    v_visited_1897_ = leanh::lean_ctor_get(v___x_1896_, 0);
                    v_checked_1898_ = leanh::lean_ctor_get(v___x_1896_, 1);
                    v_isSharedCheck_1909_ = (!leanh::lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1909_ == 0 {
                        v___x_1900_ = v___x_1896_;
                        v_isShared_1901_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_checked_1898_);
                        leanh::lean_inc(v_visited_1897_);
                        leanh::lean_dec(v___x_1896_);
                        v___x_1900_ = leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1885_);
                    v___x_1910_ = leanh::lean_box((v___x_1895_) as usize);
                    v___x_1911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1911_, 0, v___x_1910_);
                    return v___x_1911_;
                }
            }
            1 => {
                v___x_1902_ = lean_array_uset(v_visited_1897_, v___x_1892_, v_e_1885_);
                if v_isShared_1901_ == 0 {
                    leanh::lean_ctor_set(v___x_1900_, 0, v___x_1902_);
                    v___x_1904_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_checked_1898_);
                    v___x_1904_ = v_reuseFailAlloc_1908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1905_ = lean_st_ref_set(v_a_1886_, v___x_1904_);
                v___x_1906_ = leanh::lean_box((v___x_1895_) as usize);
                v___x_1907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1907_, 0, v___x_1906_);
                return v___x_1907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___boxed(
    mut v_e_1912_: *mut leanh::LeanObject,
    mut v_a_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1915_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_1912_, v_a_1913_);
    leanh::lean_dec(v_a_1913_);
    return v_res_1915_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(
    mut v_p_1916_: *mut leanh::LeanObject,
    mut v_f_1917_: *mut leanh::LeanObject,
    mut v_stopWhenVisited_1918_: u8,
    mut v_e_1919_: *mut leanh::LeanObject,
    mut v_a_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: u8 = 0;
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_unused_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1919_);
                v___x_1968_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_1919_, v_a_1920_);
                if leanh::lean_obj_tag(v___x_1968_) == 0 {
                    v_a_1969_ = leanh::lean_ctor_get(v___x_1968_, 0);
                    v_isSharedCheck_2001_ = (!leanh::lean_is_exclusive(v___x_1968_)) as u8;
                    if v_isSharedCheck_2001_ == 0 {
                        v___x_1971_ = v___x_1968_;
                        v_isShared_1972_ = v_isSharedCheck_2001_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1969_);
                        leanh::lean_dec(v___x_1968_);
                        v___x_1971_ = leanh::lean_box(0);
                        v_isShared_1972_ = v_isSharedCheck_2001_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1919_);
                    leanh::lean_dec_ref(v_f_1917_);
                    leanh::lean_dec_ref(v_p_1916_);
                    v_a_2002_ = leanh::lean_ctor_get(v___x_1968_, 0);
                    v_isSharedCheck_2009_ = (!leanh::lean_is_exclusive(v___x_1968_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2004_ = v___x_1968_;
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2002_);
                        leanh::lean_dec(v___x_1968_);
                        v___x_2004_ = leanh::lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_f_1917_);
                leanh::lean_inc_ref(v_p_1916_);
                v___x_1938_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_d_1935_, v___y_1937_, v___y_1930_, v___y_1931_, v___y_1933_, v___y_1932_, v___y_1934_, v___y_1929_);
                if leanh::lean_obj_tag(v___x_1938_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1938_, 1);
                    v_e_1919_ = v_b_1936_;
                    v_a_1920_ = v___y_1937_;
                    v___y_1921_ = v___y_1930_;
                    v___y_1922_ = v___y_1931_;
                    v___y_1923_ = v___y_1933_;
                    v___y_1924_ = v___y_1932_;
                    v___y_1925_ = v___y_1934_;
                    v___y_1926_ = v___y_1929_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_1936_);
                    leanh::lean_dec_ref(v_f_1917_);
                    leanh::lean_dec_ref(v_p_1916_);
                    return v___x_1938_;
                }
            }
            2 => match leanh::lean_obj_tag(v_e_1919_) {
                7 => {
                    v_binderType_1948_ = leanh::lean_ctor_get(v_e_1919_, 1);
                    leanh::lean_inc_ref(v_binderType_1948_);
                    v_body_1949_ = leanh::lean_ctor_get(v_e_1919_, 2);
                    leanh::lean_inc_ref(v_body_1949_);
                    leanh::lean_dec_ref_known(v_e_1919_, 3);
                    v___y_1929_ = v___y_1947_;
                    v___y_1930_ = v___y_1942_;
                    v___y_1931_ = v___y_1943_;
                    v___y_1932_ = v___y_1945_;
                    v___y_1933_ = v___y_1944_;
                    v___y_1934_ = v___y_1946_;
                    v_d_1935_ = v_binderType_1948_;
                    v_b_1936_ = v_body_1949_;
                    v___y_1937_ = v___y_1941_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_1950_ = leanh::lean_ctor_get(v_e_1919_, 1);
                    leanh::lean_inc_ref(v_binderType_1950_);
                    v_body_1951_ = leanh::lean_ctor_get(v_e_1919_, 2);
                    leanh::lean_inc_ref(v_body_1951_);
                    leanh::lean_dec_ref_known(v_e_1919_, 3);
                    v___y_1929_ = v___y_1947_;
                    v___y_1930_ = v___y_1942_;
                    v___y_1931_ = v___y_1943_;
                    v___y_1932_ = v___y_1945_;
                    v___y_1933_ = v___y_1944_;
                    v___y_1934_ = v___y_1946_;
                    v_d_1935_ = v_binderType_1950_;
                    v_b_1936_ = v_body_1951_;
                    v___y_1937_ = v___y_1941_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_1952_ = leanh::lean_ctor_get(v_e_1919_, 1);
                    leanh::lean_inc_ref(v_type_1952_);
                    v_value_1953_ = leanh::lean_ctor_get(v_e_1919_, 2);
                    leanh::lean_inc_ref(v_value_1953_);
                    v_body_1954_ = leanh::lean_ctor_get(v_e_1919_, 3);
                    leanh::lean_inc_ref(v_body_1954_);
                    leanh::lean_dec_ref_known(v_e_1919_, 4);
                    leanh::lean_inc_ref(v_f_1917_);
                    leanh::lean_inc_ref(v_p_1916_);
                    v___x_1955_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_type_1952_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
                    if leanh::lean_obj_tag(v___x_1955_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1955_, 1);
                        leanh::lean_inc_ref(v_f_1917_);
                        leanh::lean_inc_ref(v_p_1916_);
                        v___x_1956_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_value_1953_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
                        if leanh::lean_obj_tag(v___x_1956_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1956_, 1);
                            v_e_1919_ = v_body_1954_;
                            v_a_1920_ = v___y_1941_;
                            v___y_1921_ = v___y_1942_;
                            v___y_1922_ = v___y_1943_;
                            v___y_1923_ = v___y_1944_;
                            v___y_1924_ = v___y_1945_;
                            v___y_1925_ = v___y_1946_;
                            v___y_1926_ = v___y_1947_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_body_1954_);
                            leanh::lean_dec_ref(v_f_1917_);
                            leanh::lean_dec_ref(v_p_1916_);
                            return v___x_1956_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_1954_);
                        leanh::lean_dec_ref(v_value_1953_);
                        leanh::lean_dec_ref(v_f_1917_);
                        leanh::lean_dec_ref(v_p_1916_);
                        return v___x_1955_;
                    }
                }
                5 => {
                    v_fn_1958_ = leanh::lean_ctor_get(v_e_1919_, 0);
                    leanh::lean_inc_ref(v_fn_1958_);
                    v_arg_1959_ = leanh::lean_ctor_get(v_e_1919_, 1);
                    leanh::lean_inc_ref(v_arg_1959_);
                    leanh::lean_dec_ref_known(v_e_1919_, 2);
                    leanh::lean_inc_ref(v_f_1917_);
                    leanh::lean_inc_ref(v_p_1916_);
                    v___x_1960_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_fn_1958_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
                    if leanh::lean_obj_tag(v___x_1960_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1960_, 1);
                        v_e_1919_ = v_arg_1959_;
                        v_a_1920_ = v___y_1941_;
                        v___y_1921_ = v___y_1942_;
                        v___y_1922_ = v___y_1943_;
                        v___y_1923_ = v___y_1944_;
                        v___y_1924_ = v___y_1945_;
                        v___y_1925_ = v___y_1946_;
                        v___y_1926_ = v___y_1947_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_arg_1959_);
                        leanh::lean_dec_ref(v_f_1917_);
                        leanh::lean_dec_ref(v_p_1916_);
                        return v___x_1960_;
                    }
                }
                10 => {
                    v_expr_1962_ = leanh::lean_ctor_get(v_e_1919_, 1);
                    leanh::lean_inc_ref(v_expr_1962_);
                    leanh::lean_dec_ref_known(v_e_1919_, 2);
                    v_e_1919_ = v_expr_1962_;
                    v_a_1920_ = v___y_1941_;
                    v___y_1921_ = v___y_1942_;
                    v___y_1922_ = v___y_1943_;
                    v___y_1923_ = v___y_1944_;
                    v___y_1924_ = v___y_1945_;
                    v___y_1925_ = v___y_1946_;
                    v___y_1926_ = v___y_1947_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_1964_ = leanh::lean_ctor_get(v_e_1919_, 2);
                    leanh::lean_inc_ref(v_struct_1964_);
                    leanh::lean_dec_ref_known(v_e_1919_, 3);
                    v_e_1919_ = v_struct_1964_;
                    v_a_1920_ = v___y_1941_;
                    v___y_1921_ = v___y_1942_;
                    v___y_1922_ = v___y_1943_;
                    v___y_1923_ = v___y_1944_;
                    v___y_1924_ = v___y_1945_;
                    v___y_1925_ = v___y_1946_;
                    v___y_1926_ = v___y_1947_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_e_1919_);
                    leanh::lean_dec_ref(v_f_1917_);
                    leanh::lean_dec_ref(v_p_1916_);
                    v___x_1966_ = leanh::lean_box(0);
                    v___x_1967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1967_, 0, v___x_1966_);
                    return v___x_1967_;
                }
            },
            3 => {
                v___x_1973_ = (leanh::lean_unbox(v_a_1969_) as u8);
                leanh::lean_dec(v_a_1969_);
                if v___x_1973_ == 0 {
                    leanh::lean_del_object(v___x_1971_);
                    leanh::lean_inc_ref(v_p_1916_);
                    leanh::lean_inc_ref(v_e_1919_);
                    v___x_1974_ = leanh::lean_apply_1(v_p_1916_, v_e_1919_);
                    v___x_1975_ = (leanh::lean_unbox(v___x_1974_) as u8);
                    if v___x_1975_ == 0 {
                        v___y_1941_ = v_a_1920_;
                        v___y_1942_ = v___y_1921_;
                        v___y_1943_ = v___y_1922_;
                        v___y_1944_ = v___y_1923_;
                        v___y_1945_ = v___y_1924_;
                        v___y_1946_ = v___y_1925_;
                        v___y_1947_ = v___y_1926_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_e_1919_);
                        v___x_1976_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_1919_, v_a_1920_);
                        if leanh::lean_obj_tag(v___x_1976_) == 0 {
                            v_a_1977_ = leanh::lean_ctor_get(v___x_1976_, 0);
                            leanh::lean_inc(v_a_1977_);
                            leanh::lean_dec_ref_known(v___x_1976_, 1);
                            v___x_1978_ = (leanh::lean_unbox(v_a_1977_) as u8);
                            leanh::lean_dec(v_a_1977_);
                            if v___x_1978_ == 0 {
                                leanh::lean_inc_ref(v_f_1917_);
                                leanh::lean_inc(v___y_1926_);
                                leanh::lean_inc_ref(v___y_1925_);
                                leanh::lean_inc(v___y_1924_);
                                leanh::lean_inc_ref(v___y_1923_);
                                leanh::lean_inc(v___y_1922_);
                                leanh::lean_inc_ref(v___y_1921_);
                                leanh::lean_inc_ref(v_e_1919_);
                                v___x_1979_ = leanh::lean_apply_8(
                                    v_f_1917_,
                                    v_e_1919_,
                                    v___y_1921_,
                                    v___y_1922_,
                                    v___y_1923_,
                                    v___y_1924_,
                                    v___y_1925_,
                                    v___y_1926_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_1979_) == 0 {
                                    v_isSharedCheck_1987_ =
                                        (!leanh::lean_is_exclusive(v___x_1979_)) as u8;
                                    if v_isSharedCheck_1987_ == 0 {
                                        v_unused_1988_ =
                                            leanh::lean_ctor_get(v___x_1979_, 0);
                                        leanh::lean_dec(v_unused_1988_);
                                        v___x_1981_ = v___x_1979_;
                                        v_isShared_1982_ = v_isSharedCheck_1987_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1979_);
                                        v___x_1981_ = leanh::lean_box(0);
                                        v_isShared_1982_ = v_isSharedCheck_1987_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_e_1919_);
                                    leanh::lean_dec_ref(v_f_1917_);
                                    leanh::lean_dec_ref(v_p_1916_);
                                    return v___x_1979_;
                                }
                            } else {
                                v___y_1941_ = v_a_1920_;
                                v___y_1942_ = v___y_1921_;
                                v___y_1943_ = v___y_1922_;
                                v___y_1944_ = v___y_1923_;
                                v___y_1945_ = v___y_1924_;
                                v___y_1946_ = v___y_1925_;
                                v___y_1947_ = v___y_1926_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_1919_);
                            leanh::lean_dec_ref(v_f_1917_);
                            leanh::lean_dec_ref(v_p_1916_);
                            v_a_1989_ = leanh::lean_ctor_get(v___x_1976_, 0);
                            v_isSharedCheck_1996_ =
                                (!leanh::lean_is_exclusive(v___x_1976_)) as u8;
                            if v_isSharedCheck_1996_ == 0 {
                                v___x_1991_ = v___x_1976_;
                                v_isShared_1992_ = v_isSharedCheck_1996_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1989_);
                                leanh::lean_dec(v___x_1976_);
                                v___x_1991_ = leanh::lean_box(0);
                                v_isShared_1992_ = v_isSharedCheck_1996_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1919_);
                    leanh::lean_dec_ref(v_f_1917_);
                    leanh::lean_dec_ref(v_p_1916_);
                    v___x_1997_ = leanh::lean_box(0);
                    if v_isShared_1972_ == 0 {
                        leanh::lean_ctor_set(v___x_1971_, 0, v___x_1997_);
                        v___x_1999_ = v___x_1971_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
                        v___x_1999_ = v_reuseFailAlloc_2000_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_stopWhenVisited_1918_ == 0 {
                    leanh::lean_del_object(v___x_1981_);
                    v___y_1941_ = v_a_1920_;
                    v___y_1942_ = v___y_1921_;
                    v___y_1943_ = v___y_1922_;
                    v___y_1944_ = v___y_1923_;
                    v___y_1945_ = v___y_1924_;
                    v___y_1946_ = v___y_1925_;
                    v___y_1947_ = v___y_1926_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_1919_);
                    leanh::lean_dec_ref(v_f_1917_);
                    leanh::lean_dec_ref(v_p_1916_);
                    v___x_1983_ = leanh::lean_box(0);
                    if v_isShared_1982_ == 0 {
                        leanh::lean_ctor_set(v___x_1981_, 0, v___x_1983_);
                        v___x_1985_ = v___x_1981_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1986_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
                        v___x_1985_ = v_reuseFailAlloc_1986_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1985_;
            }
            6 => {
                if v_isShared_1992_ == 0 {
                    v___x_1994_ = v___x_1991_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
                    v___x_1994_ = v_reuseFailAlloc_1995_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1994_;
            }
            8 => {
                return v___x_1999_;
            }
            9 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4___boxed(
    mut v_p_2010_: *mut leanh::LeanObject,
    mut v_f_2011_: *mut leanh::LeanObject,
    mut v_stopWhenVisited_2012_: *mut leanh::LeanObject,
    mut v_e_2013_: *mut leanh::LeanObject,
    mut v_a_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_2022_: u8 = 0;
    let mut v_res_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_2022_ = (leanh::lean_unbox(v_stopWhenVisited_2012_) as u8);
    v_res_2023_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_2010_, v_f_2011_, v_stopWhenVisited_boxed_2022_, v_e_2013_, v_a_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
    leanh::lean_dec(v___y_2020_);
    leanh::lean_dec_ref(v___y_2019_);
    leanh::lean_dec(v___y_2018_);
    leanh::lean_dec_ref(v___y_2017_);
    leanh::lean_dec(v___y_2016_);
    leanh::lean_dec_ref(v___y_2015_);
    leanh::lean_dec(v_a_2014_);
    return v_res_2023_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(
    mut v_p_2024_: *mut leanh::LeanObject,
    mut v_f_2025_: *mut leanh::LeanObject,
    mut v_e_2026_: *mut leanh::LeanObject,
    mut v_stopWhenVisited_2027_: u8,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
    mut v___y_2030_: *mut leanh::LeanObject,
    mut v___y_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2035_ = l_Lean_ForEachExprWhere_initCache;
                v___x_2036_ = lean_st_mk_ref(v___x_2035_);
                v___x_2037_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_2024_, v_f_2025_, v_stopWhenVisited_2027_, v_e_2026_, v___x_2036_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
                if leanh::lean_obj_tag(v___x_2037_) == 0 {
                    v_a_2038_ = leanh::lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2046_ = (!leanh::lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2040_ = v___x_2037_;
                        v_isShared_2041_ = v_isSharedCheck_2046_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2038_);
                        leanh::lean_dec(v___x_2037_);
                        v___x_2040_ = leanh::lean_box(0);
                        v_isShared_2041_ = v_isSharedCheck_2046_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2036_);
                    return v___x_2037_;
                }
            }
            1 => {
                v___x_2042_ = lean_st_ref_get(v___x_2036_);
                leanh::lean_dec(v___x_2036_);
                leanh::lean_dec(v___x_2042_);
                if v_isShared_2041_ == 0 {
                    v___x_2044_ = v___x_2040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2038_);
                    v___x_2044_ = v_reuseFailAlloc_2045_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2___boxed(
    mut v_p_2047_: *mut leanh::LeanObject,
    mut v_f_2048_: *mut leanh::LeanObject,
    mut v_e_2049_: *mut leanh::LeanObject,
    mut v_stopWhenVisited_2050_: *mut leanh::LeanObject,
    mut v___y_2051_: *mut leanh::LeanObject,
    mut v___y_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_2058_: u8 = 0;
    let mut v_res_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_2058_ = (leanh::lean_unbox(v_stopWhenVisited_2050_) as u8);
    v_res_2059_ =
        l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(
            v_p_2047_,
            v_f_2048_,
            v_e_2049_,
            v_stopWhenVisited_boxed_2058_,
            v___y_2051_,
            v___y_2052_,
            v___y_2053_,
            v___y_2054_,
            v___y_2055_,
            v___y_2056_,
        );
    leanh::lean_dec(v___y_2056_);
    leanh::lean_dec_ref(v___y_2055_);
    leanh::lean_dec(v___y_2054_);
    leanh::lean_dec_ref(v___y_2053_);
    leanh::lean_dec(v___y_2052_);
    leanh::lean_dec_ref(v___y_2051_);
    return v_res_2059_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(
    mut v_m_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u64 = 0;
    let mut v___x_2065_: u64 = 0;
    let mut v___x_2066_: u64 = 0;
    let mut v_fold_2067_: u64 = 0;
    let mut v___x_2068_: u64 = 0;
    let mut v___x_2069_: u64 = 0;
    let mut v___x_2070_: u64 = 0;
    let mut v___x_2071_: usize = 0;
    let mut v___x_2072_: usize = 0;
    let mut v___x_2073_: usize = 0;
    let mut v___x_2074_: usize = 0;
    let mut v___x_2075_: usize = 0;
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: u8 = 0;
    v_buckets_2062_ = leanh::lean_ctor_get(v_m_2060_, 1);
    v___x_2063_ = lean_array_get_size(v_buckets_2062_);
    v___x_2064_ = l_Lean_instHashableFVarId_hash(v_a_2061_);
    v___x_2065_ = 32u64;
    v___x_2066_ = lean_uint64_shift_right(v___x_2064_, v___x_2065_);
    v_fold_2067_ = lean_uint64_xor(v___x_2064_, v___x_2066_);
    v___x_2068_ = 16u64;
    v___x_2069_ = lean_uint64_shift_right(v_fold_2067_, v___x_2068_);
    v___x_2070_ = lean_uint64_xor(v_fold_2067_, v___x_2069_);
    v___x_2071_ = lean_uint64_to_usize(v___x_2070_);
    v___x_2072_ = lean_usize_of_nat(v___x_2063_);
    v___x_2073_ = 1usize;
    v___x_2074_ = lean_usize_sub(v___x_2072_, v___x_2073_);
    v___x_2075_ = lean_usize_land(v___x_2071_, v___x_2074_);
    v___x_2076_ = lean_array_uget_borrowed(v_buckets_2062_, v___x_2075_);
    v___x_2077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_2061_, v___x_2076_);
    return v___x_2077_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg___boxed(
    mut v_m_2078_: *mut leanh::LeanObject,
    mut v_a_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2080_: u8 = 0;
    let mut v_r_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_2078_, v_a_2079_);
    leanh::lean_dec(v_a_2079_);
    leanh::lean_dec_ref(v_m_2078_);
    v_r_2081_ = leanh::lean_box((v_res_2080_) as usize);
    return v_r_2081_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed(
    mut v_e_2082_: *mut leanh::LeanObject,
    mut v___y_2083_: *mut leanh::LeanObject,
    mut v___y_2084_: *mut leanh::LeanObject,
    mut v___y_2085_: *mut leanh::LeanObject,
    mut v___y_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_Compiler_LCNF_Closure_collectType___lam__0(
        v_e_2082_,
        v___y_2083_,
        v___y_2084_,
        v___y_2085_,
        v___y_2086_,
        v___y_2087_,
        v___y_2088_,
    );
    leanh::lean_dec(v___y_2088_);
    leanh::lean_dec_ref(v___y_2087_);
    leanh::lean_dec(v___y_2086_);
    leanh::lean_dec_ref(v___y_2085_);
    leanh::lean_dec(v___y_2084_);
    leanh::lean_dec_ref(v___y_2083_);
    leanh::lean_dec_ref(v_e_2082_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectType(
    mut v_type_2092_: *mut leanh::LeanObject,
    mut v_a_2093_: *mut leanh::LeanObject,
    mut v_a_2094_: *mut leanh::LeanObject,
    mut v_a_2095_: *mut leanh::LeanObject,
    mut v_a_2096_: *mut leanh::LeanObject,
    mut v_a_2097_: *mut leanh::LeanObject,
    mut v_a_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2100_: u8 = 0;
    v___x_2100_ = l_Lean_Expr_hasFVar(v_type_2092_);
    if v___x_2100_ == 0 {
        let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_type_2092_);
        v___x_2101_ = leanh::lean_box(0);
        v___x_2102_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2102_, 0, v___x_2101_);
        return v___x_2102_;
    } else {
        let mut v___f_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: u8 = 0;
        let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2103_ = leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed as *mut core::ffi::c_void,
            8,
            0,
        );
        v___x_2104_ = l_Lean_Compiler_LCNF_Closure_collectType___closed__0;
        v___x_2105_ = 0;
        v___x_2106_ =
            l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(
                v___x_2104_,
                v___f_2103_,
                v_type_2092_,
                v___x_2105_,
                v_a_2093_,
                v_a_2094_,
                v_a_2095_,
                v_a_2096_,
                v_a_2097_,
                v_a_2098_,
            );
        return v___x_2106_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(
    mut v_as_2107_: *mut leanh::LeanObject,
    mut v_i_2108_: usize,
    mut v_stop_2109_: usize,
    mut v_b_2110_: *mut leanh::LeanObject,
    mut v___y_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
    mut v___y_2114_: *mut leanh::LeanObject,
    mut v___y_2115_: *mut leanh::LeanObject,
    mut v___y_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: usize = 0;
    let mut v___x_2124_: usize = 0;
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2118_ = lean_usize_dec_eq(v_i_2108_, v_stop_2109_);
                if v___x_2118_ == 0 {
                    v___x_2119_ = lean_array_uget_borrowed(v_as_2107_, v_i_2108_);
                    v_type_2120_ = leanh::lean_ctor_get(v___x_2119_, 2);
                    leanh::lean_inc_ref(v_type_2120_);
                    v___x_2121_ = l_Lean_Compiler_LCNF_Closure_collectType(
                        v_type_2120_,
                        v___y_2111_,
                        v___y_2112_,
                        v___y_2113_,
                        v___y_2114_,
                        v___y_2115_,
                        v___y_2116_,
                    );
                    if leanh::lean_obj_tag(v___x_2121_) == 0 {
                        v_a_2122_ = leanh::lean_ctor_get(v___x_2121_, 0);
                        leanh::lean_inc(v_a_2122_);
                        leanh::lean_dec_ref_known(v___x_2121_, 1);
                        v___x_2123_ = 1usize;
                        v___x_2124_ = lean_usize_add(v_i_2108_, v___x_2123_);
                        v_i_2108_ = v___x_2124_;
                        v_b_2110_ = v_a_2122_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2121_;
                    }
                } else {
                    v___x_2126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2126_, 0, v_b_2110_);
                    return v___x_2126_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectParams(
    mut v_params_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
    mut v_a_2129_: *mut leanh::LeanObject,
    mut v_a_2130_: *mut leanh::LeanObject,
    mut v_a_2131_: *mut leanh::LeanObject,
    mut v_a_2132_: *mut leanh::LeanObject,
    mut v_a_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: u8 = 0;
    v___x_2135_ = leanh::lean_unsigned_to_nat(0);
    v___x_2136_ = lean_array_get_size(v_params_2127_);
    v___x_2137_ = leanh::lean_box(0);
    v___x_2138_ = lean_nat_dec_lt(v___x_2135_, v___x_2136_);
    if v___x_2138_ == 0 {
        let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2139_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2139_, 0, v___x_2137_);
        return v___x_2139_;
    } else {
        let mut v___x_2140_: u8 = 0;
        v___x_2140_ = lean_nat_dec_le(v___x_2136_, v___x_2136_);
        if v___x_2140_ == 0 {
            if v___x_2138_ == 0 {
                let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2141_, 0, v___x_2137_);
                return v___x_2141_;
            } else {
                let mut v___x_2142_: usize = 0;
                let mut v___x_2143_: usize = 0;
                let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2142_ = 0usize;
                v___x_2143_ = lean_usize_of_nat(v___x_2136_);
                v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_2127_, v___x_2142_, v___x_2143_, v___x_2137_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
                return v___x_2144_;
            }
        } else {
            let mut v___x_2145_: usize = 0;
            let mut v___x_2146_: usize = 0;
            let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2145_ = 0usize;
            v___x_2146_ = lean_usize_of_nat(v___x_2136_);
            v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_2127_, v___x_2145_, v___x_2146_, v___x_2137_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
            return v___x_2147_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectArg(
    mut v_arg_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
    mut v_a_2152_: *mut leanh::LeanObject,
    mut v_a_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_arg_2148_) {
        0 => {
            let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2156_ = leanh::lean_box(0);
            v___x_2157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2157_, 0, v___x_2156_);
            return v___x_2157_;
        }
        1 => {
            let mut v_fvarId_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_2158_ = leanh::lean_ctor_get(v_arg_2148_, 0);
            leanh::lean_inc(v_fvarId_2158_);
            leanh::lean_dec_ref_known(v_arg_2148_, 1);
            v___x_2159_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
                v_fvarId_2158_,
                v_a_2149_,
                v_a_2150_,
                v_a_2151_,
                v_a_2152_,
                v_a_2153_,
                v_a_2154_,
            );
            return v___x_2159_;
        }
        _ => {
            let mut v_expr_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_expr_2160_ = leanh::lean_ctor_get(v_arg_2148_, 0);
            leanh::lean_inc_ref(v_expr_2160_);
            leanh::lean_dec_ref_known(v_arg_2148_, 1);
            v___x_2161_ = l_Lean_Compiler_LCNF_Closure_collectType(
                v_expr_2160_,
                v_a_2149_,
                v_a_2150_,
                v_a_2151_,
                v_a_2152_,
                v_a_2153_,
                v_a_2154_,
            );
            return v___x_2161_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(
    mut v_as_2162_: *mut leanh::LeanObject,
    mut v_i_2163_: usize,
    mut v_stop_2164_: usize,
    mut v_b_2165_: *mut leanh::LeanObject,
    mut v___y_2166_: *mut leanh::LeanObject,
    mut v___y_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
    mut v___y_2169_: *mut leanh::LeanObject,
    mut v___y_2170_: *mut leanh::LeanObject,
    mut v___y_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: usize = 0;
    let mut v___x_2178_: usize = 0;
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2173_ = lean_usize_dec_eq(v_i_2163_, v_stop_2164_);
                if v___x_2173_ == 0 {
                    v___x_2174_ = lean_array_uget_borrowed(v_as_2162_, v_i_2163_);
                    leanh::lean_inc(v___x_2174_);
                    v___x_2175_ = l_Lean_Compiler_LCNF_Closure_collectArg(
                        v___x_2174_,
                        v___y_2166_,
                        v___y_2167_,
                        v___y_2168_,
                        v___y_2169_,
                        v___y_2170_,
                        v___y_2171_,
                    );
                    if leanh::lean_obj_tag(v___x_2175_) == 0 {
                        v_a_2176_ = leanh::lean_ctor_get(v___x_2175_, 0);
                        leanh::lean_inc(v_a_2176_);
                        leanh::lean_dec_ref_known(v___x_2175_, 1);
                        v___x_2177_ = 1usize;
                        v___x_2178_ = lean_usize_add(v_i_2163_, v___x_2177_);
                        v_i_2163_ = v___x_2178_;
                        v_b_2165_ = v_a_2176_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2175_;
                    }
                } else {
                    v___x_2180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2180_, 0, v_b_2165_);
                    return v___x_2180_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectLetValue(
    mut v_e_2181_: *mut leanh::LeanObject,
    mut v_a_2182_: *mut leanh::LeanObject,
    mut v_a_2183_: *mut leanh::LeanObject,
    mut v_a_2184_: *mut leanh::LeanObject,
    mut v_a_2185_: *mut leanh::LeanObject,
    mut v_a_2186_: *mut leanh::LeanObject,
    mut v_a_2187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_unused_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: usize = 0;
    let mut v___x_2211_: usize = 0;
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: usize = 0;
    let mut v___x_2234_: usize = 0;
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: usize = 0;
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_unused_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_2181_) {
                0 => {
                    v_isSharedCheck_2196_ = (!leanh::lean_is_exclusive(v_e_2181_)) as u8;
                    if v_isSharedCheck_2196_ == 0 {
                        v_unused_2197_ = leanh::lean_ctor_get(v_e_2181_, 0);
                        leanh::lean_dec(v_unused_2197_);
                        v___x_2190_ = v_e_2181_;
                        v_isShared_2191_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_2181_);
                        v___x_2190_ = leanh::lean_box(0);
                        v_isShared_2191_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2198_ = leanh::lean_box(0);
                    v___x_2199_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2199_, 0, v___x_2198_);
                    return v___x_2199_;
                }
                2 => {
                    v_struct_2200_ = leanh::lean_ctor_get(v_e_2181_, 2);
                    leanh::lean_inc(v_struct_2200_);
                    leanh::lean_dec_ref_known(v_e_2181_, 3);
                    v___x_2201_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
                        v_struct_2200_,
                        v_a_2182_,
                        v_a_2183_,
                        v_a_2184_,
                        v_a_2185_,
                        v_a_2186_,
                        v_a_2187_,
                    );
                    return v___x_2201_;
                }
                3 => {
                    v_args_2202_ = leanh::lean_ctor_get(v_e_2181_, 2);
                    leanh::lean_inc_ref(v_args_2202_);
                    leanh::lean_dec_ref_known(v_e_2181_, 3);
                    v___x_2203_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2204_ = lean_array_get_size(v_args_2202_);
                    v___x_2205_ = leanh::lean_box(0);
                    v___x_2206_ = lean_nat_dec_lt(v___x_2203_, v___x_2204_);
                    if v___x_2206_ == 0 {
                        leanh::lean_dec_ref(v_args_2202_);
                        v___x_2207_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2207_, 0, v___x_2205_);
                        return v___x_2207_;
                    } else {
                        v___x_2208_ = lean_nat_dec_le(v___x_2204_, v___x_2204_);
                        if v___x_2208_ == 0 {
                            if v___x_2206_ == 0 {
                                leanh::lean_dec_ref(v_args_2202_);
                                v___x_2209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2209_, 0, v___x_2205_);
                                return v___x_2209_;
                            } else {
                                v___x_2210_ = 0usize;
                                v___x_2211_ = lean_usize_of_nat(v___x_2204_);
                                v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2202_, v___x_2210_, v___x_2211_, v___x_2205_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                                leanh::lean_dec_ref(v_args_2202_);
                                return v___x_2212_;
                            }
                        } else {
                            v___x_2213_ = 0usize;
                            v___x_2214_ = lean_usize_of_nat(v___x_2204_);
                            v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2202_, v___x_2213_, v___x_2214_, v___x_2205_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                            leanh::lean_dec_ref(v_args_2202_);
                            return v___x_2215_;
                        }
                    }
                }
                _ => {
                    v_fvarId_2216_ = leanh::lean_ctor_get(v_e_2181_, 0);
                    leanh::lean_inc(v_fvarId_2216_);
                    v_args_2217_ = leanh::lean_ctor_get(v_e_2181_, 1);
                    leanh::lean_inc_ref(v_args_2217_);
                    leanh::lean_dec_ref_known(v_e_2181_, 2);
                    v___x_2218_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
                        v_fvarId_2216_,
                        v_a_2182_,
                        v_a_2183_,
                        v_a_2184_,
                        v_a_2185_,
                        v_a_2186_,
                        v_a_2187_,
                    );
                    if leanh::lean_obj_tag(v___x_2218_) == 0 {
                        v_isSharedCheck_2239_ =
                            (!leanh::lean_is_exclusive(v___x_2218_)) as u8;
                        if v_isSharedCheck_2239_ == 0 {
                            v_unused_2240_ = leanh::lean_ctor_get(v___x_2218_, 0);
                            leanh::lean_dec(v_unused_2240_);
                            v___x_2220_ = v___x_2218_;
                            v_isShared_2221_ = v_isSharedCheck_2239_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2218_);
                            v___x_2220_ = leanh::lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2239_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_args_2217_);
                        return v___x_2218_;
                    }
                }
            },
            1 => {
                v___x_2192_ = leanh::lean_box(0);
                if v_isShared_2191_ == 0 {
                    leanh::lean_ctor_set(v___x_2190_, 0, v___x_2192_);
                    v___x_2194_ = v___x_2190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
                    v___x_2194_ = v_reuseFailAlloc_2195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2194_;
            }
            3 => {
                v___x_2222_ = leanh::lean_unsigned_to_nat(0);
                v___x_2223_ = lean_array_get_size(v_args_2217_);
                v___x_2224_ = leanh::lean_box(0);
                v___x_2225_ = lean_nat_dec_lt(v___x_2222_, v___x_2223_);
                if v___x_2225_ == 0 {
                    leanh::lean_dec_ref(v_args_2217_);
                    if v_isShared_2221_ == 0 {
                        leanh::lean_ctor_set(v___x_2220_, 0, v___x_2224_);
                        v___x_2227_ = v___x_2220_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2228_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2224_);
                        v___x_2227_ = v_reuseFailAlloc_2228_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2229_ = lean_nat_dec_le(v___x_2223_, v___x_2223_);
                    if v___x_2229_ == 0 {
                        if v___x_2225_ == 0 {
                            leanh::lean_dec_ref(v_args_2217_);
                            if v_isShared_2221_ == 0 {
                                leanh::lean_ctor_set(v___x_2220_, 0, v___x_2224_);
                                v___x_2231_ = v___x_2220_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_2232_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2224_);
                                v___x_2231_ = v_reuseFailAlloc_2232_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2220_);
                            v___x_2233_ = 0usize;
                            v___x_2234_ = lean_usize_of_nat(v___x_2223_);
                            v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2217_, v___x_2233_, v___x_2234_, v___x_2224_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                            leanh::lean_dec_ref(v_args_2217_);
                            return v___x_2235_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2220_);
                        v___x_2236_ = 0usize;
                        v___x_2237_ = lean_usize_of_nat(v___x_2223_);
                        v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2217_, v___x_2236_, v___x_2237_, v___x_2224_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                        leanh::lean_dec_ref(v_args_2217_);
                        return v___x_2238_;
                    }
                }
            }
            4 => {
                return v___x_2227_;
            }
            5 => {
                return v___x_2231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(
    mut v_as_2241_: *mut leanh::LeanObject,
    mut v_i_2242_: usize,
    mut v_stop_2243_: usize,
    mut v_b_2244_: *mut leanh::LeanObject,
    mut v___y_2245_: *mut leanh::LeanObject,
    mut v___y_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: usize = 0;
    let mut v___x_2258_: u8 = 0;
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2258_ = lean_usize_dec_eq(v_i_2242_, v_stop_2243_);
                if v___x_2258_ == 0 {
                    v___x_2259_ = lean_array_uget_borrowed(v_as_2241_, v_i_2242_);
                    if leanh::lean_obj_tag(v___x_2259_) == 0 {
                        v_params_2260_ = leanh::lean_ctor_get(v___x_2259_, 1);
                        v_code_2261_ = leanh::lean_ctor_get(v___x_2259_, 2);
                        v___x_2262_ = l_Lean_Compiler_LCNF_Closure_collectParams(
                            v_params_2260_,
                            v___y_2245_,
                            v___y_2246_,
                            v___y_2247_,
                            v___y_2248_,
                            v___y_2249_,
                            v___y_2250_,
                        );
                        if leanh::lean_obj_tag(v___x_2262_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2262_, 1);
                            leanh::lean_inc_ref(v_code_2261_);
                            v___x_2263_ = l_Lean_Compiler_LCNF_Closure_collectCode(
                                v_code_2261_,
                                v___y_2245_,
                                v___y_2246_,
                                v___y_2247_,
                                v___y_2248_,
                                v___y_2249_,
                                v___y_2250_,
                            );
                            v___y_2253_ = v___x_2263_;
                            state = 1;
                            continue;
                        } else {
                            v___y_2253_ = v___x_2262_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_code_2264_ = leanh::lean_ctor_get(v___x_2259_, 0);
                        leanh::lean_inc_ref(v_code_2264_);
                        v___x_2265_ = l_Lean_Compiler_LCNF_Closure_collectCode(
                            v_code_2264_,
                            v___y_2245_,
                            v___y_2246_,
                            v___y_2247_,
                            v___y_2248_,
                            v___y_2249_,
                            v___y_2250_,
                        );
                        v___y_2253_ = v___x_2265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2266_, 0, v_b_2244_);
                    return v___x_2266_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2253_) == 0 {
                    v_a_2254_ = leanh::lean_ctor_get(v___y_2253_, 0);
                    leanh::lean_inc(v_a_2254_);
                    leanh::lean_dec_ref_known(v___y_2253_, 1);
                    v___x_2255_ = 1usize;
                    v___x_2256_ = lean_usize_add(v_i_2242_, v___x_2255_);
                    v_i_2242_ = v___x_2256_;
                    v_b_2244_ = v_a_2254_;
                    state = 0;
                    continue;
                } else {
                    return v___y_2253_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectCode(
    mut v_c_2267_: *mut leanh::LeanObject,
    mut v_a_2268_: *mut leanh::LeanObject,
    mut v_a_2269_: *mut leanh::LeanObject,
    mut v_a_2270_: *mut leanh::LeanObject,
    mut v_a_2271_: *mut leanh::LeanObject,
    mut v_a_2272_: *mut leanh::LeanObject,
    mut v_a_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: usize = 0;
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: usize = 0;
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: usize = 0;
    let mut v___x_2328_: usize = 0;
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: usize = 0;
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_unused_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_c_2267_) {
                0 => {
                    v_decl_2286_ = leanh::lean_ctor_get(v_c_2267_, 0);
                    leanh::lean_inc_ref(v_decl_2286_);
                    v_k_2287_ = leanh::lean_ctor_get(v_c_2267_, 1);
                    leanh::lean_inc_ref(v_k_2287_);
                    leanh::lean_dec_ref_known(v_c_2267_, 2);
                    v_type_2288_ = leanh::lean_ctor_get(v_decl_2286_, 2);
                    leanh::lean_inc_ref(v_type_2288_);
                    v_value_2289_ = leanh::lean_ctor_get(v_decl_2286_, 3);
                    leanh::lean_inc(v_value_2289_);
                    leanh::lean_dec_ref(v_decl_2286_);
                    v___x_2290_ = l_Lean_Compiler_LCNF_Closure_collectType(
                        v_type_2288_,
                        v_a_2268_,
                        v_a_2269_,
                        v_a_2270_,
                        v_a_2271_,
                        v_a_2272_,
                        v_a_2273_,
                    );
                    if leanh::lean_obj_tag(v___x_2290_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2290_, 1);
                        v___x_2291_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(
                            v_value_2289_,
                            v_a_2268_,
                            v_a_2269_,
                            v_a_2270_,
                            v_a_2271_,
                            v_a_2272_,
                            v_a_2273_,
                        );
                        if leanh::lean_obj_tag(v___x_2291_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2291_, 1);
                            v_c_2267_ = v_k_2287_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_k_2287_);
                            return v___x_2291_;
                        }
                    } else {
                        leanh::lean_dec(v_value_2289_);
                        leanh::lean_dec_ref(v_k_2287_);
                        return v___x_2290_;
                    }
                }
                3 => {
                    v_args_2293_ = leanh::lean_ctor_get(v_c_2267_, 1);
                    leanh::lean_inc_ref(v_args_2293_);
                    leanh::lean_dec_ref_known(v_c_2267_, 2);
                    v___x_2294_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2295_ = lean_array_get_size(v_args_2293_);
                    v___x_2296_ = leanh::lean_box(0);
                    v___x_2297_ = lean_nat_dec_lt(v___x_2294_, v___x_2295_);
                    if v___x_2297_ == 0 {
                        leanh::lean_dec_ref(v_args_2293_);
                        v___x_2298_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2298_, 0, v___x_2296_);
                        return v___x_2298_;
                    } else {
                        v___x_2299_ = lean_nat_dec_le(v___x_2295_, v___x_2295_);
                        if v___x_2299_ == 0 {
                            if v___x_2297_ == 0 {
                                leanh::lean_dec_ref(v_args_2293_);
                                v___x_2300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2300_, 0, v___x_2296_);
                                return v___x_2300_;
                            } else {
                                v___x_2301_ = 0usize;
                                v___x_2302_ = lean_usize_of_nat(v___x_2295_);
                                v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2293_, v___x_2301_, v___x_2302_, v___x_2296_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                leanh::lean_dec_ref(v_args_2293_);
                                return v___x_2303_;
                            }
                        } else {
                            v___x_2304_ = 0usize;
                            v___x_2305_ = lean_usize_of_nat(v___x_2295_);
                            v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2293_, v___x_2304_, v___x_2305_, v___x_2296_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                            leanh::lean_dec_ref(v_args_2293_);
                            return v___x_2306_;
                        }
                    }
                }
                4 => {
                    v_cases_2307_ = leanh::lean_ctor_get(v_c_2267_, 0);
                    leanh::lean_inc_ref(v_cases_2307_);
                    leanh::lean_dec_ref_known(v_c_2267_, 1);
                    v_resultType_2308_ = leanh::lean_ctor_get(v_cases_2307_, 1);
                    leanh::lean_inc_ref(v_resultType_2308_);
                    v_discr_2309_ = leanh::lean_ctor_get(v_cases_2307_, 2);
                    leanh::lean_inc(v_discr_2309_);
                    v_alts_2310_ = leanh::lean_ctor_get(v_cases_2307_, 3);
                    leanh::lean_inc_ref(v_alts_2310_);
                    leanh::lean_dec_ref(v_cases_2307_);
                    v___x_2311_ = l_Lean_Compiler_LCNF_Closure_collectType(
                        v_resultType_2308_,
                        v_a_2268_,
                        v_a_2269_,
                        v_a_2270_,
                        v_a_2271_,
                        v_a_2272_,
                        v_a_2273_,
                    );
                    if leanh::lean_obj_tag(v___x_2311_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2311_, 1);
                        v___x_2312_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
                            v_discr_2309_,
                            v_a_2268_,
                            v_a_2269_,
                            v_a_2270_,
                            v_a_2271_,
                            v_a_2272_,
                            v_a_2273_,
                        );
                        if leanh::lean_obj_tag(v___x_2312_) == 0 {
                            v_isSharedCheck_2333_ =
                                (!leanh::lean_is_exclusive(v___x_2312_)) as u8;
                            if v_isSharedCheck_2333_ == 0 {
                                v_unused_2334_ = leanh::lean_ctor_get(v___x_2312_, 0);
                                leanh::lean_dec(v_unused_2334_);
                                v___x_2314_ = v___x_2312_;
                                v_isShared_2315_ = v_isSharedCheck_2333_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2312_);
                                v___x_2314_ = leanh::lean_box(0);
                                v_isShared_2315_ = v_isSharedCheck_2333_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_alts_2310_);
                            return v___x_2312_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_alts_2310_);
                        leanh::lean_dec(v_discr_2309_);
                        return v___x_2311_;
                    }
                }
                5 => {
                    v_fvarId_2335_ = leanh::lean_ctor_get(v_c_2267_, 0);
                    leanh::lean_inc(v_fvarId_2335_);
                    leanh::lean_dec_ref_known(v_c_2267_, 1);
                    v___x_2336_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
                        v_fvarId_2335_,
                        v_a_2268_,
                        v_a_2269_,
                        v_a_2270_,
                        v_a_2271_,
                        v_a_2272_,
                        v_a_2273_,
                    );
                    return v___x_2336_;
                }
                6 => {
                    v_type_2337_ = leanh::lean_ctor_get(v_c_2267_, 0);
                    leanh::lean_inc_ref(v_type_2337_);
                    leanh::lean_dec_ref_known(v_c_2267_, 1);
                    v___x_2338_ = l_Lean_Compiler_LCNF_Closure_collectType(
                        v_type_2337_,
                        v_a_2268_,
                        v_a_2269_,
                        v_a_2270_,
                        v_a_2271_,
                        v_a_2272_,
                        v_a_2273_,
                    );
                    return v___x_2338_;
                }
                _ => {
                    v_decl_2339_ = leanh::lean_ctor_get(v_c_2267_, 0);
                    leanh::lean_inc_ref(v_decl_2339_);
                    v_k_2340_ = leanh::lean_ctor_get(v_c_2267_, 1);
                    leanh::lean_inc_ref(v_k_2340_);
                    leanh::lean_dec_ref(v_c_2267_);
                    v_decl_2276_ = v_decl_2339_;
                    v_k_2277_ = v_k_2340_;
                    v___y_2278_ = v_a_2268_;
                    v___y_2279_ = v_a_2269_;
                    v___y_2280_ = v_a_2270_;
                    v___y_2281_ = v_a_2271_;
                    v___y_2282_ = v_a_2272_;
                    v___y_2283_ = v_a_2273_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2284_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(
                    v_decl_2276_,
                    v___y_2278_,
                    v___y_2279_,
                    v___y_2280_,
                    v___y_2281_,
                    v___y_2282_,
                    v___y_2283_,
                );
                if leanh::lean_obj_tag(v___x_2284_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2284_, 1);
                    v_c_2267_ = v_k_2277_;
                    v_a_2268_ = v___y_2278_;
                    v_a_2269_ = v___y_2279_;
                    v_a_2270_ = v___y_2280_;
                    v_a_2271_ = v___y_2281_;
                    v_a_2272_ = v___y_2282_;
                    v_a_2273_ = v___y_2283_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_k_2277_);
                    return v___x_2284_;
                }
            }
            2 => {
                v___x_2316_ = leanh::lean_unsigned_to_nat(0);
                v___x_2317_ = lean_array_get_size(v_alts_2310_);
                v___x_2318_ = leanh::lean_box(0);
                v___x_2319_ = lean_nat_dec_lt(v___x_2316_, v___x_2317_);
                if v___x_2319_ == 0 {
                    leanh::lean_dec_ref(v_alts_2310_);
                    if v_isShared_2315_ == 0 {
                        leanh::lean_ctor_set(v___x_2314_, 0, v___x_2318_);
                        v___x_2321_ = v___x_2314_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2318_);
                        v___x_2321_ = v_reuseFailAlloc_2322_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2323_ = lean_nat_dec_le(v___x_2317_, v___x_2317_);
                    if v___x_2323_ == 0 {
                        if v___x_2319_ == 0 {
                            leanh::lean_dec_ref(v_alts_2310_);
                            if v_isShared_2315_ == 0 {
                                leanh::lean_ctor_set(v___x_2314_, 0, v___x_2318_);
                                v___x_2325_ = v___x_2314_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2326_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2318_);
                                v___x_2325_ = v_reuseFailAlloc_2326_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2314_);
                            v___x_2327_ = 0usize;
                            v___x_2328_ = lean_usize_of_nat(v___x_2317_);
                            v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_2310_, v___x_2327_, v___x_2328_, v___x_2318_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                            leanh::lean_dec_ref(v_alts_2310_);
                            return v___x_2329_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2314_);
                        v___x_2330_ = 0usize;
                        v___x_2331_ = lean_usize_of_nat(v___x_2317_);
                        v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_2310_, v___x_2330_, v___x_2331_, v___x_2318_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                        leanh::lean_dec_ref(v_alts_2310_);
                        return v___x_2332_;
                    }
                }
            }
            3 => {
                return v___x_2321_;
            }
            4 => {
                return v___x_2325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectFunDecl(
    mut v_decl_2341_: *mut leanh::LeanObject,
    mut v_a_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_a_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_params_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_params_2349_ = leanh::lean_ctor_get(v_decl_2341_, 2);
    leanh::lean_inc_ref(v_params_2349_);
    v_type_2350_ = leanh::lean_ctor_get(v_decl_2341_, 3);
    leanh::lean_inc_ref(v_type_2350_);
    v_value_2351_ = leanh::lean_ctor_get(v_decl_2341_, 4);
    leanh::lean_inc_ref(v_value_2351_);
    leanh::lean_dec_ref(v_decl_2341_);
    v___x_2352_ = l_Lean_Compiler_LCNF_Closure_collectType(
        v_type_2350_,
        v_a_2342_,
        v_a_2343_,
        v_a_2344_,
        v_a_2345_,
        v_a_2346_,
        v_a_2347_,
    );
    if leanh::lean_obj_tag(v___x_2352_) == 0 {
        let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_2352_, 1);
        v___x_2353_ = l_Lean_Compiler_LCNF_Closure_collectParams(
            v_params_2349_,
            v_a_2342_,
            v_a_2343_,
            v_a_2344_,
            v_a_2345_,
            v_a_2346_,
            v_a_2347_,
        );
        leanh::lean_dec_ref(v_params_2349_);
        if leanh::lean_obj_tag(v___x_2353_) == 0 {
            let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_2353_, 1);
            v___x_2354_ = l_Lean_Compiler_LCNF_Closure_collectCode(
                v_value_2351_,
                v_a_2342_,
                v_a_2343_,
                v_a_2344_,
                v_a_2345_,
                v_a_2346_,
                v_a_2347_,
            );
            return v___x_2354_;
        } else {
            leanh::lean_dec_ref(v_value_2351_);
            return v___x_2353_;
        }
    } else {
        leanh::lean_dec_ref(v_value_2351_);
        leanh::lean_dec_ref(v_params_2349_);
        return v___x_2352_;
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
    v___x_2359_ = leanh::lean_unsigned_to_nat(10);
    v___x_2360_ = leanh::lean_unsigned_to_nat(149);
    v___x_2361_ = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1;
    v___x_2362_ = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0;
    v___x_2363_ = l_mkPanicMessageWithDecl(
        v___x_2362_,
        v___x_2361_,
        v___x_2360_,
        v___x_2359_,
        v___x_2358_,
    );
    return v___x_2363_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectFVar(
    mut v_fvarId_2364_: *mut leanh::LeanObject,
    mut v_a_2365_: *mut leanh::LeanObject,
    mut v_a_2366_: *mut leanh::LeanObject,
    mut v_a_2367_: *mut leanh::LeanObject,
    mut v_a_2368_: *mut leanh::LeanObject,
    mut v_a_2369_: *mut leanh::LeanObject,
    mut v_a_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v_inScope_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstract_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: u8 = 0;
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v_val_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v_fvarId_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_unused_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2445_: u8 = 0;
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2454_: u8 = 0;
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_isSharedCheck_2472_: u8 = 0;
    let mut v_unused_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v_fvarId_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2493_: u8 = 0;
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut v_isSharedCheck_2514_: u8 = 0;
    let mut v_unused_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_unused_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_a_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2554_: u8 = 0;
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_a_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2372_ = lean_st_ref_get(v_a_2366_);
                v_visited_2373_ = leanh::lean_ctor_get(v___x_2372_, 0);
                leanh::lean_inc_ref(v_visited_2373_);
                leanh::lean_dec(v___x_2372_);
                v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_visited_2373_, v_fvarId_2364_);
                leanh::lean_dec_ref(v_visited_2373_);
                if v___x_2374_ == 0 {
                    leanh::lean_inc(v_fvarId_2364_);
                    v___x_2375_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(
                        v_fvarId_2364_,
                        v_a_2366_,
                    );
                    if leanh::lean_obj_tag(v___x_2375_) == 0 {
                        v_isSharedCheck_2564_ =
                            (!leanh::lean_is_exclusive(v___x_2375_)) as u8;
                        if v_isSharedCheck_2564_ == 0 {
                            v_unused_2565_ = leanh::lean_ctor_get(v___x_2375_, 0);
                            leanh::lean_dec(v_unused_2565_);
                            v___x_2377_ = v___x_2375_;
                            v_isShared_2378_ = v_isSharedCheck_2564_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2375_);
                            v___x_2377_ = leanh::lean_box(0);
                            v_isShared_2378_ = v_isSharedCheck_2564_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_2364_);
                        return v___x_2375_;
                    }
                } else {
                    leanh::lean_dec(v_fvarId_2364_);
                    v___x_2566_ = leanh::lean_box(0);
                    v___x_2567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2567_, 0, v___x_2566_);
                    return v___x_2567_;
                }
            }
            1 => {
                v_inScope_2379_ = leanh::lean_ctor_get(v_a_2365_, 0);
                v_abstract_2380_ = leanh::lean_ctor_get(v_a_2365_, 1);
                leanh::lean_inc_ref(v_inScope_2379_);
                leanh::lean_inc(v_fvarId_2364_);
                v___x_2381_ = leanh::lean_apply_1(v_inScope_2379_, v_fvarId_2364_);
                v___x_2382_ = (leanh::lean_unbox(v___x_2381_) as u8);
                if v___x_2382_ == 0 {
                    leanh::lean_dec(v_fvarId_2364_);
                    v___x_2383_ = leanh::lean_box(0);
                    if v_isShared_2378_ == 0 {
                        leanh::lean_ctor_set(v___x_2377_, 0, v___x_2383_);
                        v___x_2385_ = v___x_2377_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
                        v___x_2385_ = v_reuseFailAlloc_2386_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2377_);
                    v___x_2387_ = 0;
                    v___x_2388_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                        v___x_2387_,
                        v_fvarId_2364_,
                        v_a_2368_,
                    );
                    if leanh::lean_obj_tag(v___x_2388_) == 0 {
                        v_a_2389_ = leanh::lean_ctor_get(v___x_2388_, 0);
                        v_isSharedCheck_2555_ =
                            (!leanh::lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2555_ == 0 {
                            v___x_2391_ = v___x_2388_;
                            v_isShared_2392_ = v_isSharedCheck_2555_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2389_);
                            leanh::lean_dec(v___x_2388_);
                            v___x_2391_ = leanh::lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2555_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_2364_);
                        v_a_2556_ = leanh::lean_ctor_get(v___x_2388_, 0);
                        v_isSharedCheck_2563_ =
                            (!leanh::lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2563_ == 0 {
                            v___x_2558_ = v___x_2388_;
                            v_isShared_2559_ = v_isSharedCheck_2563_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2556_);
                            leanh::lean_dec(v___x_2388_);
                            v___x_2558_ = leanh::lean_box(0);
                            v_isShared_2559_ = v_isSharedCheck_2563_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2385_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2389_) == 1 {
                    leanh::lean_dec(v_fvarId_2364_);
                    v_val_2393_ = leanh::lean_ctor_get(v_a_2389_, 0);
                    v_isSharedCheck_2446_ = (!leanh::lean_is_exclusive(v_a_2389_)) as u8;
                    if v_isSharedCheck_2446_ == 0 {
                        v___x_2395_ = v_a_2389_;
                        v_isShared_2396_ = v_isSharedCheck_2446_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2393_);
                        leanh::lean_dec(v_a_2389_);
                        v___x_2395_ = leanh::lean_box(0);
                        v_isShared_2396_ = v_isSharedCheck_2446_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2391_);
                    leanh::lean_dec(v_a_2389_);
                    v___x_2447_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(
                        v___x_2387_,
                        v_fvarId_2364_,
                        v_a_2368_,
                    );
                    if leanh::lean_obj_tag(v___x_2447_) == 0 {
                        v_a_2448_ = leanh::lean_ctor_get(v___x_2447_, 0);
                        leanh::lean_inc(v_a_2448_);
                        leanh::lean_dec_ref_known(v___x_2447_, 1);
                        if leanh::lean_obj_tag(v_a_2448_) == 1 {
                            leanh::lean_dec(v_fvarId_2364_);
                            v_val_2449_ = leanh::lean_ctor_get(v_a_2448_, 0);
                            leanh::lean_inc(v_val_2449_);
                            leanh::lean_dec_ref_known(v_a_2448_, 1);
                            v_type_2450_ = leanh::lean_ctor_get(v_val_2449_, 2);
                            leanh::lean_inc_ref(v_type_2450_);
                            v___x_2451_ = l_Lean_Compiler_LCNF_Closure_collectType(
                                v_type_2450_,
                                v_a_2365_,
                                v_a_2366_,
                                v_a_2367_,
                                v_a_2368_,
                                v_a_2369_,
                                v_a_2370_,
                            );
                            if leanh::lean_obj_tag(v___x_2451_) == 0 {
                                v_isSharedCheck_2472_ =
                                    (!leanh::lean_is_exclusive(v___x_2451_)) as u8;
                                if v_isSharedCheck_2472_ == 0 {
                                    v_unused_2473_ = leanh::lean_ctor_get(v___x_2451_, 0);
                                    leanh::lean_dec(v_unused_2473_);
                                    v___x_2453_ = v___x_2451_;
                                    v_isShared_2454_ = v_isSharedCheck_2472_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_2451_);
                                    v___x_2453_ = leanh::lean_box(0);
                                    v_isShared_2454_ = v_isSharedCheck_2472_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_2449_);
                                return v___x_2451_;
                            }
                        } else {
                            leanh::lean_dec(v_a_2448_);
                            v___x_2474_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                                v___x_2387_,
                                v_fvarId_2364_,
                                v_a_2368_,
                            );
                            leanh::lean_dec(v_fvarId_2364_);
                            if leanh::lean_obj_tag(v___x_2474_) == 0 {
                                v_a_2475_ = leanh::lean_ctor_get(v___x_2474_, 0);
                                leanh::lean_inc(v_a_2475_);
                                leanh::lean_dec_ref_known(v___x_2474_, 1);
                                if leanh::lean_obj_tag(v_a_2475_) == 1 {
                                    v_val_2476_ = leanh::lean_ctor_get(v_a_2475_, 0);
                                    v_isSharedCheck_2536_ =
                                        (!leanh::lean_is_exclusive(v_a_2475_)) as u8;
                                    if v_isSharedCheck_2536_ == 0 {
                                        v___x_2478_ = v_a_2475_;
                                        v_isShared_2479_ = v_isSharedCheck_2536_;
                                        state = 17;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_2476_);
                                        leanh::lean_dec(v_a_2475_);
                                        v___x_2478_ = leanh::lean_box(0);
                                        v_isShared_2479_ = v_isSharedCheck_2536_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2475_);
                                    v___x_2537_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once), _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3);
                                    v___x_2538_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v___x_2537_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
                                    return v___x_2538_;
                                }
                            } else {
                                v_a_2539_ = leanh::lean_ctor_get(v___x_2474_, 0);
                                v_isSharedCheck_2546_ =
                                    (!leanh::lean_is_exclusive(v___x_2474_)) as u8;
                                if v_isSharedCheck_2546_ == 0 {
                                    v___x_2541_ = v___x_2474_;
                                    v_isShared_2542_ = v_isSharedCheck_2546_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2539_);
                                    leanh::lean_dec(v___x_2474_);
                                    v___x_2541_ = leanh::lean_box(0);
                                    v_isShared_2542_ = v_isSharedCheck_2546_;
                                    state = 27;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_2364_);
                        v_a_2547_ = leanh::lean_ctor_get(v___x_2447_, 0);
                        v_isSharedCheck_2554_ =
                            (!leanh::lean_is_exclusive(v___x_2447_)) as u8;
                        if v_isSharedCheck_2554_ == 0 {
                            v___x_2549_ = v___x_2447_;
                            v_isShared_2550_ = v_isSharedCheck_2554_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2547_);
                            leanh::lean_dec(v___x_2447_);
                            v___x_2549_ = leanh::lean_box(0);
                            v_isShared_2550_ = v_isSharedCheck_2554_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_fvarId_2397_ = leanh::lean_ctor_get(v_val_2393_, 0);
                v_binderName_2398_ = leanh::lean_ctor_get(v_val_2393_, 1);
                v_type_2399_ = leanh::lean_ctor_get(v_val_2393_, 3);
                leanh::lean_inc_ref(v_abstract_2380_);
                leanh::lean_inc(v_fvarId_2397_);
                v___x_2400_ = leanh::lean_apply_1(v_abstract_2380_, v_fvarId_2397_);
                v___x_2401_ = (leanh::lean_unbox(v___x_2400_) as u8);
                if v___x_2401_ == 0 {
                    leanh::lean_del_object(v___x_2391_);
                    leanh::lean_inc(v_val_2393_);
                    v___x_2402_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(
                        v_val_2393_,
                        v_a_2365_,
                        v_a_2366_,
                        v_a_2367_,
                        v_a_2368_,
                        v_a_2369_,
                        v_a_2370_,
                    );
                    if leanh::lean_obj_tag(v___x_2402_) == 0 {
                        v_isSharedCheck_2426_ =
                            (!leanh::lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2426_ == 0 {
                            v_unused_2427_ = leanh::lean_ctor_get(v___x_2402_, 0);
                            leanh::lean_dec(v_unused_2427_);
                            v___x_2404_ = v___x_2402_;
                            v_isShared_2405_ = v_isSharedCheck_2426_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2402_);
                            v___x_2404_ = leanh::lean_box(0);
                            v_isShared_2405_ = v_isSharedCheck_2426_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2395_);
                        leanh::lean_dec(v_val_2393_);
                        return v___x_2402_;
                    }
                } else {
                    leanh::lean_inc_ref(v_type_2399_);
                    leanh::lean_inc(v_binderName_2398_);
                    leanh::lean_inc(v_fvarId_2397_);
                    leanh::lean_del_object(v___x_2395_);
                    leanh::lean_dec(v_val_2393_);
                    v___x_2428_ = lean_st_ref_take(v_a_2366_);
                    v_visited_2429_ = leanh::lean_ctor_get(v___x_2428_, 0);
                    v_params_2430_ = leanh::lean_ctor_get(v___x_2428_, 1);
                    v_decls_2431_ = leanh::lean_ctor_get(v___x_2428_, 2);
                    v_isSharedCheck_2445_ = (!leanh::lean_is_exclusive(v___x_2428_)) as u8;
                    if v_isSharedCheck_2445_ == 0 {
                        v___x_2433_ = v___x_2428_;
                        v_isShared_2434_ = v_isSharedCheck_2445_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_decls_2431_);
                        leanh::lean_inc(v_params_2430_);
                        leanh::lean_inc(v_visited_2429_);
                        leanh::lean_dec(v___x_2428_);
                        v___x_2433_ = leanh::lean_box(0);
                        v_isShared_2434_ = v_isSharedCheck_2445_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2406_ = lean_st_ref_take(v_a_2366_);
                v_visited_2407_ = leanh::lean_ctor_get(v___x_2406_, 0);
                v_params_2408_ = leanh::lean_ctor_get(v___x_2406_, 1);
                v_decls_2409_ = leanh::lean_ctor_get(v___x_2406_, 2);
                v_isSharedCheck_2425_ = (!leanh::lean_is_exclusive(v___x_2406_)) as u8;
                if v_isSharedCheck_2425_ == 0 {
                    v___x_2411_ = v___x_2406_;
                    v_isShared_2412_ = v_isSharedCheck_2425_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_decls_2409_);
                    leanh::lean_inc(v_params_2408_);
                    leanh::lean_inc(v_visited_2407_);
                    leanh::lean_dec(v___x_2406_);
                    v___x_2411_ = leanh::lean_box(0);
                    v_isShared_2412_ = v_isSharedCheck_2425_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2396_ == 0 {
                    v___x_2414_ = v___x_2395_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_val_2393_);
                    v___x_2414_ = v_reuseFailAlloc_2424_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2415_ = lean_array_push(v_decls_2409_, v___x_2414_);
                if v_isShared_2412_ == 0 {
                    leanh::lean_ctor_set(v___x_2411_, 2, v___x_2415_);
                    v___x_2417_ = v___x_2411_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_visited_2407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_params_2408_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 2, v___x_2415_);
                    v___x_2417_ = v_reuseFailAlloc_2423_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2418_ = lean_st_ref_set(v_a_2366_, v___x_2417_);
                v___x_2419_ = leanh::lean_box(0);
                if v_isShared_2405_ == 0 {
                    leanh::lean_ctor_set(v___x_2404_, 0, v___x_2419_);
                    v___x_2421_ = v___x_2404_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2421_;
            }
            10 => {
                v___x_2435_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_2435_, 0, v_fvarId_2397_);
                leanh::lean_ctor_set(v___x_2435_, 1, v_binderName_2398_);
                leanh::lean_ctor_set(v___x_2435_, 2, v_type_2399_);
                leanh::lean_ctor_set_uint8(
                    v___x_2435_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2374_,
                );
                v___x_2436_ = lean_array_push(v_params_2430_, v___x_2435_);
                if v_isShared_2434_ == 0 {
                    leanh::lean_ctor_set(v___x_2433_, 1, v___x_2436_);
                    v___x_2438_ = v___x_2433_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2444_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_visited_2429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2444_, 1, v___x_2436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_decls_2431_);
                    v___x_2438_ = v_reuseFailAlloc_2444_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2439_ = lean_st_ref_set(v_a_2366_, v___x_2438_);
                v___x_2440_ = leanh::lean_box(0);
                if v_isShared_2392_ == 0 {
                    leanh::lean_ctor_set(v___x_2391_, 0, v___x_2440_);
                    v___x_2442_ = v___x_2391_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2443_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
                    v___x_2442_ = v_reuseFailAlloc_2443_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2442_;
            }
            13 => {
                v___x_2455_ = lean_st_ref_take(v_a_2366_);
                v_visited_2456_ = leanh::lean_ctor_get(v___x_2455_, 0);
                v_params_2457_ = leanh::lean_ctor_get(v___x_2455_, 1);
                v_decls_2458_ = leanh::lean_ctor_get(v___x_2455_, 2);
                v_isSharedCheck_2471_ = (!leanh::lean_is_exclusive(v___x_2455_)) as u8;
                if v_isSharedCheck_2471_ == 0 {
                    v___x_2460_ = v___x_2455_;
                    v_isShared_2461_ = v_isSharedCheck_2471_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_decls_2458_);
                    leanh::lean_inc(v_params_2457_);
                    leanh::lean_inc(v_visited_2456_);
                    leanh::lean_dec(v___x_2455_);
                    v___x_2460_ = leanh::lean_box(0);
                    v_isShared_2461_ = v_isSharedCheck_2471_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2462_ = lean_array_push(v_params_2457_, v_val_2449_);
                if v_isShared_2461_ == 0 {
                    leanh::lean_ctor_set(v___x_2460_, 1, v___x_2462_);
                    v___x_2464_ = v___x_2460_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_visited_2456_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_decls_2458_);
                    v___x_2464_ = v_reuseFailAlloc_2470_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2465_ = lean_st_ref_set(v_a_2366_, v___x_2464_);
                v___x_2466_ = leanh::lean_box(0);
                if v_isShared_2454_ == 0 {
                    leanh::lean_ctor_set(v___x_2453_, 0, v___x_2466_);
                    v___x_2468_ = v___x_2453_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
                    v___x_2468_ = v_reuseFailAlloc_2469_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2468_;
            }
            17 => {
                v_fvarId_2480_ = leanh::lean_ctor_get(v_val_2476_, 0);
                v_binderName_2481_ = leanh::lean_ctor_get(v_val_2476_, 1);
                v_type_2482_ = leanh::lean_ctor_get(v_val_2476_, 2);
                v_value_2483_ = leanh::lean_ctor_get(v_val_2476_, 3);
                leanh::lean_inc_ref(v_type_2482_);
                v___x_2484_ = l_Lean_Compiler_LCNF_Closure_collectType(
                    v_type_2482_,
                    v_a_2365_,
                    v_a_2366_,
                    v_a_2367_,
                    v_a_2368_,
                    v_a_2369_,
                    v_a_2370_,
                );
                if leanh::lean_obj_tag(v___x_2484_) == 0 {
                    v_isSharedCheck_2534_ = (!leanh::lean_is_exclusive(v___x_2484_)) as u8;
                    if v_isSharedCheck_2534_ == 0 {
                        v_unused_2535_ = leanh::lean_ctor_get(v___x_2484_, 0);
                        leanh::lean_dec(v_unused_2535_);
                        v___x_2486_ = v___x_2484_;
                        v_isShared_2487_ = v_isSharedCheck_2534_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2484_);
                        v___x_2486_ = leanh::lean_box(0);
                        v_isShared_2487_ = v_isSharedCheck_2534_;
                        state = 18;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2478_);
                    leanh::lean_dec(v_val_2476_);
                    return v___x_2484_;
                }
            }
            18 => {
                leanh::lean_inc_ref(v_abstract_2380_);
                leanh::lean_inc(v_fvarId_2480_);
                v___x_2488_ = leanh::lean_apply_1(v_abstract_2380_, v_fvarId_2480_);
                v___x_2489_ = (leanh::lean_unbox(v___x_2488_) as u8);
                if v___x_2489_ == 0 {
                    leanh::lean_del_object(v___x_2486_);
                    leanh::lean_inc(v_value_2483_);
                    v___x_2490_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(
                        v_value_2483_,
                        v_a_2365_,
                        v_a_2366_,
                        v_a_2367_,
                        v_a_2368_,
                        v_a_2369_,
                        v_a_2370_,
                    );
                    if leanh::lean_obj_tag(v___x_2490_) == 0 {
                        v_isSharedCheck_2514_ =
                            (!leanh::lean_is_exclusive(v___x_2490_)) as u8;
                        if v_isSharedCheck_2514_ == 0 {
                            v_unused_2515_ = leanh::lean_ctor_get(v___x_2490_, 0);
                            leanh::lean_dec(v_unused_2515_);
                            v___x_2492_ = v___x_2490_;
                            v_isShared_2493_ = v_isSharedCheck_2514_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2490_);
                            v___x_2492_ = leanh::lean_box(0);
                            v_isShared_2493_ = v_isSharedCheck_2514_;
                            state = 19;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2478_);
                        leanh::lean_dec(v_val_2476_);
                        return v___x_2490_;
                    }
                } else {
                    leanh::lean_inc_ref(v_type_2482_);
                    leanh::lean_inc(v_binderName_2481_);
                    leanh::lean_inc(v_fvarId_2480_);
                    leanh::lean_del_object(v___x_2478_);
                    leanh::lean_dec(v_val_2476_);
                    v___x_2516_ = lean_st_ref_take(v_a_2366_);
                    v_visited_2517_ = leanh::lean_ctor_get(v___x_2516_, 0);
                    v_params_2518_ = leanh::lean_ctor_get(v___x_2516_, 1);
                    v_decls_2519_ = leanh::lean_ctor_get(v___x_2516_, 2);
                    v_isSharedCheck_2533_ = (!leanh::lean_is_exclusive(v___x_2516_)) as u8;
                    if v_isSharedCheck_2533_ == 0 {
                        v___x_2521_ = v___x_2516_;
                        v_isShared_2522_ = v_isSharedCheck_2533_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_decls_2519_);
                        leanh::lean_inc(v_params_2518_);
                        leanh::lean_inc(v_visited_2517_);
                        leanh::lean_dec(v___x_2516_);
                        v___x_2521_ = leanh::lean_box(0);
                        v_isShared_2522_ = v_isSharedCheck_2533_;
                        state = 24;
                        continue;
                    }
                }
            }
            19 => {
                v___x_2494_ = lean_st_ref_take(v_a_2366_);
                v_visited_2495_ = leanh::lean_ctor_get(v___x_2494_, 0);
                v_params_2496_ = leanh::lean_ctor_get(v___x_2494_, 1);
                v_decls_2497_ = leanh::lean_ctor_get(v___x_2494_, 2);
                v_isSharedCheck_2513_ = (!leanh::lean_is_exclusive(v___x_2494_)) as u8;
                if v_isSharedCheck_2513_ == 0 {
                    v___x_2499_ = v___x_2494_;
                    v_isShared_2500_ = v_isSharedCheck_2513_;
                    state = 20;
                    continue;
                } else {
                    leanh::lean_inc(v_decls_2497_);
                    leanh::lean_inc(v_params_2496_);
                    leanh::lean_inc(v_visited_2495_);
                    leanh::lean_dec(v___x_2494_);
                    v___x_2499_ = leanh::lean_box(0);
                    v_isShared_2500_ = v_isSharedCheck_2513_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2479_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2478_, 0);
                    v___x_2502_ = v___x_2478_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_val_2476_);
                    v___x_2502_ = v_reuseFailAlloc_2512_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2503_ = lean_array_push(v_decls_2497_, v___x_2502_);
                if v_isShared_2500_ == 0 {
                    leanh::lean_ctor_set(v___x_2499_, 2, v___x_2503_);
                    v___x_2505_ = v___x_2499_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_visited_2495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_params_2496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 2, v___x_2503_);
                    v___x_2505_ = v_reuseFailAlloc_2511_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_2506_ = lean_st_ref_set(v_a_2366_, v___x_2505_);
                v___x_2507_ = leanh::lean_box(0);
                if v_isShared_2493_ == 0 {
                    leanh::lean_ctor_set(v___x_2492_, 0, v___x_2507_);
                    v___x_2509_ = v___x_2492_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
                    v___x_2509_ = v_reuseFailAlloc_2510_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2509_;
            }
            24 => {
                v___x_2523_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_2523_, 0, v_fvarId_2480_);
                leanh::lean_ctor_set(v___x_2523_, 1, v_binderName_2481_);
                leanh::lean_ctor_set(v___x_2523_, 2, v_type_2482_);
                leanh::lean_ctor_set_uint8(
                    v___x_2523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2374_,
                );
                v___x_2524_ = lean_array_push(v_params_2518_, v___x_2523_);
                if v_isShared_2522_ == 0 {
                    leanh::lean_ctor_set(v___x_2521_, 1, v___x_2524_);
                    v___x_2526_ = v___x_2521_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_visited_2517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_decls_2519_);
                    v___x_2526_ = v_reuseFailAlloc_2532_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_2527_ = lean_st_ref_set(v_a_2366_, v___x_2526_);
                v___x_2528_ = leanh::lean_box(0);
                if v_isShared_2487_ == 0 {
                    leanh::lean_ctor_set(v___x_2486_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2486_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2531_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2530_;
            }
            27 => {
                if v_isShared_2542_ == 0 {
                    v___x_2544_ = v___x_2541_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
                    v___x_2544_ = v_reuseFailAlloc_2545_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2544_;
            }
            29 => {
                if v_isShared_2550_ == 0 {
                    v___x_2552_ = v___x_2549_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
                    v___x_2552_ = v_reuseFailAlloc_2553_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2552_;
            }
            31 => {
                if v_isShared_2559_ == 0 {
                    v___x_2561_ = v___x_2558_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
                    v___x_2561_ = v_reuseFailAlloc_2562_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectType___lam__0(
    mut v_e_2568_: *mut leanh::LeanObject,
    mut v___y_2569_: *mut leanh::LeanObject,
    mut v___y_2570_: *mut leanh::LeanObject,
    mut v___y_2571_: *mut leanh::LeanObject,
    mut v___y_2572_: *mut leanh::LeanObject,
    mut v___y_2573_: *mut leanh::LeanObject,
    mut v___y_2574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_Expr_fvarId_x21(v_e_2568_);
    v___x_2577_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
        v___x_2576_,
        v___y_2569_,
        v___y_2570_,
        v___y_2571_,
        v___y_2572_,
        v___y_2573_,
        v___y_2574_,
    );
    return v___x_2577_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectArg___boxed(
    mut v_arg_2578_: *mut leanh::LeanObject,
    mut v_a_2579_: *mut leanh::LeanObject,
    mut v_a_2580_: *mut leanh::LeanObject,
    mut v_a_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
    mut v_a_2584_: *mut leanh::LeanObject,
    mut v_a_2585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2586_ = l_Lean_Compiler_LCNF_Closure_collectArg(
        v_arg_2578_,
        v_a_2579_,
        v_a_2580_,
        v_a_2581_,
        v_a_2582_,
        v_a_2583_,
        v_a_2584_,
    );
    leanh::lean_dec(v_a_2584_);
    leanh::lean_dec_ref(v_a_2583_);
    leanh::lean_dec(v_a_2582_);
    leanh::lean_dec_ref(v_a_2581_);
    leanh::lean_dec(v_a_2580_);
    leanh::lean_dec_ref(v_a_2579_);
    return v_res_2586_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectType___boxed(
    mut v_type_2587_: *mut leanh::LeanObject,
    mut v_a_2588_: *mut leanh::LeanObject,
    mut v_a_2589_: *mut leanh::LeanObject,
    mut v_a_2590_: *mut leanh::LeanObject,
    mut v_a_2591_: *mut leanh::LeanObject,
    mut v_a_2592_: *mut leanh::LeanObject,
    mut v_a_2593_: *mut leanh::LeanObject,
    mut v_a_2594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_Lean_Compiler_LCNF_Closure_collectType(
        v_type_2587_,
        v_a_2588_,
        v_a_2589_,
        v_a_2590_,
        v_a_2591_,
        v_a_2592_,
        v_a_2593_,
    );
    leanh::lean_dec(v_a_2593_);
    leanh::lean_dec_ref(v_a_2592_);
    leanh::lean_dec(v_a_2591_);
    leanh::lean_dec_ref(v_a_2590_);
    leanh::lean_dec(v_a_2589_);
    leanh::lean_dec_ref(v_a_2588_);
    return v_res_2595_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(
    mut v_decl_2596_: *mut leanh::LeanObject,
    mut v_a_2597_: *mut leanh::LeanObject,
    mut v_a_2598_: *mut leanh::LeanObject,
    mut v_a_2599_: *mut leanh::LeanObject,
    mut v_a_2600_: *mut leanh::LeanObject,
    mut v_a_2601_: *mut leanh::LeanObject,
    mut v_a_2602_: *mut leanh::LeanObject,
    mut v_a_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(
        v_decl_2596_,
        v_a_2597_,
        v_a_2598_,
        v_a_2599_,
        v_a_2600_,
        v_a_2601_,
        v_a_2602_,
    );
    leanh::lean_dec(v_a_2602_);
    leanh::lean_dec_ref(v_a_2601_);
    leanh::lean_dec(v_a_2600_);
    leanh::lean_dec_ref(v_a_2599_);
    leanh::lean_dec(v_a_2598_);
    leanh::lean_dec_ref(v_a_2597_);
    return v_res_2604_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7___boxed(
    mut v_as_2605_: *mut leanh::LeanObject,
    mut v_i_2606_: *mut leanh::LeanObject,
    mut v_stop_2607_: *mut leanh::LeanObject,
    mut v_b_2608_: *mut leanh::LeanObject,
    mut v___y_2609_: *mut leanh::LeanObject,
    mut v___y_2610_: *mut leanh::LeanObject,
    mut v___y_2611_: *mut leanh::LeanObject,
    mut v___y_2612_: *mut leanh::LeanObject,
    mut v___y_2613_: *mut leanh::LeanObject,
    mut v___y_2614_: *mut leanh::LeanObject,
    mut v___y_2615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2616_: usize = 0;
    let mut v_stop_boxed_2617_: usize = 0;
    let mut v_res_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2616_ = leanh::lean_unbox_usize(v_i_2606_);
    leanh::lean_dec(v_i_2606_);
    v_stop_boxed_2617_ = leanh::lean_unbox_usize(v_stop_2607_);
    leanh::lean_dec(v_stop_2607_);
    v_res_2618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_as_2605_, v_i_boxed_2616_, v_stop_boxed_2617_, v_b_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
    leanh::lean_dec(v___y_2614_);
    leanh::lean_dec_ref(v___y_2613_);
    leanh::lean_dec(v___y_2612_);
    leanh::lean_dec_ref(v___y_2611_);
    leanh::lean_dec(v___y_2610_);
    leanh::lean_dec_ref(v___y_2609_);
    leanh::lean_dec_ref(v_as_2605_);
    return v_res_2618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0___boxed(
    mut v_as_2619_: *mut leanh::LeanObject,
    mut v_i_2620_: *mut leanh::LeanObject,
    mut v_stop_2621_: *mut leanh::LeanObject,
    mut v_b_2622_: *mut leanh::LeanObject,
    mut v___y_2623_: *mut leanh::LeanObject,
    mut v___y_2624_: *mut leanh::LeanObject,
    mut v___y_2625_: *mut leanh::LeanObject,
    mut v___y_2626_: *mut leanh::LeanObject,
    mut v___y_2627_: *mut leanh::LeanObject,
    mut v___y_2628_: *mut leanh::LeanObject,
    mut v___y_2629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2630_: usize = 0;
    let mut v_stop_boxed_2631_: usize = 0;
    let mut v_res_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2630_ = leanh::lean_unbox_usize(v_i_2620_);
    leanh::lean_dec(v_i_2620_);
    v_stop_boxed_2631_ = leanh::lean_unbox_usize(v_stop_2621_);
    leanh::lean_dec(v_stop_2621_);
    v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_as_2619_, v_i_boxed_2630_, v_stop_boxed_2631_, v_b_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
    leanh::lean_dec(v___y_2628_);
    leanh::lean_dec_ref(v___y_2627_);
    leanh::lean_dec(v___y_2626_);
    leanh::lean_dec_ref(v___y_2625_);
    leanh::lean_dec(v___y_2624_);
    leanh::lean_dec_ref(v___y_2623_);
    leanh::lean_dec_ref(v_as_2619_);
    return v_res_2632_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectParams___boxed(
    mut v_params_2633_: *mut leanh::LeanObject,
    mut v_a_2634_: *mut leanh::LeanObject,
    mut v_a_2635_: *mut leanh::LeanObject,
    mut v_a_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v_a_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2641_ = l_Lean_Compiler_LCNF_Closure_collectParams(
        v_params_2633_,
        v_a_2634_,
        v_a_2635_,
        v_a_2636_,
        v_a_2637_,
        v_a_2638_,
        v_a_2639_,
    );
    leanh::lean_dec(v_a_2639_);
    leanh::lean_dec_ref(v_a_2638_);
    leanh::lean_dec(v_a_2637_);
    leanh::lean_dec_ref(v_a_2636_);
    leanh::lean_dec(v_a_2635_);
    leanh::lean_dec_ref(v_a_2634_);
    leanh::lean_dec_ref(v_params_2633_);
    return v_res_2641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11___boxed(
    mut v_as_2642_: *mut leanh::LeanObject,
    mut v_i_2643_: *mut leanh::LeanObject,
    mut v_stop_2644_: *mut leanh::LeanObject,
    mut v_b_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
    mut v___y_2650_: *mut leanh::LeanObject,
    mut v___y_2651_: *mut leanh::LeanObject,
    mut v___y_2652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2653_: usize = 0;
    let mut v_stop_boxed_2654_: usize = 0;
    let mut v_res_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2653_ = leanh::lean_unbox_usize(v_i_2643_);
    leanh::lean_dec(v_i_2643_);
    v_stop_boxed_2654_ = leanh::lean_unbox_usize(v_stop_2644_);
    leanh::lean_dec(v_stop_2644_);
    v_res_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_as_2642_, v_i_boxed_2653_, v_stop_boxed_2654_, v_b_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
    leanh::lean_dec(v___y_2651_);
    leanh::lean_dec_ref(v___y_2650_);
    leanh::lean_dec(v___y_2649_);
    leanh::lean_dec_ref(v___y_2648_);
    leanh::lean_dec(v___y_2647_);
    leanh::lean_dec_ref(v___y_2646_);
    leanh::lean_dec_ref(v_as_2642_);
    return v_res_2655_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectLetValue___boxed(
    mut v_e_2656_: *mut leanh::LeanObject,
    mut v_a_2657_: *mut leanh::LeanObject,
    mut v_a_2658_: *mut leanh::LeanObject,
    mut v_a_2659_: *mut leanh::LeanObject,
    mut v_a_2660_: *mut leanh::LeanObject,
    mut v_a_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
    mut v_a_2663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(
        v_e_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_,
    );
    leanh::lean_dec(v_a_2662_);
    leanh::lean_dec_ref(v_a_2661_);
    leanh::lean_dec(v_a_2660_);
    leanh::lean_dec_ref(v_a_2659_);
    leanh::lean_dec(v_a_2658_);
    leanh::lean_dec_ref(v_a_2657_);
    return v_res_2664_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectCode___boxed(
    mut v_c_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_a_2668_: *mut leanh::LeanObject,
    mut v_a_2669_: *mut leanh::LeanObject,
    mut v_a_2670_: *mut leanh::LeanObject,
    mut v_a_2671_: *mut leanh::LeanObject,
    mut v_a_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Compiler_LCNF_Closure_collectCode(
        v_c_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_,
    );
    leanh::lean_dec(v_a_2671_);
    leanh::lean_dec_ref(v_a_2670_);
    leanh::lean_dec(v_a_2669_);
    leanh::lean_dec_ref(v_a_2668_);
    leanh::lean_dec(v_a_2667_);
    leanh::lean_dec_ref(v_a_2666_);
    return v_res_2673_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectFVar___boxed(
    mut v_fvarId_2674_: *mut leanh::LeanObject,
    mut v_a_2675_: *mut leanh::LeanObject,
    mut v_a_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
    mut v_a_2679_: *mut leanh::LeanObject,
    mut v_a_2680_: *mut leanh::LeanObject,
    mut v_a_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2682_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
        v_fvarId_2674_,
        v_a_2675_,
        v_a_2676_,
        v_a_2677_,
        v_a_2678_,
        v_a_2679_,
        v_a_2680_,
    );
    leanh::lean_dec(v_a_2680_);
    leanh::lean_dec_ref(v_a_2679_);
    leanh::lean_dec(v_a_2678_);
    leanh::lean_dec_ref(v_a_2677_);
    leanh::lean_dec(v_a_2676_);
    leanh::lean_dec_ref(v_a_2675_);
    return v_res_2682_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(
    mut v_00_u03b2_2683_: *mut leanh::LeanObject,
    mut v_m_2684_: *mut leanh::LeanObject,
    mut v_a_2685_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2686_: u8 = 0;
    v___x_2686_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_2684_, v_a_2685_);
    return v___x_2686_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___boxed(
    mut v_00_u03b2_2687_: *mut leanh::LeanObject,
    mut v_m_2688_: *mut leanh::LeanObject,
    mut v_a_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2690_: u8 = 0;
    let mut v_r_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(v_00_u03b2_2687_, v_m_2688_, v_a_2689_);
    leanh::lean_dec(v_a_2689_);
    leanh::lean_dec_ref(v_m_2688_);
    v_r_2691_ = leanh::lean_box((v_res_2690_) as usize);
    return v_r_2691_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(
    mut v_e_2692_: *mut leanh::LeanObject,
    mut v_a_2693_: *mut leanh::LeanObject,
    mut v___y_2694_: *mut leanh::LeanObject,
    mut v___y_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_2692_, v_a_2693_);
    return v___x_2701_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___boxed(
    mut v_e_2702_: *mut leanh::LeanObject,
    mut v_a_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
    mut v___y_2708_: *mut leanh::LeanObject,
    mut v___y_2709_: *mut leanh::LeanObject,
    mut v___y_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2711_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(v_e_2702_, v_a_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
    leanh::lean_dec(v___y_2709_);
    leanh::lean_dec_ref(v___y_2708_);
    leanh::lean_dec(v___y_2707_);
    leanh::lean_dec_ref(v___y_2706_);
    leanh::lean_dec(v___y_2705_);
    leanh::lean_dec_ref(v___y_2704_);
    leanh::lean_dec(v_a_2703_);
    return v_res_2711_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(
    mut v_e_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v___y_2714_: *mut leanh::LeanObject,
    mut v___y_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_2712_, v_a_2713_);
    return v___x_2721_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___boxed(
    mut v_e_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v___y_2724_: *mut leanh::LeanObject,
    mut v___y_2725_: *mut leanh::LeanObject,
    mut v___y_2726_: *mut leanh::LeanObject,
    mut v___y_2727_: *mut leanh::LeanObject,
    mut v___y_2728_: *mut leanh::LeanObject,
    mut v___y_2729_: *mut leanh::LeanObject,
    mut v___y_2730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(v_e_2722_, v_a_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
    leanh::lean_dec(v___y_2729_);
    leanh::lean_dec_ref(v___y_2728_);
    leanh::lean_dec(v___y_2727_);
    leanh::lean_dec_ref(v___y_2726_);
    leanh::lean_dec(v___y_2725_);
    leanh::lean_dec_ref(v___y_2724_);
    leanh::lean_dec(v_a_2723_);
    return v_res_2731_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(
    mut v_00_u03b2_2732_: *mut leanh::LeanObject,
    mut v_m_2733_: *mut leanh::LeanObject,
    mut v_a_2734_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2735_: u8 = 0;
    v___x_2735_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_2733_, v_a_2734_);
    return v___x_2735_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___boxed(
    mut v_00_u03b2_2736_: *mut leanh::LeanObject,
    mut v_m_2737_: *mut leanh::LeanObject,
    mut v_a_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2739_: u8 = 0;
    let mut v_r_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(v_00_u03b2_2736_, v_m_2737_, v_a_2738_);
    leanh::lean_dec_ref(v_a_2738_);
    leanh::lean_dec_ref(v_m_2737_);
    v_r_2740_ = leanh::lean_box((v_res_2739_) as usize);
    return v_r_2740_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15(
    mut v_00_u03b2_2741_: *mut leanh::LeanObject,
    mut v_m_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_b_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_m_2742_, v_a_2743_, v_b_2744_);
    return v___x_2745_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(
    mut v_00_u03b2_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
    mut v_x_2748_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2749_: u8 = 0;
    v___x_2749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_2747_, v_x_2748_);
    return v___x_2749_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___boxed(
    mut v_00_u03b2_2750_: *mut leanh::LeanObject,
    mut v_a_2751_: *mut leanh::LeanObject,
    mut v_x_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2753_: u8 = 0;
    let mut v_r_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2753_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(v_00_u03b2_2750_, v_a_2751_, v_x_2752_);
    leanh::lean_dec(v_x_2752_);
    leanh::lean_dec_ref(v_a_2751_);
    v_r_2754_ = leanh::lean_box((v_res_2753_) as usize);
    return v_r_2754_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17(
    mut v_00_u03b2_2755_: *mut leanh::LeanObject,
    mut v_data_2756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2757_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_data_2756_);
    return v___x_2757_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18(
    mut v_00_u03b2_2758_: *mut leanh::LeanObject,
    mut v_i_2759_: *mut leanh::LeanObject,
    mut v_source_2760_: *mut leanh::LeanObject,
    mut v_target_2761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2762_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v_i_2759_, v_source_2760_, v_target_2761_);
    return v___x_2762_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19(
    mut v_00_u03b2_2763_: *mut leanh::LeanObject,
    mut v_x_2764_: *mut leanh::LeanObject,
    mut v_x_2765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_x_2764_, v_x_2765_);
    return v___x_2766_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(
    mut v_k_2767_: *mut leanh::LeanObject,
    mut v_t_2768_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2774_: u8 = 0;
    let mut v___x_2776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2768_) == 0 {
                    v_k_2769_ = leanh::lean_ctor_get(v_t_2768_, 1);
                    v_l_2770_ = leanh::lean_ctor_get(v_t_2768_, 3);
                    v_r_2771_ = leanh::lean_ctor_get(v_t_2768_, 4);
                    v___x_2772_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2767_, v_k_2769_);
                    match v___x_2772_ {
                        0 => {
                            v_t_2768_ = v_l_2770_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2774_ = 1;
                            return v___x_2774_;
                        }
                        _ => {
                            v_t_2768_ = v_r_2771_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2776_ = 0;
                    return v___x_2776_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg___boxed(
    mut v_k_2777_: *mut leanh::LeanObject,
    mut v_t_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2779_: u8 = 0;
    let mut v_r_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2779_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_2777_, v_t_2778_);
    leanh::lean_dec(v_t_2778_);
    leanh::lean_dec(v_k_2777_);
    v_r_2780_ = leanh::lean_box((v_res_2779_) as usize);
    return v_r_2780_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_as_2782_: *mut leanh::LeanObject,
    mut v_i_2783_: usize,
    mut v_stop_2784_: usize,
    mut v_b_2785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: usize = 0;
    let mut v___x_2789_: usize = 0;
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2791_ = lean_usize_dec_eq(v_i_2783_, v_stop_2784_);
                if v___x_2791_ == 0 {
                    v___x_2792_ = lean_array_uget_borrowed(v_as_2782_, v_i_2783_);
                    v___x_2793_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_2792_);
                    v___x_2794_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v___x_2793_, v_a_2781_);
                    leanh::lean_dec(v___x_2793_);
                    if v___x_2794_ == 0 {
                        leanh::lean_inc(v___x_2792_);
                        v___x_2795_ = lean_array_push(v_b_2785_, v___x_2792_);
                        v___y_2787_ = v___x_2795_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2787_ = v_b_2785_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2785_;
                }
            }
            1 => {
                v___x_2788_ = 1usize;
                v___x_2789_ = lean_usize_add(v_i_2783_, v___x_2788_);
                v_i_2783_ = v___x_2789_;
                v_b_2785_ = v___y_2787_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2___boxed(
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v_as_2797_: *mut leanh::LeanObject,
    mut v_i_2798_: *mut leanh::LeanObject,
    mut v_stop_2799_: *mut leanh::LeanObject,
    mut v_b_2800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2801_: usize = 0;
    let mut v_stop_boxed_2802_: usize = 0;
    let mut v_res_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2801_ = leanh::lean_unbox_usize(v_i_2798_);
    leanh::lean_dec(v_i_2798_);
    v_stop_boxed_2802_ = leanh::lean_unbox_usize(v_stop_2799_);
    leanh::lean_dec(v_stop_2799_);
    v_res_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_2796_, v_as_2797_, v_i_boxed_2801_, v_stop_boxed_2802_, v_b_2800_);
    leanh::lean_dec_ref(v_as_2797_);
    leanh::lean_dec(v_a_2796_);
    return v_res_2803_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(
    mut v_as_2804_: *mut leanh::LeanObject,
    mut v_sz_2805_: usize,
    mut v_i_2806_: usize,
    mut v_b_2807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: usize = 0;
    let mut v___x_2815_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2809_ = lean_usize_dec_lt(v_i_2806_, v_sz_2805_);
                if v___x_2809_ == 0 {
                    v___x_2810_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2810_, 0, v_b_2807_);
                    return v___x_2810_;
                } else {
                    v_a_2811_ = lean_array_uget_borrowed(v_as_2804_, v_i_2806_);
                    v_fvarId_2812_ = leanh::lean_ctor_get(v_a_2811_, 0);
                    leanh::lean_inc(v_fvarId_2812_);
                    v___x_2813_ = l_Lean_FVarIdSet_insert(v_b_2807_, v_fvarId_2812_);
                    v___x_2814_ = 1usize;
                    v___x_2815_ = lean_usize_add(v_i_2806_, v___x_2814_);
                    v_i_2806_ = v___x_2815_;
                    v_b_2807_ = v___x_2813_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg___boxed(
    mut v_as_2817_: *mut leanh::LeanObject,
    mut v_sz_2818_: *mut leanh::LeanObject,
    mut v_i_2819_: *mut leanh::LeanObject,
    mut v_b_2820_: *mut leanh::LeanObject,
    mut v___y_2821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2822_: usize = 0;
    let mut v_i_boxed_2823_: usize = 0;
    let mut v_res_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2822_ = leanh::lean_unbox_usize(v_sz_2818_);
    leanh::lean_dec(v_sz_2818_);
    v_i_boxed_2823_ = leanh::lean_unbox_usize(v_i_2819_);
    leanh::lean_dec(v_i_2819_);
    v_res_2824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_2817_, v_sz_boxed_2822_, v_i_boxed_2823_, v_b_2820_);
    leanh::lean_dec_ref(v_as_2817_);
    return v_res_2824_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0;
    v___x_2828_ = l_Lean_instEmptyCollectionFVarIdHashSet;
    v___x_2829_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2829_, 0, v___x_2828_);
    leanh::lean_ctor_set(v___x_2829_, 1, v___x_2827_);
    leanh::lean_ctor_set(v___x_2829_, 2, v___x_2827_);
    return v___x_2829_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_run___redArg(
    mut v_x_2830_: *mut leanh::LeanObject,
    mut v_inScope_2831_: *mut leanh::LeanObject,
    mut v_abstract_2832_: *mut leanh::LeanObject,
    mut v_a_2833_: *mut leanh::LeanObject,
    mut v_a_2834_: *mut leanh::LeanObject,
    mut v_a_2835_: *mut leanh::LeanObject,
    mut v_a_2836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2849_: usize = 0;
    let mut v___x_2850_: usize = 0;
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___y_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: usize = 0;
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v_a_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2838_ = leanh::lean_unsigned_to_nat(0);
                v___x_2839_ = l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0;
                v___x_2840_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1,
                );
                v___x_2841_ = lean_st_mk_ref(v___x_2840_);
                v___x_2842_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2842_, 0, v_inScope_2831_);
                leanh::lean_ctor_set(v___x_2842_, 1, v_abstract_2832_);
                leanh::lean_inc(v_a_2836_);
                leanh::lean_inc_ref(v_a_2835_);
                leanh::lean_inc(v_a_2834_);
                leanh::lean_inc_ref(v_a_2833_);
                leanh::lean_inc(v___x_2841_);
                v___x_2843_ = leanh::lean_apply_7(
                    v_x_2830_,
                    v___x_2842_,
                    v___x_2841_,
                    v_a_2833_,
                    v_a_2834_,
                    v_a_2835_,
                    v_a_2836_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2843_) == 0 {
                    v_a_2844_ = leanh::lean_ctor_get(v___x_2843_, 0);
                    leanh::lean_inc(v_a_2844_);
                    leanh::lean_dec_ref_known(v___x_2843_, 1);
                    v___x_2845_ = lean_st_ref_get(v___x_2841_);
                    leanh::lean_dec(v___x_2841_);
                    v_params_2846_ = leanh::lean_ctor_get(v___x_2845_, 1);
                    leanh::lean_inc_ref(v_params_2846_);
                    v_decls_2847_ = leanh::lean_ctor_get(v___x_2845_, 2);
                    leanh::lean_inc_ref(v_decls_2847_);
                    leanh::lean_dec(v___x_2845_);
                    v___x_2848_ = leanh::lean_box(1);
                    v_sz_2849_ = lean_array_size(v_params_2846_);
                    v___x_2850_ = 0usize;
                    v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_params_2846_, v_sz_2849_, v___x_2850_, v___x_2848_);
                    if leanh::lean_obj_tag(v___x_2851_) == 0 {
                        v_a_2852_ = leanh::lean_ctor_get(v___x_2851_, 0);
                        v_isSharedCheck_2870_ =
                            (!leanh::lean_is_exclusive(v___x_2851_)) as u8;
                        if v_isSharedCheck_2870_ == 0 {
                            v___x_2854_ = v___x_2851_;
                            v_isShared_2855_ = v_isSharedCheck_2870_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2852_);
                            leanh::lean_dec(v___x_2851_);
                            v___x_2854_ = leanh::lean_box(0);
                            v_isShared_2855_ = v_isSharedCheck_2870_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_decls_2847_);
                        leanh::lean_dec_ref(v_params_2846_);
                        leanh::lean_dec(v_a_2844_);
                        v_a_2871_ = leanh::lean_ctor_get(v___x_2851_, 0);
                        v_isSharedCheck_2878_ =
                            (!leanh::lean_is_exclusive(v___x_2851_)) as u8;
                        if v_isSharedCheck_2878_ == 0 {
                            v___x_2873_ = v___x_2851_;
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2871_);
                            leanh::lean_dec(v___x_2851_);
                            v___x_2873_ = leanh::lean_box(0);
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2841_);
                    v_a_2879_ = leanh::lean_ctor_get(v___x_2843_, 0);
                    v_isSharedCheck_2886_ = (!leanh::lean_is_exclusive(v___x_2843_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2881_ = v___x_2843_;
                        v_isShared_2882_ = v_isSharedCheck_2886_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2879_);
                        leanh::lean_dec(v___x_2843_);
                        v___x_2881_ = leanh::lean_box(0);
                        v_isShared_2882_ = v_isSharedCheck_2886_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2863_ = lean_array_get_size(v_decls_2847_);
                v___x_2864_ = lean_nat_dec_lt(v___x_2838_, v___x_2863_);
                if v___x_2864_ == 0 {
                    leanh::lean_dec(v_a_2852_);
                    leanh::lean_dec_ref(v_decls_2847_);
                    v___y_2857_ = v___x_2839_;
                    state = 2;
                    continue;
                } else {
                    v___x_2865_ = lean_nat_dec_le(v___x_2863_, v___x_2863_);
                    if v___x_2865_ == 0 {
                        if v___x_2864_ == 0 {
                            leanh::lean_dec(v_a_2852_);
                            leanh::lean_dec_ref(v_decls_2847_);
                            v___y_2857_ = v___x_2839_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2866_ = lean_usize_of_nat(v___x_2863_);
                            v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_2852_, v_decls_2847_, v___x_2850_, v___x_2866_, v___x_2839_);
                            leanh::lean_dec_ref(v_decls_2847_);
                            leanh::lean_dec(v_a_2852_);
                            v___y_2857_ = v___x_2867_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2868_ = lean_usize_of_nat(v___x_2863_);
                        v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_2852_, v_decls_2847_, v___x_2850_, v___x_2868_, v___x_2839_);
                        leanh::lean_dec_ref(v_decls_2847_);
                        leanh::lean_dec(v_a_2852_);
                        v___y_2857_ = v___x_2869_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2858_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2858_, 0, v_params_2846_);
                leanh::lean_ctor_set(v___x_2858_, 1, v___y_2857_);
                v___x_2859_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2859_, 0, v_a_2844_);
                leanh::lean_ctor_set(v___x_2859_, 1, v___x_2858_);
                if v_isShared_2855_ == 0 {
                    leanh::lean_ctor_set(v___x_2854_, 0, v___x_2859_);
                    v___x_2861_ = v___x_2854_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2861_;
            }
            4 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2876_;
            }
            6 => {
                if v_isShared_2882_ == 0 {
                    v___x_2884_ = v___x_2881_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
                    v___x_2884_ = v_reuseFailAlloc_2885_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_run___redArg___boxed(
    mut v_x_2887_: *mut leanh::LeanObject,
    mut v_inScope_2888_: *mut leanh::LeanObject,
    mut v_abstract_2889_: *mut leanh::LeanObject,
    mut v_a_2890_: *mut leanh::LeanObject,
    mut v_a_2891_: *mut leanh::LeanObject,
    mut v_a_2892_: *mut leanh::LeanObject,
    mut v_a_2893_: *mut leanh::LeanObject,
    mut v_a_2894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Lean_Compiler_LCNF_Closure_run___redArg(
        v_x_2887_,
        v_inScope_2888_,
        v_abstract_2889_,
        v_a_2890_,
        v_a_2891_,
        v_a_2892_,
        v_a_2893_,
    );
    leanh::lean_dec(v_a_2893_);
    leanh::lean_dec_ref(v_a_2892_);
    leanh::lean_dec(v_a_2891_);
    leanh::lean_dec_ref(v_a_2890_);
    return v_res_2895_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_run(
    mut v_00_u03b1_2896_: *mut leanh::LeanObject,
    mut v_x_2897_: *mut leanh::LeanObject,
    mut v_inScope_2898_: *mut leanh::LeanObject,
    mut v_abstract_2899_: *mut leanh::LeanObject,
    mut v_a_2900_: *mut leanh::LeanObject,
    mut v_a_2901_: *mut leanh::LeanObject,
    mut v_a_2902_: *mut leanh::LeanObject,
    mut v_a_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2905_ = l_Lean_Compiler_LCNF_Closure_run___redArg(
        v_x_2897_,
        v_inScope_2898_,
        v_abstract_2899_,
        v_a_2900_,
        v_a_2901_,
        v_a_2902_,
        v_a_2903_,
    );
    return v___x_2905_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_run___boxed(
    mut v_00_u03b1_2906_: *mut leanh::LeanObject,
    mut v_x_2907_: *mut leanh::LeanObject,
    mut v_inScope_2908_: *mut leanh::LeanObject,
    mut v_abstract_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
    mut v_a_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Lean_Compiler_LCNF_Closure_run(
        v_00_u03b1_2906_,
        v_x_2907_,
        v_inScope_2908_,
        v_abstract_2909_,
        v_a_2910_,
        v_a_2911_,
        v_a_2912_,
        v_a_2913_,
    );
    leanh::lean_dec(v_a_2913_);
    leanh::lean_dec_ref(v_a_2912_);
    leanh::lean_dec(v_a_2911_);
    leanh::lean_dec_ref(v_a_2910_);
    return v_res_2915_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(
    mut v_as_2916_: *mut leanh::LeanObject,
    mut v_sz_2917_: usize,
    mut v_i_2918_: usize,
    mut v_b_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_2916_, v_sz_2917_, v_i_2918_, v_b_2919_);
    return v___x_2925_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___boxed(
    mut v_as_2926_: *mut leanh::LeanObject,
    mut v_sz_2927_: *mut leanh::LeanObject,
    mut v_i_2928_: *mut leanh::LeanObject,
    mut v_b_2929_: *mut leanh::LeanObject,
    mut v___y_2930_: *mut leanh::LeanObject,
    mut v___y_2931_: *mut leanh::LeanObject,
    mut v___y_2932_: *mut leanh::LeanObject,
    mut v___y_2933_: *mut leanh::LeanObject,
    mut v___y_2934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2935_: usize = 0;
    let mut v_i_boxed_2936_: usize = 0;
    let mut v_res_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2935_ = leanh::lean_unbox_usize(v_sz_2927_);
    leanh::lean_dec(v_sz_2927_);
    v_i_boxed_2936_ = leanh::lean_unbox_usize(v_i_2928_);
    leanh::lean_dec(v_i_2928_);
    v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(v_as_2926_, v_sz_boxed_2935_, v_i_boxed_2936_, v_b_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
    leanh::lean_dec(v___y_2933_);
    leanh::lean_dec_ref(v___y_2932_);
    leanh::lean_dec(v___y_2931_);
    leanh::lean_dec_ref(v___y_2930_);
    leanh::lean_dec_ref(v_as_2926_);
    return v_res_2937_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(
    mut v_00_u03b2_2938_: *mut leanh::LeanObject,
    mut v_k_2939_: *mut leanh::LeanObject,
    mut v_t_2940_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2941_: u8 = 0;
    v___x_2941_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_2939_, v_t_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___boxed(
    mut v_00_u03b2_2942_: *mut leanh::LeanObject,
    mut v_k_2943_: *mut leanh::LeanObject,
    mut v_t_2944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2945_: u8 = 0;
    let mut v_r_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(
            v_00_u03b2_2942_,
            v_k_2943_,
            v_t_2944_,
        );
    leanh::lean_dec(v_t_2944_);
    leanh::lean_dec(v_k_2943_);
    v_r_2946_ = leanh::lean_box((v_res_2945_) as usize);
    return v_r_2946_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Closure(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Closure(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Closure(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ForEachExprWhere(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Closure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Closure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Closure(builtin);
}
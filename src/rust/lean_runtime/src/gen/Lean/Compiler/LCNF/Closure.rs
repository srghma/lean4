// Lean compiler output
// Module: Lean.Compiler.LCNF.Closure
// Imports: Lean.Util.ForEachExprWhere Lean.Compiler.LCNF.CompilerM
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land, lean_usize_mod,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_7, lean_apply_8, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4_value
) as *mut LeanObject;
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0: usize = 0;
pub static l_Lean_Compiler_LCNF_Closure_collectType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_isFVar___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_Closure_collectType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectType___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            67, 108, 111, 115, 117, 114, 101, 46, 99, 111, 108, 108, 101, 99, 116, 70, 86, 97, 114,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            67, 108, 111, 115, 117, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1474_: *mut LeanObject,
    mut v_x_1475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1475_) == 0 {
                    return v_x_1474_;
                } else {
                    v_key_1476_ = lean_ctor_get(v_x_1475_, 0);
                    v_value_1477_ = lean_ctor_get(v_x_1475_, 1);
                    v_tail_1478_ = lean_ctor_get(v_x_1475_, 2);
                    v_isSharedCheck_1501_ = (!lean_is_exclusive(v_x_1475_)) as u8;
                    if v_isSharedCheck_1501_ == 0 {
                        v___x_1480_ = v_x_1475_;
                        v_isShared_1481_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1478_);
                        lean_inc(v_value_1477_);
                        lean_inc(v_key_1476_);
                        lean_dec(v_x_1475_);
                        v___x_1480_ = lean_box(0);
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
                lean_inc(v___x_1495_);
                if v_isShared_1481_ == 0 {
                    lean_ctor_set(v___x_1480_, 2, v___x_1495_);
                    v___x_1497_ = v___x_1480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_key_1476_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_value_1477_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 2, v___x_1495_);
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
    mut v_i_1502_: *mut LeanObject,
    mut v_source_1503_: *mut LeanObject,
    mut v_target_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v_es_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1505_ = lean_array_get_size(v_source_1503_);
                v___x_1506_ = lean_nat_dec_lt(v_i_1502_, v___x_1505_);
                if v___x_1506_ == 0 {
                    lean_dec_ref(v_source_1503_);
                    lean_dec(v_i_1502_);
                    return v_target_1504_;
                } else {
                    v_es_1507_ = lean_array_fget(v_source_1503_, v_i_1502_);
                    v___x_1508_ = lean_box(0);
                    v_source_1509_ = lean_array_fset(v_source_1503_, v_i_1502_, v___x_1508_);
                    v_target_1510_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1504_, v_es_1507_);
                    v___x_1511_ = lean_unsigned_to_nat(1);
                    v___x_1512_ = lean_nat_add(v_i_1502_, v___x_1511_);
                    lean_dec(v_i_1502_);
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
    mut v_data_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    v___x_1515_ = lean_array_get_size(v_data_1514_);
    v___x_1516_ = lean_unsigned_to_nat(2);
    v_nbuckets_1517_ = lean_nat_mul(v___x_1515_, v___x_1516_);
    v___x_1518_ = lean_unsigned_to_nat(0);
    v___x_1519_ = lean_box(0);
    v___x_1520_ = lean_mk_array(v_nbuckets_1517_, v___x_1519_);
    v___x_1521_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(v___x_1518_, v_data_1514_, v___x_1520_);
    return v___x_1521_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(
    mut v_a_1522_: *mut LeanObject,
    mut v_x_1523_: *mut LeanObject,
) -> u8 {
    let mut v___x_1524_: u8 = 0;
    let mut v_key_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1523_) == 0 {
                    v___x_1524_ = 0;
                    return v___x_1524_;
                } else {
                    v_key_1525_ = lean_ctor_get(v_x_1523_, 0);
                    v_tail_1526_ = lean_ctor_get(v_x_1523_, 2);
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
    mut v_a_1529_: *mut LeanObject,
    mut v_x_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1531_: u8 = 0;
    let mut v_r_1532_: *mut LeanObject = core::ptr::null_mut();
    v_res_1531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_1529_, v_x_1530_);
    lean_dec(v_x_1530_);
    lean_dec(v_a_1529_);
    v_r_1532_ = lean_box((v_res_1531_) as usize);
    return v_r_1532_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(
    mut v_m_1533_: *mut LeanObject,
    mut v_a_1534_: *mut LeanObject,
    mut v_b_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v_val_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut v_unused_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1536_ = lean_ctor_get(v_m_1533_, 0);
                v_buckets_1537_ = lean_ctor_get(v_m_1533_, 1);
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
                    lean_inc_ref(v_buckets_1537_);
                    lean_inc(v_size_1536_);
                    v_isSharedCheck_1573_ = (!lean_is_exclusive(v_m_1533_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v_unused_1574_ = lean_ctor_get(v_m_1533_, 1);
                        lean_dec(v_unused_1574_);
                        v_unused_1575_ = lean_ctor_get(v_m_1533_, 0);
                        lean_dec(v_unused_1575_);
                        v___x_1554_ = v_m_1533_;
                        v_isShared_1555_ = v_isSharedCheck_1573_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1533_);
                        v___x_1554_ = lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1573_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1535_);
                    lean_dec(v_a_1534_);
                    return v_m_1533_;
                }
            }
            1 => {
                v___x_1556_ = lean_unsigned_to_nat(1);
                v_size_x27_1557_ = lean_nat_add(v_size_1536_, v___x_1556_);
                lean_dec(v_size_1536_);
                lean_inc(v_bkt_1551_);
                v___x_1558_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1558_, 0, v_a_1534_);
                lean_ctor_set(v___x_1558_, 1, v_b_1535_);
                lean_ctor_set(v___x_1558_, 2, v_bkt_1551_);
                v_buckets_x27_1559_ = lean_array_uset(v_buckets_1537_, v___x_1550_, v___x_1558_);
                v___x_1560_ = lean_unsigned_to_nat(4);
                v___x_1561_ = lean_nat_mul(v_size_x27_1557_, v___x_1560_);
                v___x_1562_ = lean_unsigned_to_nat(3);
                v___x_1563_ = lean_nat_div(v___x_1561_, v___x_1562_);
                lean_dec(v___x_1561_);
                v___x_1564_ = lean_array_get_size(v_buckets_x27_1559_);
                v___x_1565_ = lean_nat_dec_le(v___x_1563_, v___x_1564_);
                lean_dec(v___x_1563_);
                if v___x_1565_ == 0 {
                    v_val_1566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_buckets_x27_1559_);
                    if v_isShared_1555_ == 0 {
                        lean_ctor_set(v___x_1554_, 1, v_val_1566_);
                        lean_ctor_set(v___x_1554_, 0, v_size_x27_1557_);
                        v___x_1568_ = v___x_1554_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_size_x27_1557_);
                        lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_val_1566_);
                        v___x_1568_ = v_reuseFailAlloc_1569_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1555_ == 0 {
                        lean_ctor_set(v___x_1554_, 1, v_buckets_x27_1559_);
                        lean_ctor_set(v___x_1554_, 0, v_size_x27_1557_);
                        v___x_1571_ = v___x_1554_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_size_x27_1557_);
                        lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_buckets_x27_1559_);
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
    mut v_fvarId_1576_: *mut LeanObject,
    mut v_a_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1579_ = lean_st_ref_take(v_a_1577_);
                v_visited_1580_ = lean_ctor_get(v___x_1579_, 0);
                v_params_1581_ = lean_ctor_get(v___x_1579_, 1);
                v_decls_1582_ = lean_ctor_get(v___x_1579_, 2);
                v_isSharedCheck_1593_ = (!lean_is_exclusive(v___x_1579_)) as u8;
                if v_isSharedCheck_1593_ == 0 {
                    v___x_1584_ = v___x_1579_;
                    v_isShared_1585_ = v_isSharedCheck_1593_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_decls_1582_);
                    lean_inc(v_params_1581_);
                    lean_inc(v_visited_1580_);
                    lean_dec(v___x_1579_);
                    v___x_1584_ = lean_box(0);
                    v_isShared_1585_ = v_isSharedCheck_1593_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1586_ = lean_box(0);
                v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_visited_1580_, v_fvarId_1576_, v___x_1586_);
                if v_isShared_1585_ == 0 {
                    lean_ctor_set(v___x_1584_, 0, v___x_1587_);
                    v___x_1589_ = v___x_1584_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1587_);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_params_1581_);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_decls_1582_);
                    v___x_1589_ = v_reuseFailAlloc_1592_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1590_ = lean_st_ref_set(v_a_1577_, v___x_1589_);
                v___x_1591_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1591_, 0, v___x_1586_);
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_markVisited___redArg___boxed(
    mut v_fvarId_1594_: *mut LeanObject,
    mut v_a_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1597_: *mut LeanObject = core::ptr::null_mut();
    v_res_1597_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_1594_, v_a_1595_);
    lean_dec(v_a_1595_);
    return v_res_1597_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_markVisited(
    mut v_fvarId_1598_: *mut LeanObject,
    mut v_a_1599_: *mut LeanObject,
    mut v_a_1600_: *mut LeanObject,
    mut v_a_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_1598_, v_a_1600_);
    return v___x_1606_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_markVisited___boxed(
    mut v_fvarId_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
    mut v_a_1609_: *mut LeanObject,
    mut v_a_1610_: *mut LeanObject,
    mut v_a_1611_: *mut LeanObject,
    mut v_a_1612_: *mut LeanObject,
    mut v_a_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1615_: *mut LeanObject = core::ptr::null_mut();
    v_res_1615_ = l_Lean_Compiler_LCNF_Closure_markVisited(
        v_fvarId_1607_,
        v_a_1608_,
        v_a_1609_,
        v_a_1610_,
        v_a_1611_,
        v_a_1612_,
        v_a_1613_,
    );
    lean_dec(v_a_1613_);
    lean_dec_ref(v_a_1612_);
    lean_dec(v_a_1611_);
    lean_dec_ref(v_a_1610_);
    lean_dec(v_a_1609_);
    lean_dec_ref(v_a_1608_);
    return v_res_1615_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0(
    mut v_00_u03b2_1616_: *mut LeanObject,
    mut v_m_1617_: *mut LeanObject,
    mut v_a_1618_: *mut LeanObject,
    mut v_b_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_m_1617_, v_a_1618_, v_b_1619_);
    return v___x_1620_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(
    mut v_00_u03b2_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_x_1623_: *mut LeanObject,
) -> u8 {
    let mut v___x_1624_: u8 = 0;
    v___x_1624_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_1622_, v_x_1623_);
    return v___x_1624_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___boxed(
    mut v_00_u03b2_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
    mut v_x_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1628_: u8 = 0;
    let mut v_r_1629_: *mut LeanObject = core::ptr::null_mut();
    v_res_1628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(v_00_u03b2_1625_, v_a_1626_, v_x_1627_);
    lean_dec(v_x_1627_);
    lean_dec(v_a_1626_);
    v_r_1629_ = lean_box((v_res_1628_) as usize);
    return v_r_1629_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1(
    mut v_00_u03b2_1630_: *mut LeanObject,
    mut v_data_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_data_1631_);
    return v___x_1632_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1633_: *mut LeanObject,
    mut v_i_1634_: *mut LeanObject,
    mut v_source_1635_: *mut LeanObject,
    mut v_target_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    v___x_1637_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(v_i_1634_, v_source_1635_, v_target_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1638_: *mut LeanObject,
    mut v_x_1639_: *mut LeanObject,
    mut v_x_1640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1639_, v_x_1640_);
    return v___x_1641_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_instMonadEIO(lean_box(0));
    return v___x_1642_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(
    mut v_msg_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1660_: u8 = 0;
    let mut v_toFunctor_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___f_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v_toFunctor_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___f_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_22543__overap_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut v_unused_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v_unused_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_unused_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v_unused_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1655_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0);
                v___x_1656_ = l_StateRefT_x27_instMonad___redArg(v___x_1655_);
                v_toApplicative_1657_ = lean_ctor_get(v___x_1656_, 0);
                v_isSharedCheck_1720_ = (!lean_is_exclusive(v___x_1656_)) as u8;
                if v_isSharedCheck_1720_ == 0 {
                    v_unused_1721_ = lean_ctor_get(v___x_1656_, 1);
                    lean_dec(v_unused_1721_);
                    v___x_1659_ = v___x_1656_;
                    v_isShared_1660_ = v_isSharedCheck_1720_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1657_);
                    lean_dec(v___x_1656_);
                    v___x_1659_ = lean_box(0);
                    v_isShared_1660_ = v_isSharedCheck_1720_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1661_ = lean_ctor_get(v_toApplicative_1657_, 0);
                v_toSeq_1662_ = lean_ctor_get(v_toApplicative_1657_, 2);
                v_toSeqLeft_1663_ = lean_ctor_get(v_toApplicative_1657_, 3);
                v_toSeqRight_1664_ = lean_ctor_get(v_toApplicative_1657_, 4);
                v_isSharedCheck_1718_ = (!lean_is_exclusive(v_toApplicative_1657_)) as u8;
                if v_isSharedCheck_1718_ == 0 {
                    v_unused_1719_ = lean_ctor_get(v_toApplicative_1657_, 1);
                    lean_dec(v_unused_1719_);
                    v___x_1666_ = v_toApplicative_1657_;
                    v_isShared_1667_ = v_isSharedCheck_1718_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1664_);
                    lean_inc(v_toSeqLeft_1663_);
                    lean_inc(v_toSeq_1662_);
                    lean_inc(v_toFunctor_1661_);
                    lean_dec(v_toApplicative_1657_);
                    v___x_1666_ = lean_box(0);
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
                lean_inc_ref(v_toFunctor_1661_);
                v___f_1670_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1670_, 0, v_toFunctor_1661_);
                v___f_1671_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1671_, 0, v_toFunctor_1661_);
                v___x_1672_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1672_, 0, v___f_1670_);
                lean_ctor_set(v___x_1672_, 1, v___f_1671_);
                v___f_1673_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1673_, 0, v_toSeqRight_1664_);
                v___f_1674_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1674_, 0, v_toSeqLeft_1663_);
                v___f_1675_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1675_, 0, v_toSeq_1662_);
                if v_isShared_1667_ == 0 {
                    lean_ctor_set(v___x_1666_, 4, v___f_1673_);
                    lean_ctor_set(v___x_1666_, 3, v___f_1674_);
                    lean_ctor_set(v___x_1666_, 2, v___f_1675_);
                    lean_ctor_set(v___x_1666_, 1, v___f_1668_);
                    lean_ctor_set(v___x_1666_, 0, v___x_1672_);
                    v___x_1677_ = v___x_1666_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1672_);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___f_1668_);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 2, v___f_1675_);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 3, v___f_1674_);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 4, v___f_1673_);
                    v___x_1677_ = v_reuseFailAlloc_1717_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1660_ == 0 {
                    lean_ctor_set(v___x_1659_, 1, v___f_1669_);
                    lean_ctor_set(v___x_1659_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1659_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1677_);
                    lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___f_1669_);
                    v___x_1679_ = v_reuseFailAlloc_1716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1680_ = l_StateRefT_x27_instMonad___redArg(v___x_1679_);
                v_toApplicative_1681_ = lean_ctor_get(v___x_1680_, 0);
                v_isSharedCheck_1714_ = (!lean_is_exclusive(v___x_1680_)) as u8;
                if v_isSharedCheck_1714_ == 0 {
                    v_unused_1715_ = lean_ctor_get(v___x_1680_, 1);
                    lean_dec(v_unused_1715_);
                    v___x_1683_ = v___x_1680_;
                    v_isShared_1684_ = v_isSharedCheck_1714_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1681_);
                    lean_dec(v___x_1680_);
                    v___x_1683_ = lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1714_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1685_ = lean_ctor_get(v_toApplicative_1681_, 0);
                v_toSeq_1686_ = lean_ctor_get(v_toApplicative_1681_, 2);
                v_toSeqLeft_1687_ = lean_ctor_get(v_toApplicative_1681_, 3);
                v_toSeqRight_1688_ = lean_ctor_get(v_toApplicative_1681_, 4);
                v_isSharedCheck_1712_ = (!lean_is_exclusive(v_toApplicative_1681_)) as u8;
                if v_isSharedCheck_1712_ == 0 {
                    v_unused_1713_ = lean_ctor_get(v_toApplicative_1681_, 1);
                    lean_dec(v_unused_1713_);
                    v___x_1690_ = v_toApplicative_1681_;
                    v_isShared_1691_ = v_isSharedCheck_1712_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1688_);
                    lean_inc(v_toSeqLeft_1687_);
                    lean_inc(v_toSeq_1686_);
                    lean_inc(v_toFunctor_1685_);
                    lean_dec(v_toApplicative_1681_);
                    v___x_1690_ = lean_box(0);
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
                lean_inc_ref(v_toFunctor_1685_);
                v___f_1694_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1694_, 0, v_toFunctor_1685_);
                v___f_1695_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1695_, 0, v_toFunctor_1685_);
                v___x_1696_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1696_, 0, v___f_1694_);
                lean_ctor_set(v___x_1696_, 1, v___f_1695_);
                v___f_1697_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1697_, 0, v_toSeqRight_1688_);
                v___f_1698_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1698_, 0, v_toSeqLeft_1687_);
                v___f_1699_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1699_, 0, v_toSeq_1686_);
                if v_isShared_1691_ == 0 {
                    lean_ctor_set(v___x_1690_, 4, v___f_1697_);
                    lean_ctor_set(v___x_1690_, 3, v___f_1698_);
                    lean_ctor_set(v___x_1690_, 2, v___f_1699_);
                    lean_ctor_set(v___x_1690_, 1, v___f_1692_);
                    lean_ctor_set(v___x_1690_, 0, v___x_1696_);
                    v___x_1701_ = v___x_1690_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1696_);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___f_1692_);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 2, v___f_1699_);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 3, v___f_1698_);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 4, v___f_1697_);
                    v___x_1701_ = v_reuseFailAlloc_1711_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1684_ == 0 {
                    lean_ctor_set(v___x_1683_, 1, v___f_1693_);
                    lean_ctor_set(v___x_1683_, 0, v___x_1701_);
                    v___x_1703_ = v___x_1683_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1701_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___f_1693_);
                    v___x_1703_ = v_reuseFailAlloc_1710_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1704_ = l_StateRefT_x27_instMonad___redArg(v___x_1703_);
                v___x_1705_ = lean_box(0);
                v___x_1706_ = l_instInhabitedOfMonad___redArg(v___x_1704_, v___x_1705_);
                v___f_1707_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1707_, 0, v___x_1706_);
                v___x_22543__overap_1708_ = lean_panic_fn_borrowed(v___f_1707_, v_msg_1647_);
                lean_dec_ref(v___f_1707_);
                lean_inc(v___y_1653_);
                lean_inc_ref(v___y_1652_);
                lean_inc(v___y_1651_);
                lean_inc_ref(v___y_1650_);
                lean_inc(v___y_1649_);
                lean_inc_ref(v___y_1648_);
                v___x_1709_ = lean_apply_7(
                    v___x_22543__overap_1708_,
                    v___y_1648_,
                    v___y_1649_,
                    v___y_1650_,
                    v___y_1651_,
                    v___y_1652_,
                    v___y_1653_,
                    lean_box(0),
                );
                return v___x_1709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___boxed(
    mut v_msg_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1730_: *mut LeanObject = core::ptr::null_mut();
    v_res_1730_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(
        v_msg_1722_,
        v___y_1723_,
        v___y_1724_,
        v___y_1725_,
        v___y_1726_,
        v___y_1727_,
        v___y_1728_,
    );
    lean_dec(v___y_1728_);
    lean_dec_ref(v___y_1727_);
    lean_dec(v___y_1726_);
    lean_dec_ref(v___y_1725_);
    lean_dec(v___y_1724_);
    lean_dec_ref(v___y_1723_);
    return v_res_1730_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(
    mut v_a_1731_: *mut LeanObject,
    mut v_x_1732_: *mut LeanObject,
) -> u8 {
    let mut v___x_1733_: u8 = 0;
    let mut v_key_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1732_) == 0 {
                    v___x_1733_ = 0;
                    return v___x_1733_;
                } else {
                    v_key_1734_ = lean_ctor_get(v_x_1732_, 0);
                    v_tail_1735_ = lean_ctor_get(v_x_1732_, 2);
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
    mut v_a_1738_: *mut LeanObject,
    mut v_x_1739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1740_: u8 = 0;
    let mut v_r_1741_: *mut LeanObject = core::ptr::null_mut();
    v_res_1740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_1738_, v_x_1739_);
    lean_dec(v_x_1739_);
    lean_dec_ref(v_a_1738_);
    v_r_1741_ = lean_box((v_res_1740_) as usize);
    return v_r_1741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(
    mut v_m_1742_: *mut LeanObject,
    mut v_a_1743_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    v_buckets_1744_ = lean_ctor_get(v_m_1742_, 1);
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
    mut v_m_1760_: *mut LeanObject,
    mut v_a_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: u8 = 0;
    let mut v_r_1763_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_1760_, v_a_1761_);
    lean_dec_ref(v_a_1761_);
    lean_dec_ref(v_m_1760_);
    v_r_1763_ = lean_box((v_res_1762_) as usize);
    return v_r_1763_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(
    mut v_x_1764_: *mut LeanObject,
    mut v_x_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1765_) == 0 {
                    return v_x_1764_;
                } else {
                    v_key_1766_ = lean_ctor_get(v_x_1765_, 0);
                    v_value_1767_ = lean_ctor_get(v_x_1765_, 1);
                    v_tail_1768_ = lean_ctor_get(v_x_1765_, 2);
                    v_isSharedCheck_1791_ = (!lean_is_exclusive(v_x_1765_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1770_ = v_x_1765_;
                        v_isShared_1771_ = v_isSharedCheck_1791_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1768_);
                        lean_inc(v_value_1767_);
                        lean_inc(v_key_1766_);
                        lean_dec(v_x_1765_);
                        v___x_1770_ = lean_box(0);
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
                lean_inc(v___x_1785_);
                if v_isShared_1771_ == 0 {
                    lean_ctor_set(v___x_1770_, 2, v___x_1785_);
                    v___x_1787_ = v___x_1770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_key_1766_);
                    lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_value_1767_);
                    lean_ctor_set(v_reuseFailAlloc_1790_, 2, v___x_1785_);
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
    mut v_i_1792_: *mut LeanObject,
    mut v_source_1793_: *mut LeanObject,
    mut v_target_1794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v_es_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1795_ = lean_array_get_size(v_source_1793_);
                v___x_1796_ = lean_nat_dec_lt(v_i_1792_, v___x_1795_);
                if v___x_1796_ == 0 {
                    lean_dec_ref(v_source_1793_);
                    lean_dec(v_i_1792_);
                    return v_target_1794_;
                } else {
                    v_es_1797_ = lean_array_fget(v_source_1793_, v_i_1792_);
                    v___x_1798_ = lean_box(0);
                    v_source_1799_ = lean_array_fset(v_source_1793_, v_i_1792_, v___x_1798_);
                    v_target_1800_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_target_1794_, v_es_1797_);
                    v___x_1801_ = lean_unsigned_to_nat(1);
                    v___x_1802_ = lean_nat_add(v_i_1792_, v___x_1801_);
                    lean_dec(v_i_1792_);
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
    mut v_data_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    v___x_1805_ = lean_array_get_size(v_data_1804_);
    v___x_1806_ = lean_unsigned_to_nat(2);
    v_nbuckets_1807_ = lean_nat_mul(v___x_1805_, v___x_1806_);
    v___x_1808_ = lean_unsigned_to_nat(0);
    v___x_1809_ = lean_box(0);
    v___x_1810_ = lean_mk_array(v_nbuckets_1807_, v___x_1809_);
    v___x_1811_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v___x_1808_, v_data_1804_, v___x_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(
    mut v_m_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
    mut v_b_1814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v_val_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1852_: u8 = 0;
    let mut v_unused_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1815_ = lean_ctor_get(v_m_1812_, 0);
                v_buckets_1816_ = lean_ctor_get(v_m_1812_, 1);
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
                    lean_inc_ref(v_buckets_1816_);
                    lean_inc(v_size_1815_);
                    v_isSharedCheck_1852_ = (!lean_is_exclusive(v_m_1812_)) as u8;
                    if v_isSharedCheck_1852_ == 0 {
                        v_unused_1853_ = lean_ctor_get(v_m_1812_, 1);
                        lean_dec(v_unused_1853_);
                        v_unused_1854_ = lean_ctor_get(v_m_1812_, 0);
                        lean_dec(v_unused_1854_);
                        v___x_1833_ = v_m_1812_;
                        v_isShared_1834_ = v_isSharedCheck_1852_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1812_);
                        v___x_1833_ = lean_box(0);
                        v_isShared_1834_ = v_isSharedCheck_1852_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1814_);
                    lean_dec_ref(v_a_1813_);
                    return v_m_1812_;
                }
            }
            1 => {
                v___x_1835_ = lean_unsigned_to_nat(1);
                v_size_x27_1836_ = lean_nat_add(v_size_1815_, v___x_1835_);
                lean_dec(v_size_1815_);
                lean_inc(v_bkt_1830_);
                v___x_1837_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1837_, 0, v_a_1813_);
                lean_ctor_set(v___x_1837_, 1, v_b_1814_);
                lean_ctor_set(v___x_1837_, 2, v_bkt_1830_);
                v_buckets_x27_1838_ = lean_array_uset(v_buckets_1816_, v___x_1829_, v___x_1837_);
                v___x_1839_ = lean_unsigned_to_nat(4);
                v___x_1840_ = lean_nat_mul(v_size_x27_1836_, v___x_1839_);
                v___x_1841_ = lean_unsigned_to_nat(3);
                v___x_1842_ = lean_nat_div(v___x_1840_, v___x_1841_);
                lean_dec(v___x_1840_);
                v___x_1843_ = lean_array_get_size(v_buckets_x27_1838_);
                v___x_1844_ = lean_nat_dec_le(v___x_1842_, v___x_1843_);
                lean_dec(v___x_1842_);
                if v___x_1844_ == 0 {
                    v_val_1845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_buckets_x27_1838_);
                    if v_isShared_1834_ == 0 {
                        lean_ctor_set(v___x_1833_, 1, v_val_1845_);
                        lean_ctor_set(v___x_1833_, 0, v_size_x27_1836_);
                        v___x_1847_ = v___x_1833_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_size_x27_1836_);
                        lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_val_1845_);
                        v___x_1847_ = v_reuseFailAlloc_1848_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1834_ == 0 {
                        lean_ctor_set(v___x_1833_, 1, v_buckets_x27_1838_);
                        lean_ctor_set(v___x_1833_, 0, v_size_x27_1836_);
                        v___x_1850_ = v___x_1833_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_size_x27_1836_);
                        lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_buckets_x27_1838_);
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
    mut v_e_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1858_ = lean_st_ref_get(v_a_1856_);
                v_checked_1859_ = lean_ctor_get(v___x_1858_, 1);
                lean_inc_ref(v_checked_1859_);
                lean_dec(v___x_1858_);
                v___x_1860_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_checked_1859_, v_e_1855_);
                lean_dec_ref(v_checked_1859_);
                if v___x_1860_ == 0 {
                    v___x_1861_ = lean_st_ref_take(v_a_1856_);
                    v_visited_1862_ = lean_ctor_get(v___x_1861_, 0);
                    v_checked_1863_ = lean_ctor_get(v___x_1861_, 1);
                    v_isSharedCheck_1875_ = (!lean_is_exclusive(v___x_1861_)) as u8;
                    if v_isSharedCheck_1875_ == 0 {
                        v___x_1865_ = v___x_1861_;
                        v_isShared_1866_ = v_isSharedCheck_1875_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_checked_1863_);
                        lean_inc(v_visited_1862_);
                        lean_dec(v___x_1861_);
                        v___x_1865_ = lean_box(0);
                        v_isShared_1866_ = v_isSharedCheck_1875_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1855_);
                    v___x_1876_ = lean_box((v___x_1860_) as usize);
                    v___x_1877_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1877_, 0, v___x_1876_);
                    return v___x_1877_;
                }
            }
            1 => {
                v___x_1867_ = lean_box(0);
                v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_checked_1863_, v_e_1855_, v___x_1867_);
                if v_isShared_1866_ == 0 {
                    lean_ctor_set(v___x_1865_, 1, v___x_1868_);
                    v___x_1870_ = v___x_1865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_visited_1862_);
                    lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1868_);
                    v___x_1870_ = v_reuseFailAlloc_1874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1871_ = lean_st_ref_set(v_a_1856_, v___x_1870_);
                v___x_1872_ = lean_box((v___x_1860_) as usize);
                v___x_1873_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                return v___x_1873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg___boxed(
    mut v_e_1878_: *mut LeanObject,
    mut v_a_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1881_: *mut LeanObject = core::ptr::null_mut();
    v_res_1881_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_1878_, v_a_1879_);
    lean_dec(v_a_1879_);
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
    mut v_e_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: usize = 0;
    let mut v___x_1891_: usize = 0;
    let mut v___x_1892_: usize = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: usize = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1888_ = lean_st_ref_get(v_a_1886_);
                v_visited_1889_ = lean_ctor_get(v___x_1888_, 0);
                lean_inc_ref(v_visited_1889_);
                lean_dec(v___x_1888_);
                v___x_1890_ = lean_ptr_addr(v_e_1885_);
                v___x_1891_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0_once), _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___closed__0);
                v___x_1892_ = lean_usize_mod(v___x_1890_, v___x_1891_);
                v___x_1893_ = lean_array_uget(v_visited_1889_, v___x_1892_);
                lean_dec_ref(v_visited_1889_);
                v___x_1894_ = lean_ptr_addr(v___x_1893_);
                lean_dec(v___x_1893_);
                v___x_1895_ = lean_usize_dec_eq(v___x_1894_, v___x_1890_);
                if v___x_1895_ == 0 {
                    v___x_1896_ = lean_st_ref_take(v_a_1886_);
                    v_visited_1897_ = lean_ctor_get(v___x_1896_, 0);
                    v_checked_1898_ = lean_ctor_get(v___x_1896_, 1);
                    v_isSharedCheck_1909_ = (!lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1909_ == 0 {
                        v___x_1900_ = v___x_1896_;
                        v_isShared_1901_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_checked_1898_);
                        lean_inc(v_visited_1897_);
                        lean_dec(v___x_1896_);
                        v___x_1900_ = lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1885_);
                    v___x_1910_ = lean_box((v___x_1895_) as usize);
                    v___x_1911_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1911_, 0, v___x_1910_);
                    return v___x_1911_;
                }
            }
            1 => {
                v___x_1902_ = lean_array_uset(v_visited_1897_, v___x_1892_, v_e_1885_);
                if v_isShared_1901_ == 0 {
                    lean_ctor_set(v___x_1900_, 0, v___x_1902_);
                    v___x_1904_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1902_);
                    lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_checked_1898_);
                    v___x_1904_ = v_reuseFailAlloc_1908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1905_ = lean_st_ref_set(v_a_1886_, v___x_1904_);
                v___x_1906_ = lean_box((v___x_1895_) as usize);
                v___x_1907_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1907_, 0, v___x_1906_);
                return v___x_1907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___boxed(
    mut v_e_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1915_: *mut LeanObject = core::ptr::null_mut();
    v_res_1915_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_1912_, v_a_1913_);
    lean_dec(v_a_1913_);
    return v_res_1915_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(
    mut v_p_1916_: *mut LeanObject,
    mut v_f_1917_: *mut LeanObject,
    mut v_stopWhenVisited_1918_: u8,
    mut v_e_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: u8 = 0;
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_unused_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1919_);
                v___x_1968_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_1919_, v_a_1920_);
                if lean_obj_tag(v___x_1968_) == 0 {
                    v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
                    v_isSharedCheck_2001_ = (!lean_is_exclusive(v___x_1968_)) as u8;
                    if v_isSharedCheck_2001_ == 0 {
                        v___x_1971_ = v___x_1968_;
                        v_isShared_1972_ = v_isSharedCheck_2001_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1969_);
                        lean_dec(v___x_1968_);
                        v___x_1971_ = lean_box(0);
                        v_isShared_1972_ = v_isSharedCheck_2001_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1919_);
                    lean_dec_ref(v_f_1917_);
                    lean_dec_ref(v_p_1916_);
                    v_a_2002_ = lean_ctor_get(v___x_1968_, 0);
                    v_isSharedCheck_2009_ = (!lean_is_exclusive(v___x_1968_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2004_ = v___x_1968_;
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2002_);
                        lean_dec(v___x_1968_);
                        v___x_2004_ = lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_f_1917_);
                lean_inc_ref(v_p_1916_);
                v___x_1938_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_d_1935_, v___y_1937_, v___y_1930_, v___y_1931_, v___y_1933_, v___y_1932_, v___y_1934_, v___y_1929_);
                if lean_obj_tag(v___x_1938_) == 0 {
                    lean_dec_ref_known(v___x_1938_, 1);
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
                    lean_dec_ref(v_b_1936_);
                    lean_dec_ref(v_f_1917_);
                    lean_dec_ref(v_p_1916_);
                    return v___x_1938_;
                }
            }
            2 => match lean_obj_tag(v_e_1919_) {
                7 => {
                    v_binderType_1948_ = lean_ctor_get(v_e_1919_, 1);
                    lean_inc_ref(v_binderType_1948_);
                    v_body_1949_ = lean_ctor_get(v_e_1919_, 2);
                    lean_inc_ref(v_body_1949_);
                    lean_dec_ref_known(v_e_1919_, 3);
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
                    v_binderType_1950_ = lean_ctor_get(v_e_1919_, 1);
                    lean_inc_ref(v_binderType_1950_);
                    v_body_1951_ = lean_ctor_get(v_e_1919_, 2);
                    lean_inc_ref(v_body_1951_);
                    lean_dec_ref_known(v_e_1919_, 3);
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
                    v_type_1952_ = lean_ctor_get(v_e_1919_, 1);
                    lean_inc_ref(v_type_1952_);
                    v_value_1953_ = lean_ctor_get(v_e_1919_, 2);
                    lean_inc_ref(v_value_1953_);
                    v_body_1954_ = lean_ctor_get(v_e_1919_, 3);
                    lean_inc_ref(v_body_1954_);
                    lean_dec_ref_known(v_e_1919_, 4);
                    lean_inc_ref(v_f_1917_);
                    lean_inc_ref(v_p_1916_);
                    v___x_1955_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_type_1952_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
                    if lean_obj_tag(v___x_1955_) == 0 {
                        lean_dec_ref_known(v___x_1955_, 1);
                        lean_inc_ref(v_f_1917_);
                        lean_inc_ref(v_p_1916_);
                        v___x_1956_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_value_1953_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
                        if lean_obj_tag(v___x_1956_) == 0 {
                            lean_dec_ref_known(v___x_1956_, 1);
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
                            lean_dec_ref(v_body_1954_);
                            lean_dec_ref(v_f_1917_);
                            lean_dec_ref(v_p_1916_);
                            return v___x_1956_;
                        }
                    } else {
                        lean_dec_ref(v_body_1954_);
                        lean_dec_ref(v_value_1953_);
                        lean_dec_ref(v_f_1917_);
                        lean_dec_ref(v_p_1916_);
                        return v___x_1955_;
                    }
                }
                5 => {
                    v_fn_1958_ = lean_ctor_get(v_e_1919_, 0);
                    lean_inc_ref(v_fn_1958_);
                    v_arg_1959_ = lean_ctor_get(v_e_1919_, 1);
                    lean_inc_ref(v_arg_1959_);
                    lean_dec_ref_known(v_e_1919_, 2);
                    lean_inc_ref(v_f_1917_);
                    lean_inc_ref(v_p_1916_);
                    v___x_1960_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_1916_, v_f_1917_, v_stopWhenVisited_1918_, v_fn_1958_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
                    if lean_obj_tag(v___x_1960_) == 0 {
                        lean_dec_ref_known(v___x_1960_, 1);
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
                        lean_dec_ref(v_arg_1959_);
                        lean_dec_ref(v_f_1917_);
                        lean_dec_ref(v_p_1916_);
                        return v___x_1960_;
                    }
                }
                10 => {
                    v_expr_1962_ = lean_ctor_get(v_e_1919_, 1);
                    lean_inc_ref(v_expr_1962_);
                    lean_dec_ref_known(v_e_1919_, 2);
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
                    v_struct_1964_ = lean_ctor_get(v_e_1919_, 2);
                    lean_inc_ref(v_struct_1964_);
                    lean_dec_ref_known(v_e_1919_, 3);
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
                    lean_dec_ref(v_e_1919_);
                    lean_dec_ref(v_f_1917_);
                    lean_dec_ref(v_p_1916_);
                    v___x_1966_ = lean_box(0);
                    v___x_1967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1967_, 0, v___x_1966_);
                    return v___x_1967_;
                }
            },
            3 => {
                v___x_1973_ = (lean_unbox(v_a_1969_) as u8);
                lean_dec(v_a_1969_);
                if v___x_1973_ == 0 {
                    lean_del_object(v___x_1971_);
                    lean_inc_ref(v_p_1916_);
                    lean_inc_ref(v_e_1919_);
                    v___x_1974_ = lean_apply_1(v_p_1916_, v_e_1919_);
                    v___x_1975_ = (lean_unbox(v___x_1974_) as u8);
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
                        lean_inc_ref(v_e_1919_);
                        v___x_1976_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_1919_, v_a_1920_);
                        if lean_obj_tag(v___x_1976_) == 0 {
                            v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
                            lean_inc(v_a_1977_);
                            lean_dec_ref_known(v___x_1976_, 1);
                            v___x_1978_ = (lean_unbox(v_a_1977_) as u8);
                            lean_dec(v_a_1977_);
                            if v___x_1978_ == 0 {
                                lean_inc_ref(v_f_1917_);
                                lean_inc(v___y_1926_);
                                lean_inc_ref(v___y_1925_);
                                lean_inc(v___y_1924_);
                                lean_inc_ref(v___y_1923_);
                                lean_inc(v___y_1922_);
                                lean_inc_ref(v___y_1921_);
                                lean_inc_ref(v_e_1919_);
                                v___x_1979_ = lean_apply_8(
                                    v_f_1917_,
                                    v_e_1919_,
                                    v___y_1921_,
                                    v___y_1922_,
                                    v___y_1923_,
                                    v___y_1924_,
                                    v___y_1925_,
                                    v___y_1926_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_1979_) == 0 {
                                    v_isSharedCheck_1987_ = (!lean_is_exclusive(v___x_1979_)) as u8;
                                    if v_isSharedCheck_1987_ == 0 {
                                        v_unused_1988_ = lean_ctor_get(v___x_1979_, 0);
                                        lean_dec(v_unused_1988_);
                                        v___x_1981_ = v___x_1979_;
                                        v_isShared_1982_ = v_isSharedCheck_1987_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1979_);
                                        v___x_1981_ = lean_box(0);
                                        v_isShared_1982_ = v_isSharedCheck_1987_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_e_1919_);
                                    lean_dec_ref(v_f_1917_);
                                    lean_dec_ref(v_p_1916_);
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
                            lean_dec_ref(v_e_1919_);
                            lean_dec_ref(v_f_1917_);
                            lean_dec_ref(v_p_1916_);
                            v_a_1989_ = lean_ctor_get(v___x_1976_, 0);
                            v_isSharedCheck_1996_ = (!lean_is_exclusive(v___x_1976_)) as u8;
                            if v_isSharedCheck_1996_ == 0 {
                                v___x_1991_ = v___x_1976_;
                                v_isShared_1992_ = v_isSharedCheck_1996_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1989_);
                                lean_dec(v___x_1976_);
                                v___x_1991_ = lean_box(0);
                                v_isShared_1992_ = v_isSharedCheck_1996_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1919_);
                    lean_dec_ref(v_f_1917_);
                    lean_dec_ref(v_p_1916_);
                    v___x_1997_ = lean_box(0);
                    if v_isShared_1972_ == 0 {
                        lean_ctor_set(v___x_1971_, 0, v___x_1997_);
                        v___x_1999_ = v___x_1971_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
                        v___x_1999_ = v_reuseFailAlloc_2000_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_stopWhenVisited_1918_ == 0 {
                    lean_del_object(v___x_1981_);
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
                    lean_dec_ref(v_e_1919_);
                    lean_dec_ref(v_f_1917_);
                    lean_dec_ref(v_p_1916_);
                    v___x_1983_ = lean_box(0);
                    if v_isShared_1982_ == 0 {
                        lean_ctor_set(v___x_1981_, 0, v___x_1983_);
                        v___x_1985_ = v___x_1981_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
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
                    v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
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
                    v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
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
    mut v_p_2010_: *mut LeanObject,
    mut v_f_2011_: *mut LeanObject,
    mut v_stopWhenVisited_2012_: *mut LeanObject,
    mut v_e_2013_: *mut LeanObject,
    mut v_a_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
    mut v___y_2020_: *mut LeanObject,
    mut v___y_2021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stopWhenVisited_boxed_2022_: u8 = 0;
    let mut v_res_2023_: *mut LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_2022_ = (lean_unbox(v_stopWhenVisited_2012_) as u8);
    v_res_2023_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_2010_, v_f_2011_, v_stopWhenVisited_boxed_2022_, v_e_2013_, v_a_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
    lean_dec(v___y_2020_);
    lean_dec_ref(v___y_2019_);
    lean_dec(v___y_2018_);
    lean_dec_ref(v___y_2017_);
    lean_dec(v___y_2016_);
    lean_dec_ref(v___y_2015_);
    lean_dec(v_a_2014_);
    return v_res_2023_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(
    mut v_p_2024_: *mut LeanObject,
    mut v_f_2025_: *mut LeanObject,
    mut v_e_2026_: *mut LeanObject,
    mut v_stopWhenVisited_2027_: u8,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2035_ = l_Lean_ForEachExprWhere_initCache;
                v___x_2036_ = lean_st_mk_ref(v___x_2035_);
                v___x_2037_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_2024_, v_f_2025_, v_stopWhenVisited_2027_, v_e_2026_, v___x_2036_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
                if lean_obj_tag(v___x_2037_) == 0 {
                    v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2046_ = (!lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2040_ = v___x_2037_;
                        v_isShared_2041_ = v_isSharedCheck_2046_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2038_);
                        lean_dec(v___x_2037_);
                        v___x_2040_ = lean_box(0);
                        v_isShared_2041_ = v_isSharedCheck_2046_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2036_);
                    return v___x_2037_;
                }
            }
            1 => {
                v___x_2042_ = lean_st_ref_get(v___x_2036_);
                lean_dec(v___x_2036_);
                lean_dec(v___x_2042_);
                if v_isShared_2041_ == 0 {
                    v___x_2044_ = v___x_2040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2038_);
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
    mut v_p_2047_: *mut LeanObject,
    mut v_f_2048_: *mut LeanObject,
    mut v_e_2049_: *mut LeanObject,
    mut v_stopWhenVisited_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stopWhenVisited_boxed_2058_: u8 = 0;
    let mut v_res_2059_: *mut LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_2058_ = (lean_unbox(v_stopWhenVisited_2050_) as u8);
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
    lean_dec(v___y_2056_);
    lean_dec_ref(v___y_2055_);
    lean_dec(v___y_2054_);
    lean_dec_ref(v___y_2053_);
    lean_dec(v___y_2052_);
    lean_dec_ref(v___y_2051_);
    return v_res_2059_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(
    mut v_m_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: u8 = 0;
    v_buckets_2062_ = lean_ctor_get(v_m_2060_, 1);
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
    mut v_m_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2080_: u8 = 0;
    let mut v_r_2081_: *mut LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_2078_, v_a_2079_);
    lean_dec(v_a_2079_);
    lean_dec_ref(v_m_2078_);
    v_r_2081_ = lean_box((v_res_2080_) as usize);
    return v_r_2081_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed(
    mut v_e_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
    mut v___y_2086_: *mut LeanObject,
    mut v___y_2087_: *mut LeanObject,
    mut v___y_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2090_: *mut LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_Compiler_LCNF_Closure_collectType___lam__0(
        v_e_2082_,
        v___y_2083_,
        v___y_2084_,
        v___y_2085_,
        v___y_2086_,
        v___y_2087_,
        v___y_2088_,
    );
    lean_dec(v___y_2088_);
    lean_dec_ref(v___y_2087_);
    lean_dec(v___y_2086_);
    lean_dec_ref(v___y_2085_);
    lean_dec(v___y_2084_);
    lean_dec_ref(v___y_2083_);
    lean_dec_ref(v_e_2082_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectType(
    mut v_type_2092_: *mut LeanObject,
    mut v_a_2093_: *mut LeanObject,
    mut v_a_2094_: *mut LeanObject,
    mut v_a_2095_: *mut LeanObject,
    mut v_a_2096_: *mut LeanObject,
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2100_: u8 = 0;
    v___x_2100_ = l_Lean_Expr_hasFVar(v_type_2092_);
    if v___x_2100_ == 0 {
        let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_type_2092_);
        v___x_2101_ = lean_box(0);
        v___x_2102_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2102_, 0, v___x_2101_);
        return v___x_2102_;
    } else {
        let mut v___f_2103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: u8 = 0;
        let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
        v___f_2103_ = lean_alloc_closure(
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
    mut v_as_2107_: *mut LeanObject,
    mut v_i_2108_: usize,
    mut v_stop_2109_: usize,
    mut v_b_2110_: *mut LeanObject,
    mut v___y_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
    mut v___y_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: usize = 0;
    let mut v___x_2124_: usize = 0;
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2118_ = lean_usize_dec_eq(v_i_2108_, v_stop_2109_);
                if v___x_2118_ == 0 {
                    v___x_2119_ = lean_array_uget_borrowed(v_as_2107_, v_i_2108_);
                    v_type_2120_ = lean_ctor_get(v___x_2119_, 2);
                    lean_inc_ref(v_type_2120_);
                    v___x_2121_ = l_Lean_Compiler_LCNF_Closure_collectType(
                        v_type_2120_,
                        v___y_2111_,
                        v___y_2112_,
                        v___y_2113_,
                        v___y_2114_,
                        v___y_2115_,
                        v___y_2116_,
                    );
                    if lean_obj_tag(v___x_2121_) == 0 {
                        v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
                        lean_inc(v_a_2122_);
                        lean_dec_ref_known(v___x_2121_, 1);
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
                    v___x_2126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2126_, 0, v_b_2110_);
                    return v___x_2126_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectParams(
    mut v_params_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
    mut v_a_2131_: *mut LeanObject,
    mut v_a_2132_: *mut LeanObject,
    mut v_a_2133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: u8 = 0;
    v___x_2135_ = lean_unsigned_to_nat(0);
    v___x_2136_ = lean_array_get_size(v_params_2127_);
    v___x_2137_ = lean_box(0);
    v___x_2138_ = lean_nat_dec_lt(v___x_2135_, v___x_2136_);
    if v___x_2138_ == 0 {
        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
        v___x_2139_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2139_, 0, v___x_2137_);
        return v___x_2139_;
    } else {
        let mut v___x_2140_: u8 = 0;
        v___x_2140_ = lean_nat_dec_le(v___x_2136_, v___x_2136_);
        if v___x_2140_ == 0 {
            if v___x_2138_ == 0 {
                let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
                v___x_2141_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2141_, 0, v___x_2137_);
                return v___x_2141_;
            } else {
                let mut v___x_2142_: usize = 0;
                let mut v___x_2143_: usize = 0;
                let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
                v___x_2142_ = 0usize;
                v___x_2143_ = lean_usize_of_nat(v___x_2136_);
                v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_2127_, v___x_2142_, v___x_2143_, v___x_2137_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
                return v___x_2144_;
            }
        } else {
            let mut v___x_2145_: usize = 0;
            let mut v___x_2146_: usize = 0;
            let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
            v___x_2145_ = 0usize;
            v___x_2146_ = lean_usize_of_nat(v___x_2136_);
            v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_2127_, v___x_2145_, v___x_2146_, v___x_2137_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
            return v___x_2147_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectArg(
    mut v_arg_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_arg_2148_) {
        0 => {
            let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
            v___x_2156_ = lean_box(0);
            v___x_2157_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_2157_, 0, v___x_2156_);
            return v___x_2157_;
        }
        1 => {
            let mut v_fvarId_2158_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
            v_fvarId_2158_ = lean_ctor_get(v_arg_2148_, 0);
            lean_inc(v_fvarId_2158_);
            lean_dec_ref_known(v_arg_2148_, 1);
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
            let mut v_expr_2160_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
            v_expr_2160_ = lean_ctor_get(v_arg_2148_, 0);
            lean_inc_ref(v_expr_2160_);
            lean_dec_ref_known(v_arg_2148_, 1);
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
    mut v_as_2162_: *mut LeanObject,
    mut v_i_2163_: usize,
    mut v_stop_2164_: usize,
    mut v_b_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
    mut v___y_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: usize = 0;
    let mut v___x_2178_: usize = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2173_ = lean_usize_dec_eq(v_i_2163_, v_stop_2164_);
                if v___x_2173_ == 0 {
                    v___x_2174_ = lean_array_uget_borrowed(v_as_2162_, v_i_2163_);
                    lean_inc(v___x_2174_);
                    v___x_2175_ = l_Lean_Compiler_LCNF_Closure_collectArg(
                        v___x_2174_,
                        v___y_2166_,
                        v___y_2167_,
                        v___y_2168_,
                        v___y_2169_,
                        v___y_2170_,
                        v___y_2171_,
                    );
                    if lean_obj_tag(v___x_2175_) == 0 {
                        v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
                        lean_inc(v_a_2176_);
                        lean_dec_ref_known(v___x_2175_, 1);
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
                    v___x_2180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2180_, 0, v_b_2165_);
                    return v___x_2180_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectLetValue(
    mut v_e_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
    mut v_a_2184_: *mut LeanObject,
    mut v_a_2185_: *mut LeanObject,
    mut v_a_2186_: *mut LeanObject,
    mut v_a_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_unused_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: usize = 0;
    let mut v___x_2211_: usize = 0;
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: usize = 0;
    let mut v___x_2234_: usize = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: usize = 0;
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_unused_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2181_) {
                0 => {
                    v_isSharedCheck_2196_ = (!lean_is_exclusive(v_e_2181_)) as u8;
                    if v_isSharedCheck_2196_ == 0 {
                        v_unused_2197_ = lean_ctor_get(v_e_2181_, 0);
                        lean_dec(v_unused_2197_);
                        v___x_2190_ = v_e_2181_;
                        v_isShared_2191_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_e_2181_);
                        v___x_2190_ = lean_box(0);
                        v_isShared_2191_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2198_ = lean_box(0);
                    v___x_2199_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2199_, 0, v___x_2198_);
                    return v___x_2199_;
                }
                2 => {
                    v_struct_2200_ = lean_ctor_get(v_e_2181_, 2);
                    lean_inc(v_struct_2200_);
                    lean_dec_ref_known(v_e_2181_, 3);
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
                    v_args_2202_ = lean_ctor_get(v_e_2181_, 2);
                    lean_inc_ref(v_args_2202_);
                    lean_dec_ref_known(v_e_2181_, 3);
                    v___x_2203_ = lean_unsigned_to_nat(0);
                    v___x_2204_ = lean_array_get_size(v_args_2202_);
                    v___x_2205_ = lean_box(0);
                    v___x_2206_ = lean_nat_dec_lt(v___x_2203_, v___x_2204_);
                    if v___x_2206_ == 0 {
                        lean_dec_ref(v_args_2202_);
                        v___x_2207_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2207_, 0, v___x_2205_);
                        return v___x_2207_;
                    } else {
                        v___x_2208_ = lean_nat_dec_le(v___x_2204_, v___x_2204_);
                        if v___x_2208_ == 0 {
                            if v___x_2206_ == 0 {
                                lean_dec_ref(v_args_2202_);
                                v___x_2209_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2209_, 0, v___x_2205_);
                                return v___x_2209_;
                            } else {
                                v___x_2210_ = 0usize;
                                v___x_2211_ = lean_usize_of_nat(v___x_2204_);
                                v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2202_, v___x_2210_, v___x_2211_, v___x_2205_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                                lean_dec_ref(v_args_2202_);
                                return v___x_2212_;
                            }
                        } else {
                            v___x_2213_ = 0usize;
                            v___x_2214_ = lean_usize_of_nat(v___x_2204_);
                            v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2202_, v___x_2213_, v___x_2214_, v___x_2205_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                            lean_dec_ref(v_args_2202_);
                            return v___x_2215_;
                        }
                    }
                }
                _ => {
                    v_fvarId_2216_ = lean_ctor_get(v_e_2181_, 0);
                    lean_inc(v_fvarId_2216_);
                    v_args_2217_ = lean_ctor_get(v_e_2181_, 1);
                    lean_inc_ref(v_args_2217_);
                    lean_dec_ref_known(v_e_2181_, 2);
                    v___x_2218_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
                        v_fvarId_2216_,
                        v_a_2182_,
                        v_a_2183_,
                        v_a_2184_,
                        v_a_2185_,
                        v_a_2186_,
                        v_a_2187_,
                    );
                    if lean_obj_tag(v___x_2218_) == 0 {
                        v_isSharedCheck_2239_ = (!lean_is_exclusive(v___x_2218_)) as u8;
                        if v_isSharedCheck_2239_ == 0 {
                            v_unused_2240_ = lean_ctor_get(v___x_2218_, 0);
                            lean_dec(v_unused_2240_);
                            v___x_2220_ = v___x_2218_;
                            v_isShared_2221_ = v_isSharedCheck_2239_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_2218_);
                            v___x_2220_ = lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2239_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_args_2217_);
                        return v___x_2218_;
                    }
                }
            },
            1 => {
                v___x_2192_ = lean_box(0);
                if v_isShared_2191_ == 0 {
                    lean_ctor_set(v___x_2190_, 0, v___x_2192_);
                    v___x_2194_ = v___x_2190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
                    v___x_2194_ = v_reuseFailAlloc_2195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2194_;
            }
            3 => {
                v___x_2222_ = lean_unsigned_to_nat(0);
                v___x_2223_ = lean_array_get_size(v_args_2217_);
                v___x_2224_ = lean_box(0);
                v___x_2225_ = lean_nat_dec_lt(v___x_2222_, v___x_2223_);
                if v___x_2225_ == 0 {
                    lean_dec_ref(v_args_2217_);
                    if v_isShared_2221_ == 0 {
                        lean_ctor_set(v___x_2220_, 0, v___x_2224_);
                        v___x_2227_ = v___x_2220_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2224_);
                        v___x_2227_ = v_reuseFailAlloc_2228_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2229_ = lean_nat_dec_le(v___x_2223_, v___x_2223_);
                    if v___x_2229_ == 0 {
                        if v___x_2225_ == 0 {
                            lean_dec_ref(v_args_2217_);
                            if v_isShared_2221_ == 0 {
                                lean_ctor_set(v___x_2220_, 0, v___x_2224_);
                                v___x_2231_ = v___x_2220_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2224_);
                                v___x_2231_ = v_reuseFailAlloc_2232_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2220_);
                            v___x_2233_ = 0usize;
                            v___x_2234_ = lean_usize_of_nat(v___x_2223_);
                            v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2217_, v___x_2233_, v___x_2234_, v___x_2224_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                            lean_dec_ref(v_args_2217_);
                            return v___x_2235_;
                        }
                    } else {
                        lean_del_object(v___x_2220_);
                        v___x_2236_ = 0usize;
                        v___x_2237_ = lean_usize_of_nat(v___x_2223_);
                        v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2217_, v___x_2236_, v___x_2237_, v___x_2224_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
                        lean_dec_ref(v_args_2217_);
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
    mut v_as_2241_: *mut LeanObject,
    mut v_i_2242_: usize,
    mut v_stop_2243_: usize,
    mut v_b_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: usize = 0;
    let mut v___x_2258_: u8 = 0;
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2258_ = lean_usize_dec_eq(v_i_2242_, v_stop_2243_);
                if v___x_2258_ == 0 {
                    v___x_2259_ = lean_array_uget_borrowed(v_as_2241_, v_i_2242_);
                    if lean_obj_tag(v___x_2259_) == 0 {
                        v_params_2260_ = lean_ctor_get(v___x_2259_, 1);
                        v_code_2261_ = lean_ctor_get(v___x_2259_, 2);
                        v___x_2262_ = l_Lean_Compiler_LCNF_Closure_collectParams(
                            v_params_2260_,
                            v___y_2245_,
                            v___y_2246_,
                            v___y_2247_,
                            v___y_2248_,
                            v___y_2249_,
                            v___y_2250_,
                        );
                        if lean_obj_tag(v___x_2262_) == 0 {
                            lean_dec_ref_known(v___x_2262_, 1);
                            lean_inc_ref(v_code_2261_);
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
                        v_code_2264_ = lean_ctor_get(v___x_2259_, 0);
                        lean_inc_ref(v_code_2264_);
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
                    v___x_2266_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2266_, 0, v_b_2244_);
                    return v___x_2266_;
                }
            }
            1 => {
                if lean_obj_tag(v___y_2253_) == 0 {
                    v_a_2254_ = lean_ctor_get(v___y_2253_, 0);
                    lean_inc(v_a_2254_);
                    lean_dec_ref_known(v___y_2253_, 1);
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
    mut v_c_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
    mut v_a_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: usize = 0;
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: usize = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: usize = 0;
    let mut v___x_2328_: usize = 0;
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: usize = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_unused_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_c_2267_) {
                0 => {
                    v_decl_2286_ = lean_ctor_get(v_c_2267_, 0);
                    lean_inc_ref(v_decl_2286_);
                    v_k_2287_ = lean_ctor_get(v_c_2267_, 1);
                    lean_inc_ref(v_k_2287_);
                    lean_dec_ref_known(v_c_2267_, 2);
                    v_type_2288_ = lean_ctor_get(v_decl_2286_, 2);
                    lean_inc_ref(v_type_2288_);
                    v_value_2289_ = lean_ctor_get(v_decl_2286_, 3);
                    lean_inc(v_value_2289_);
                    lean_dec_ref(v_decl_2286_);
                    v___x_2290_ = l_Lean_Compiler_LCNF_Closure_collectType(
                        v_type_2288_,
                        v_a_2268_,
                        v_a_2269_,
                        v_a_2270_,
                        v_a_2271_,
                        v_a_2272_,
                        v_a_2273_,
                    );
                    if lean_obj_tag(v___x_2290_) == 0 {
                        lean_dec_ref_known(v___x_2290_, 1);
                        v___x_2291_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(
                            v_value_2289_,
                            v_a_2268_,
                            v_a_2269_,
                            v_a_2270_,
                            v_a_2271_,
                            v_a_2272_,
                            v_a_2273_,
                        );
                        if lean_obj_tag(v___x_2291_) == 0 {
                            lean_dec_ref_known(v___x_2291_, 1);
                            v_c_2267_ = v_k_2287_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_k_2287_);
                            return v___x_2291_;
                        }
                    } else {
                        lean_dec(v_value_2289_);
                        lean_dec_ref(v_k_2287_);
                        return v___x_2290_;
                    }
                }
                3 => {
                    v_args_2293_ = lean_ctor_get(v_c_2267_, 1);
                    lean_inc_ref(v_args_2293_);
                    lean_dec_ref_known(v_c_2267_, 2);
                    v___x_2294_ = lean_unsigned_to_nat(0);
                    v___x_2295_ = lean_array_get_size(v_args_2293_);
                    v___x_2296_ = lean_box(0);
                    v___x_2297_ = lean_nat_dec_lt(v___x_2294_, v___x_2295_);
                    if v___x_2297_ == 0 {
                        lean_dec_ref(v_args_2293_);
                        v___x_2298_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2298_, 0, v___x_2296_);
                        return v___x_2298_;
                    } else {
                        v___x_2299_ = lean_nat_dec_le(v___x_2295_, v___x_2295_);
                        if v___x_2299_ == 0 {
                            if v___x_2297_ == 0 {
                                lean_dec_ref(v_args_2293_);
                                v___x_2300_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2300_, 0, v___x_2296_);
                                return v___x_2300_;
                            } else {
                                v___x_2301_ = 0usize;
                                v___x_2302_ = lean_usize_of_nat(v___x_2295_);
                                v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2293_, v___x_2301_, v___x_2302_, v___x_2296_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                lean_dec_ref(v_args_2293_);
                                return v___x_2303_;
                            }
                        } else {
                            v___x_2304_ = 0usize;
                            v___x_2305_ = lean_usize_of_nat(v___x_2295_);
                            v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_2293_, v___x_2304_, v___x_2305_, v___x_2296_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                            lean_dec_ref(v_args_2293_);
                            return v___x_2306_;
                        }
                    }
                }
                4 => {
                    v_cases_2307_ = lean_ctor_get(v_c_2267_, 0);
                    lean_inc_ref(v_cases_2307_);
                    lean_dec_ref_known(v_c_2267_, 1);
                    v_resultType_2308_ = lean_ctor_get(v_cases_2307_, 1);
                    lean_inc_ref(v_resultType_2308_);
                    v_discr_2309_ = lean_ctor_get(v_cases_2307_, 2);
                    lean_inc(v_discr_2309_);
                    v_alts_2310_ = lean_ctor_get(v_cases_2307_, 3);
                    lean_inc_ref(v_alts_2310_);
                    lean_dec_ref(v_cases_2307_);
                    v___x_2311_ = l_Lean_Compiler_LCNF_Closure_collectType(
                        v_resultType_2308_,
                        v_a_2268_,
                        v_a_2269_,
                        v_a_2270_,
                        v_a_2271_,
                        v_a_2272_,
                        v_a_2273_,
                    );
                    if lean_obj_tag(v___x_2311_) == 0 {
                        lean_dec_ref_known(v___x_2311_, 1);
                        v___x_2312_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
                            v_discr_2309_,
                            v_a_2268_,
                            v_a_2269_,
                            v_a_2270_,
                            v_a_2271_,
                            v_a_2272_,
                            v_a_2273_,
                        );
                        if lean_obj_tag(v___x_2312_) == 0 {
                            v_isSharedCheck_2333_ = (!lean_is_exclusive(v___x_2312_)) as u8;
                            if v_isSharedCheck_2333_ == 0 {
                                v_unused_2334_ = lean_ctor_get(v___x_2312_, 0);
                                lean_dec(v_unused_2334_);
                                v___x_2314_ = v___x_2312_;
                                v_isShared_2315_ = v_isSharedCheck_2333_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_2312_);
                                v___x_2314_ = lean_box(0);
                                v_isShared_2315_ = v_isSharedCheck_2333_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_alts_2310_);
                            return v___x_2312_;
                        }
                    } else {
                        lean_dec_ref(v_alts_2310_);
                        lean_dec(v_discr_2309_);
                        return v___x_2311_;
                    }
                }
                5 => {
                    v_fvarId_2335_ = lean_ctor_get(v_c_2267_, 0);
                    lean_inc(v_fvarId_2335_);
                    lean_dec_ref_known(v_c_2267_, 1);
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
                    v_type_2337_ = lean_ctor_get(v_c_2267_, 0);
                    lean_inc_ref(v_type_2337_);
                    lean_dec_ref_known(v_c_2267_, 1);
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
                    v_decl_2339_ = lean_ctor_get(v_c_2267_, 0);
                    lean_inc_ref(v_decl_2339_);
                    v_k_2340_ = lean_ctor_get(v_c_2267_, 1);
                    lean_inc_ref(v_k_2340_);
                    lean_dec_ref(v_c_2267_);
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
                if lean_obj_tag(v___x_2284_) == 0 {
                    lean_dec_ref_known(v___x_2284_, 1);
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
                    lean_dec_ref(v_k_2277_);
                    return v___x_2284_;
                }
            }
            2 => {
                v___x_2316_ = lean_unsigned_to_nat(0);
                v___x_2317_ = lean_array_get_size(v_alts_2310_);
                v___x_2318_ = lean_box(0);
                v___x_2319_ = lean_nat_dec_lt(v___x_2316_, v___x_2317_);
                if v___x_2319_ == 0 {
                    lean_dec_ref(v_alts_2310_);
                    if v_isShared_2315_ == 0 {
                        lean_ctor_set(v___x_2314_, 0, v___x_2318_);
                        v___x_2321_ = v___x_2314_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2318_);
                        v___x_2321_ = v_reuseFailAlloc_2322_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2323_ = lean_nat_dec_le(v___x_2317_, v___x_2317_);
                    if v___x_2323_ == 0 {
                        if v___x_2319_ == 0 {
                            lean_dec_ref(v_alts_2310_);
                            if v_isShared_2315_ == 0 {
                                lean_ctor_set(v___x_2314_, 0, v___x_2318_);
                                v___x_2325_ = v___x_2314_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2318_);
                                v___x_2325_ = v_reuseFailAlloc_2326_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2314_);
                            v___x_2327_ = 0usize;
                            v___x_2328_ = lean_usize_of_nat(v___x_2317_);
                            v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_2310_, v___x_2327_, v___x_2328_, v___x_2318_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                            lean_dec_ref(v_alts_2310_);
                            return v___x_2329_;
                        }
                    } else {
                        lean_del_object(v___x_2314_);
                        v___x_2330_ = 0usize;
                        v___x_2331_ = lean_usize_of_nat(v___x_2317_);
                        v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_2310_, v___x_2330_, v___x_2331_, v___x_2318_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                        lean_dec_ref(v_alts_2310_);
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
    mut v_decl_2341_: *mut LeanObject,
    mut v_a_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
    mut v_a_2344_: *mut LeanObject,
    mut v_a_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    v_params_2349_ = lean_ctor_get(v_decl_2341_, 2);
    lean_inc_ref(v_params_2349_);
    v_type_2350_ = lean_ctor_get(v_decl_2341_, 3);
    lean_inc_ref(v_type_2350_);
    v_value_2351_ = lean_ctor_get(v_decl_2341_, 4);
    lean_inc_ref(v_value_2351_);
    lean_dec_ref(v_decl_2341_);
    v___x_2352_ = l_Lean_Compiler_LCNF_Closure_collectType(
        v_type_2350_,
        v_a_2342_,
        v_a_2343_,
        v_a_2344_,
        v_a_2345_,
        v_a_2346_,
        v_a_2347_,
    );
    if lean_obj_tag(v___x_2352_) == 0 {
        let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2352_, 1);
        v___x_2353_ = l_Lean_Compiler_LCNF_Closure_collectParams(
            v_params_2349_,
            v_a_2342_,
            v_a_2343_,
            v_a_2344_,
            v_a_2345_,
            v_a_2346_,
            v_a_2347_,
        );
        lean_dec_ref(v_params_2349_);
        if lean_obj_tag(v___x_2353_) == 0 {
            let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_2353_, 1);
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
            lean_dec_ref(v_value_2351_);
            return v___x_2353_;
        }
    } else {
        lean_dec_ref(v_value_2351_);
        lean_dec_ref(v_params_2349_);
        return v___x_2352_;
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3() -> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
    v___x_2359_ = lean_unsigned_to_nat(10);
    v___x_2360_ = lean_unsigned_to_nat(149);
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
    mut v_fvarId_2364_: *mut LeanObject,
    mut v_a_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v_inScope_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstract_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: u8 = 0;
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v_val_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v_fvarId_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_unused_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2445_: u8 = 0;
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2454_: u8 = 0;
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_isSharedCheck_2472_: u8 = 0;
    let mut v_unused_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v_fvarId_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2493_: u8 = 0;
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut v_isSharedCheck_2514_: u8 = 0;
    let mut v_unused_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_unused_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_a_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2554_: u8 = 0;
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_a_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2372_ = lean_st_ref_get(v_a_2366_);
                v_visited_2373_ = lean_ctor_get(v___x_2372_, 0);
                lean_inc_ref(v_visited_2373_);
                lean_dec(v___x_2372_);
                v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_visited_2373_, v_fvarId_2364_);
                lean_dec_ref(v_visited_2373_);
                if v___x_2374_ == 0 {
                    lean_inc(v_fvarId_2364_);
                    v___x_2375_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(
                        v_fvarId_2364_,
                        v_a_2366_,
                    );
                    if lean_obj_tag(v___x_2375_) == 0 {
                        v_isSharedCheck_2564_ = (!lean_is_exclusive(v___x_2375_)) as u8;
                        if v_isSharedCheck_2564_ == 0 {
                            v_unused_2565_ = lean_ctor_get(v___x_2375_, 0);
                            lean_dec(v_unused_2565_);
                            v___x_2377_ = v___x_2375_;
                            v_isShared_2378_ = v_isSharedCheck_2564_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2375_);
                            v___x_2377_ = lean_box(0);
                            v_isShared_2378_ = v_isSharedCheck_2564_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_fvarId_2364_);
                        return v___x_2375_;
                    }
                } else {
                    lean_dec(v_fvarId_2364_);
                    v___x_2566_ = lean_box(0);
                    v___x_2567_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2567_, 0, v___x_2566_);
                    return v___x_2567_;
                }
            }
            1 => {
                v_inScope_2379_ = lean_ctor_get(v_a_2365_, 0);
                v_abstract_2380_ = lean_ctor_get(v_a_2365_, 1);
                lean_inc_ref(v_inScope_2379_);
                lean_inc(v_fvarId_2364_);
                v___x_2381_ = lean_apply_1(v_inScope_2379_, v_fvarId_2364_);
                v___x_2382_ = (lean_unbox(v___x_2381_) as u8);
                if v___x_2382_ == 0 {
                    lean_dec(v_fvarId_2364_);
                    v___x_2383_ = lean_box(0);
                    if v_isShared_2378_ == 0 {
                        lean_ctor_set(v___x_2377_, 0, v___x_2383_);
                        v___x_2385_ = v___x_2377_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
                        v___x_2385_ = v_reuseFailAlloc_2386_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2377_);
                    v___x_2387_ = 0;
                    v___x_2388_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                        v___x_2387_,
                        v_fvarId_2364_,
                        v_a_2368_,
                    );
                    if lean_obj_tag(v___x_2388_) == 0 {
                        v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
                        v_isSharedCheck_2555_ = (!lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2555_ == 0 {
                            v___x_2391_ = v___x_2388_;
                            v_isShared_2392_ = v_isSharedCheck_2555_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2389_);
                            lean_dec(v___x_2388_);
                            v___x_2391_ = lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2555_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_fvarId_2364_);
                        v_a_2556_ = lean_ctor_get(v___x_2388_, 0);
                        v_isSharedCheck_2563_ = (!lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2563_ == 0 {
                            v___x_2558_ = v___x_2388_;
                            v_isShared_2559_ = v_isSharedCheck_2563_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_2556_);
                            lean_dec(v___x_2388_);
                            v___x_2558_ = lean_box(0);
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
                if lean_obj_tag(v_a_2389_) == 1 {
                    lean_dec(v_fvarId_2364_);
                    v_val_2393_ = lean_ctor_get(v_a_2389_, 0);
                    v_isSharedCheck_2446_ = (!lean_is_exclusive(v_a_2389_)) as u8;
                    if v_isSharedCheck_2446_ == 0 {
                        v___x_2395_ = v_a_2389_;
                        v_isShared_2396_ = v_isSharedCheck_2446_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_2393_);
                        lean_dec(v_a_2389_);
                        v___x_2395_ = lean_box(0);
                        v_isShared_2396_ = v_isSharedCheck_2446_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2391_);
                    lean_dec(v_a_2389_);
                    v___x_2447_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(
                        v___x_2387_,
                        v_fvarId_2364_,
                        v_a_2368_,
                    );
                    if lean_obj_tag(v___x_2447_) == 0 {
                        v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
                        lean_inc(v_a_2448_);
                        lean_dec_ref_known(v___x_2447_, 1);
                        if lean_obj_tag(v_a_2448_) == 1 {
                            lean_dec(v_fvarId_2364_);
                            v_val_2449_ = lean_ctor_get(v_a_2448_, 0);
                            lean_inc(v_val_2449_);
                            lean_dec_ref_known(v_a_2448_, 1);
                            v_type_2450_ = lean_ctor_get(v_val_2449_, 2);
                            lean_inc_ref(v_type_2450_);
                            v___x_2451_ = l_Lean_Compiler_LCNF_Closure_collectType(
                                v_type_2450_,
                                v_a_2365_,
                                v_a_2366_,
                                v_a_2367_,
                                v_a_2368_,
                                v_a_2369_,
                                v_a_2370_,
                            );
                            if lean_obj_tag(v___x_2451_) == 0 {
                                v_isSharedCheck_2472_ = (!lean_is_exclusive(v___x_2451_)) as u8;
                                if v_isSharedCheck_2472_ == 0 {
                                    v_unused_2473_ = lean_ctor_get(v___x_2451_, 0);
                                    lean_dec(v_unused_2473_);
                                    v___x_2453_ = v___x_2451_;
                                    v_isShared_2454_ = v_isSharedCheck_2472_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_dec(v___x_2451_);
                                    v___x_2453_ = lean_box(0);
                                    v_isShared_2454_ = v_isSharedCheck_2472_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                lean_dec(v_val_2449_);
                                return v___x_2451_;
                            }
                        } else {
                            lean_dec(v_a_2448_);
                            v___x_2474_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                                v___x_2387_,
                                v_fvarId_2364_,
                                v_a_2368_,
                            );
                            lean_dec(v_fvarId_2364_);
                            if lean_obj_tag(v___x_2474_) == 0 {
                                v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
                                lean_inc(v_a_2475_);
                                lean_dec_ref_known(v___x_2474_, 1);
                                if lean_obj_tag(v_a_2475_) == 1 {
                                    v_val_2476_ = lean_ctor_get(v_a_2475_, 0);
                                    v_isSharedCheck_2536_ = (!lean_is_exclusive(v_a_2475_)) as u8;
                                    if v_isSharedCheck_2536_ == 0 {
                                        v___x_2478_ = v_a_2475_;
                                        v_isShared_2479_ = v_isSharedCheck_2536_;
                                        state = 17;
                                        continue;
                                    } else {
                                        lean_inc(v_val_2476_);
                                        lean_dec(v_a_2475_);
                                        v___x_2478_ = lean_box(0);
                                        v_isShared_2479_ = v_isSharedCheck_2536_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_2475_);
                                    v___x_2537_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once), _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3);
                                    v___x_2538_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v___x_2537_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
                                    return v___x_2538_;
                                }
                            } else {
                                v_a_2539_ = lean_ctor_get(v___x_2474_, 0);
                                v_isSharedCheck_2546_ = (!lean_is_exclusive(v___x_2474_)) as u8;
                                if v_isSharedCheck_2546_ == 0 {
                                    v___x_2541_ = v___x_2474_;
                                    v_isShared_2542_ = v_isSharedCheck_2546_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_inc(v_a_2539_);
                                    lean_dec(v___x_2474_);
                                    v___x_2541_ = lean_box(0);
                                    v_isShared_2542_ = v_isSharedCheck_2546_;
                                    state = 27;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_fvarId_2364_);
                        v_a_2547_ = lean_ctor_get(v___x_2447_, 0);
                        v_isSharedCheck_2554_ = (!lean_is_exclusive(v___x_2447_)) as u8;
                        if v_isSharedCheck_2554_ == 0 {
                            v___x_2549_ = v___x_2447_;
                            v_isShared_2550_ = v_isSharedCheck_2554_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_2547_);
                            lean_dec(v___x_2447_);
                            v___x_2549_ = lean_box(0);
                            v_isShared_2550_ = v_isSharedCheck_2554_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_fvarId_2397_ = lean_ctor_get(v_val_2393_, 0);
                v_binderName_2398_ = lean_ctor_get(v_val_2393_, 1);
                v_type_2399_ = lean_ctor_get(v_val_2393_, 3);
                lean_inc_ref(v_abstract_2380_);
                lean_inc(v_fvarId_2397_);
                v___x_2400_ = lean_apply_1(v_abstract_2380_, v_fvarId_2397_);
                v___x_2401_ = (lean_unbox(v___x_2400_) as u8);
                if v___x_2401_ == 0 {
                    lean_del_object(v___x_2391_);
                    lean_inc(v_val_2393_);
                    v___x_2402_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(
                        v_val_2393_,
                        v_a_2365_,
                        v_a_2366_,
                        v_a_2367_,
                        v_a_2368_,
                        v_a_2369_,
                        v_a_2370_,
                    );
                    if lean_obj_tag(v___x_2402_) == 0 {
                        v_isSharedCheck_2426_ = (!lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2426_ == 0 {
                            v_unused_2427_ = lean_ctor_get(v___x_2402_, 0);
                            lean_dec(v_unused_2427_);
                            v___x_2404_ = v___x_2402_;
                            v_isShared_2405_ = v_isSharedCheck_2426_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_2402_);
                            v___x_2404_ = lean_box(0);
                            v_isShared_2405_ = v_isSharedCheck_2426_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2395_);
                        lean_dec(v_val_2393_);
                        return v___x_2402_;
                    }
                } else {
                    lean_inc_ref(v_type_2399_);
                    lean_inc(v_binderName_2398_);
                    lean_inc(v_fvarId_2397_);
                    lean_del_object(v___x_2395_);
                    lean_dec(v_val_2393_);
                    v___x_2428_ = lean_st_ref_take(v_a_2366_);
                    v_visited_2429_ = lean_ctor_get(v___x_2428_, 0);
                    v_params_2430_ = lean_ctor_get(v___x_2428_, 1);
                    v_decls_2431_ = lean_ctor_get(v___x_2428_, 2);
                    v_isSharedCheck_2445_ = (!lean_is_exclusive(v___x_2428_)) as u8;
                    if v_isSharedCheck_2445_ == 0 {
                        v___x_2433_ = v___x_2428_;
                        v_isShared_2434_ = v_isSharedCheck_2445_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_decls_2431_);
                        lean_inc(v_params_2430_);
                        lean_inc(v_visited_2429_);
                        lean_dec(v___x_2428_);
                        v___x_2433_ = lean_box(0);
                        v_isShared_2434_ = v_isSharedCheck_2445_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2406_ = lean_st_ref_take(v_a_2366_);
                v_visited_2407_ = lean_ctor_get(v___x_2406_, 0);
                v_params_2408_ = lean_ctor_get(v___x_2406_, 1);
                v_decls_2409_ = lean_ctor_get(v___x_2406_, 2);
                v_isSharedCheck_2425_ = (!lean_is_exclusive(v___x_2406_)) as u8;
                if v_isSharedCheck_2425_ == 0 {
                    v___x_2411_ = v___x_2406_;
                    v_isShared_2412_ = v_isSharedCheck_2425_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_decls_2409_);
                    lean_inc(v_params_2408_);
                    lean_inc(v_visited_2407_);
                    lean_dec(v___x_2406_);
                    v___x_2411_ = lean_box(0);
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
                    v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_val_2393_);
                    v___x_2414_ = v_reuseFailAlloc_2424_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2415_ = lean_array_push(v_decls_2409_, v___x_2414_);
                if v_isShared_2412_ == 0 {
                    lean_ctor_set(v___x_2411_, 2, v___x_2415_);
                    v___x_2417_ = v___x_2411_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_visited_2407_);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_params_2408_);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 2, v___x_2415_);
                    v___x_2417_ = v_reuseFailAlloc_2423_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2418_ = lean_st_ref_set(v_a_2366_, v___x_2417_);
                v___x_2419_ = lean_box(0);
                if v_isShared_2405_ == 0 {
                    lean_ctor_set(v___x_2404_, 0, v___x_2419_);
                    v___x_2421_ = v___x_2404_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2421_;
            }
            10 => {
                v___x_2435_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_2435_, 0, v_fvarId_2397_);
                lean_ctor_set(v___x_2435_, 1, v_binderName_2398_);
                lean_ctor_set(v___x_2435_, 2, v_type_2399_);
                lean_ctor_set_uint8(
                    v___x_2435_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2374_,
                );
                v___x_2436_ = lean_array_push(v_params_2430_, v___x_2435_);
                if v_isShared_2434_ == 0 {
                    lean_ctor_set(v___x_2433_, 1, v___x_2436_);
                    v___x_2438_ = v___x_2433_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_visited_2429_);
                    lean_ctor_set(v_reuseFailAlloc_2444_, 1, v___x_2436_);
                    lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_decls_2431_);
                    v___x_2438_ = v_reuseFailAlloc_2444_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2439_ = lean_st_ref_set(v_a_2366_, v___x_2438_);
                v___x_2440_ = lean_box(0);
                if v_isShared_2392_ == 0 {
                    lean_ctor_set(v___x_2391_, 0, v___x_2440_);
                    v___x_2442_ = v___x_2391_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
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
                v_visited_2456_ = lean_ctor_get(v___x_2455_, 0);
                v_params_2457_ = lean_ctor_get(v___x_2455_, 1);
                v_decls_2458_ = lean_ctor_get(v___x_2455_, 2);
                v_isSharedCheck_2471_ = (!lean_is_exclusive(v___x_2455_)) as u8;
                if v_isSharedCheck_2471_ == 0 {
                    v___x_2460_ = v___x_2455_;
                    v_isShared_2461_ = v_isSharedCheck_2471_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_decls_2458_);
                    lean_inc(v_params_2457_);
                    lean_inc(v_visited_2456_);
                    lean_dec(v___x_2455_);
                    v___x_2460_ = lean_box(0);
                    v_isShared_2461_ = v_isSharedCheck_2471_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2462_ = lean_array_push(v_params_2457_, v_val_2449_);
                if v_isShared_2461_ == 0 {
                    lean_ctor_set(v___x_2460_, 1, v___x_2462_);
                    v___x_2464_ = v___x_2460_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_visited_2456_);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2462_);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_decls_2458_);
                    v___x_2464_ = v_reuseFailAlloc_2470_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2465_ = lean_st_ref_set(v_a_2366_, v___x_2464_);
                v___x_2466_ = lean_box(0);
                if v_isShared_2454_ == 0 {
                    lean_ctor_set(v___x_2453_, 0, v___x_2466_);
                    v___x_2468_ = v___x_2453_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
                    v___x_2468_ = v_reuseFailAlloc_2469_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2468_;
            }
            17 => {
                v_fvarId_2480_ = lean_ctor_get(v_val_2476_, 0);
                v_binderName_2481_ = lean_ctor_get(v_val_2476_, 1);
                v_type_2482_ = lean_ctor_get(v_val_2476_, 2);
                v_value_2483_ = lean_ctor_get(v_val_2476_, 3);
                lean_inc_ref(v_type_2482_);
                v___x_2484_ = l_Lean_Compiler_LCNF_Closure_collectType(
                    v_type_2482_,
                    v_a_2365_,
                    v_a_2366_,
                    v_a_2367_,
                    v_a_2368_,
                    v_a_2369_,
                    v_a_2370_,
                );
                if lean_obj_tag(v___x_2484_) == 0 {
                    v_isSharedCheck_2534_ = (!lean_is_exclusive(v___x_2484_)) as u8;
                    if v_isSharedCheck_2534_ == 0 {
                        v_unused_2535_ = lean_ctor_get(v___x_2484_, 0);
                        lean_dec(v_unused_2535_);
                        v___x_2486_ = v___x_2484_;
                        v_isShared_2487_ = v_isSharedCheck_2534_;
                        state = 18;
                        continue;
                    } else {
                        lean_dec(v___x_2484_);
                        v___x_2486_ = lean_box(0);
                        v_isShared_2487_ = v_isSharedCheck_2534_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2478_);
                    lean_dec(v_val_2476_);
                    return v___x_2484_;
                }
            }
            18 => {
                lean_inc_ref(v_abstract_2380_);
                lean_inc(v_fvarId_2480_);
                v___x_2488_ = lean_apply_1(v_abstract_2380_, v_fvarId_2480_);
                v___x_2489_ = (lean_unbox(v___x_2488_) as u8);
                if v___x_2489_ == 0 {
                    lean_del_object(v___x_2486_);
                    lean_inc(v_value_2483_);
                    v___x_2490_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(
                        v_value_2483_,
                        v_a_2365_,
                        v_a_2366_,
                        v_a_2367_,
                        v_a_2368_,
                        v_a_2369_,
                        v_a_2370_,
                    );
                    if lean_obj_tag(v___x_2490_) == 0 {
                        v_isSharedCheck_2514_ = (!lean_is_exclusive(v___x_2490_)) as u8;
                        if v_isSharedCheck_2514_ == 0 {
                            v_unused_2515_ = lean_ctor_get(v___x_2490_, 0);
                            lean_dec(v_unused_2515_);
                            v___x_2492_ = v___x_2490_;
                            v_isShared_2493_ = v_isSharedCheck_2514_;
                            state = 19;
                            continue;
                        } else {
                            lean_dec(v___x_2490_);
                            v___x_2492_ = lean_box(0);
                            v_isShared_2493_ = v_isSharedCheck_2514_;
                            state = 19;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2478_);
                        lean_dec(v_val_2476_);
                        return v___x_2490_;
                    }
                } else {
                    lean_inc_ref(v_type_2482_);
                    lean_inc(v_binderName_2481_);
                    lean_inc(v_fvarId_2480_);
                    lean_del_object(v___x_2478_);
                    lean_dec(v_val_2476_);
                    v___x_2516_ = lean_st_ref_take(v_a_2366_);
                    v_visited_2517_ = lean_ctor_get(v___x_2516_, 0);
                    v_params_2518_ = lean_ctor_get(v___x_2516_, 1);
                    v_decls_2519_ = lean_ctor_get(v___x_2516_, 2);
                    v_isSharedCheck_2533_ = (!lean_is_exclusive(v___x_2516_)) as u8;
                    if v_isSharedCheck_2533_ == 0 {
                        v___x_2521_ = v___x_2516_;
                        v_isShared_2522_ = v_isSharedCheck_2533_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_decls_2519_);
                        lean_inc(v_params_2518_);
                        lean_inc(v_visited_2517_);
                        lean_dec(v___x_2516_);
                        v___x_2521_ = lean_box(0);
                        v_isShared_2522_ = v_isSharedCheck_2533_;
                        state = 24;
                        continue;
                    }
                }
            }
            19 => {
                v___x_2494_ = lean_st_ref_take(v_a_2366_);
                v_visited_2495_ = lean_ctor_get(v___x_2494_, 0);
                v_params_2496_ = lean_ctor_get(v___x_2494_, 1);
                v_decls_2497_ = lean_ctor_get(v___x_2494_, 2);
                v_isSharedCheck_2513_ = (!lean_is_exclusive(v___x_2494_)) as u8;
                if v_isSharedCheck_2513_ == 0 {
                    v___x_2499_ = v___x_2494_;
                    v_isShared_2500_ = v_isSharedCheck_2513_;
                    state = 20;
                    continue;
                } else {
                    lean_inc(v_decls_2497_);
                    lean_inc(v_params_2496_);
                    lean_inc(v_visited_2495_);
                    lean_dec(v___x_2494_);
                    v___x_2499_ = lean_box(0);
                    v_isShared_2500_ = v_isSharedCheck_2513_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2479_ == 0 {
                    lean_ctor_set_tag(v___x_2478_, 0);
                    v___x_2502_ = v___x_2478_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_val_2476_);
                    v___x_2502_ = v_reuseFailAlloc_2512_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2503_ = lean_array_push(v_decls_2497_, v___x_2502_);
                if v_isShared_2500_ == 0 {
                    lean_ctor_set(v___x_2499_, 2, v___x_2503_);
                    v___x_2505_ = v___x_2499_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_visited_2495_);
                    lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_params_2496_);
                    lean_ctor_set(v_reuseFailAlloc_2511_, 2, v___x_2503_);
                    v___x_2505_ = v_reuseFailAlloc_2511_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_2506_ = lean_st_ref_set(v_a_2366_, v___x_2505_);
                v___x_2507_ = lean_box(0);
                if v_isShared_2493_ == 0 {
                    lean_ctor_set(v___x_2492_, 0, v___x_2507_);
                    v___x_2509_ = v___x_2492_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
                    v___x_2509_ = v_reuseFailAlloc_2510_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2509_;
            }
            24 => {
                v___x_2523_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_2523_, 0, v_fvarId_2480_);
                lean_ctor_set(v___x_2523_, 1, v_binderName_2481_);
                lean_ctor_set(v___x_2523_, 2, v_type_2482_);
                lean_ctor_set_uint8(
                    v___x_2523_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2374_,
                );
                v___x_2524_ = lean_array_push(v_params_2518_, v___x_2523_);
                if v_isShared_2522_ == 0 {
                    lean_ctor_set(v___x_2521_, 1, v___x_2524_);
                    v___x_2526_ = v___x_2521_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_visited_2517_);
                    lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2524_);
                    lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_decls_2519_);
                    v___x_2526_ = v_reuseFailAlloc_2532_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_2527_ = lean_st_ref_set(v_a_2366_, v___x_2526_);
                v___x_2528_ = lean_box(0);
                if v_isShared_2487_ == 0 {
                    lean_ctor_set(v___x_2486_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2486_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
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
                    v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
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
                    v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
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
                    v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
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
    mut v_e_2568_: *mut LeanObject,
    mut v___y_2569_: *mut LeanObject,
    mut v___y_2570_: *mut LeanObject,
    mut v___y_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_arg_2578_: *mut LeanObject,
    mut v_a_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2586_: *mut LeanObject = core::ptr::null_mut();
    v_res_2586_ = l_Lean_Compiler_LCNF_Closure_collectArg(
        v_arg_2578_,
        v_a_2579_,
        v_a_2580_,
        v_a_2581_,
        v_a_2582_,
        v_a_2583_,
        v_a_2584_,
    );
    lean_dec(v_a_2584_);
    lean_dec_ref(v_a_2583_);
    lean_dec(v_a_2582_);
    lean_dec_ref(v_a_2581_);
    lean_dec(v_a_2580_);
    lean_dec_ref(v_a_2579_);
    return v_res_2586_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectType___boxed(
    mut v_type_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
    mut v_a_2591_: *mut LeanObject,
    mut v_a_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2595_: *mut LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_Lean_Compiler_LCNF_Closure_collectType(
        v_type_2587_,
        v_a_2588_,
        v_a_2589_,
        v_a_2590_,
        v_a_2591_,
        v_a_2592_,
        v_a_2593_,
    );
    lean_dec(v_a_2593_);
    lean_dec_ref(v_a_2592_);
    lean_dec(v_a_2591_);
    lean_dec_ref(v_a_2590_);
    lean_dec(v_a_2589_);
    lean_dec_ref(v_a_2588_);
    return v_res_2595_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(
    mut v_decl_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
    mut v_a_2602_: *mut LeanObject,
    mut v_a_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2604_: *mut LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(
        v_decl_2596_,
        v_a_2597_,
        v_a_2598_,
        v_a_2599_,
        v_a_2600_,
        v_a_2601_,
        v_a_2602_,
    );
    lean_dec(v_a_2602_);
    lean_dec_ref(v_a_2601_);
    lean_dec(v_a_2600_);
    lean_dec_ref(v_a_2599_);
    lean_dec(v_a_2598_);
    lean_dec_ref(v_a_2597_);
    return v_res_2604_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7___boxed(
    mut v_as_2605_: *mut LeanObject,
    mut v_i_2606_: *mut LeanObject,
    mut v_stop_2607_: *mut LeanObject,
    mut v_b_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
    mut v___y_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
    mut v___y_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2616_: usize = 0;
    let mut v_stop_boxed_2617_: usize = 0;
    let mut v_res_2618_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2616_ = lean_unbox_usize(v_i_2606_);
    lean_dec(v_i_2606_);
    v_stop_boxed_2617_ = lean_unbox_usize(v_stop_2607_);
    lean_dec(v_stop_2607_);
    v_res_2618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_as_2605_, v_i_boxed_2616_, v_stop_boxed_2617_, v_b_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
    lean_dec(v___y_2614_);
    lean_dec_ref(v___y_2613_);
    lean_dec(v___y_2612_);
    lean_dec_ref(v___y_2611_);
    lean_dec(v___y_2610_);
    lean_dec_ref(v___y_2609_);
    lean_dec_ref(v_as_2605_);
    return v_res_2618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0___boxed(
    mut v_as_2619_: *mut LeanObject,
    mut v_i_2620_: *mut LeanObject,
    mut v_stop_2621_: *mut LeanObject,
    mut v_b_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2630_: usize = 0;
    let mut v_stop_boxed_2631_: usize = 0;
    let mut v_res_2632_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2630_ = lean_unbox_usize(v_i_2620_);
    lean_dec(v_i_2620_);
    v_stop_boxed_2631_ = lean_unbox_usize(v_stop_2621_);
    lean_dec(v_stop_2621_);
    v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_as_2619_, v_i_boxed_2630_, v_stop_boxed_2631_, v_b_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
    lean_dec(v___y_2628_);
    lean_dec_ref(v___y_2627_);
    lean_dec(v___y_2626_);
    lean_dec_ref(v___y_2625_);
    lean_dec(v___y_2624_);
    lean_dec_ref(v___y_2623_);
    lean_dec_ref(v_as_2619_);
    return v_res_2632_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectParams___boxed(
    mut v_params_2633_: *mut LeanObject,
    mut v_a_2634_: *mut LeanObject,
    mut v_a_2635_: *mut LeanObject,
    mut v_a_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2641_: *mut LeanObject = core::ptr::null_mut();
    v_res_2641_ = l_Lean_Compiler_LCNF_Closure_collectParams(
        v_params_2633_,
        v_a_2634_,
        v_a_2635_,
        v_a_2636_,
        v_a_2637_,
        v_a_2638_,
        v_a_2639_,
    );
    lean_dec(v_a_2639_);
    lean_dec_ref(v_a_2638_);
    lean_dec(v_a_2637_);
    lean_dec_ref(v_a_2636_);
    lean_dec(v_a_2635_);
    lean_dec_ref(v_a_2634_);
    lean_dec_ref(v_params_2633_);
    return v_res_2641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11___boxed(
    mut v_as_2642_: *mut LeanObject,
    mut v_i_2643_: *mut LeanObject,
    mut v_stop_2644_: *mut LeanObject,
    mut v_b_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
    mut v___y_2651_: *mut LeanObject,
    mut v___y_2652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2653_: usize = 0;
    let mut v_stop_boxed_2654_: usize = 0;
    let mut v_res_2655_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2653_ = lean_unbox_usize(v_i_2643_);
    lean_dec(v_i_2643_);
    v_stop_boxed_2654_ = lean_unbox_usize(v_stop_2644_);
    lean_dec(v_stop_2644_);
    v_res_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_as_2642_, v_i_boxed_2653_, v_stop_boxed_2654_, v_b_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
    lean_dec(v___y_2651_);
    lean_dec_ref(v___y_2650_);
    lean_dec(v___y_2649_);
    lean_dec_ref(v___y_2648_);
    lean_dec(v___y_2647_);
    lean_dec_ref(v___y_2646_);
    lean_dec_ref(v_as_2642_);
    return v_res_2655_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectLetValue___boxed(
    mut v_e_2656_: *mut LeanObject,
    mut v_a_2657_: *mut LeanObject,
    mut v_a_2658_: *mut LeanObject,
    mut v_a_2659_: *mut LeanObject,
    mut v_a_2660_: *mut LeanObject,
    mut v_a_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
    mut v_a_2663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2664_: *mut LeanObject = core::ptr::null_mut();
    v_res_2664_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(
        v_e_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_,
    );
    lean_dec(v_a_2662_);
    lean_dec_ref(v_a_2661_);
    lean_dec(v_a_2660_);
    lean_dec_ref(v_a_2659_);
    lean_dec(v_a_2658_);
    lean_dec_ref(v_a_2657_);
    return v_res_2664_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectCode___boxed(
    mut v_c_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
    mut v_a_2669_: *mut LeanObject,
    mut v_a_2670_: *mut LeanObject,
    mut v_a_2671_: *mut LeanObject,
    mut v_a_2672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2673_: *mut LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Compiler_LCNF_Closure_collectCode(
        v_c_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_,
    );
    lean_dec(v_a_2671_);
    lean_dec_ref(v_a_2670_);
    lean_dec(v_a_2669_);
    lean_dec_ref(v_a_2668_);
    lean_dec(v_a_2667_);
    lean_dec_ref(v_a_2666_);
    return v_res_2673_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_collectFVar___boxed(
    mut v_fvarId_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
    mut v_a_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2682_: *mut LeanObject = core::ptr::null_mut();
    v_res_2682_ = l_Lean_Compiler_LCNF_Closure_collectFVar(
        v_fvarId_2674_,
        v_a_2675_,
        v_a_2676_,
        v_a_2677_,
        v_a_2678_,
        v_a_2679_,
        v_a_2680_,
    );
    lean_dec(v_a_2680_);
    lean_dec_ref(v_a_2679_);
    lean_dec(v_a_2678_);
    lean_dec_ref(v_a_2677_);
    lean_dec(v_a_2676_);
    lean_dec_ref(v_a_2675_);
    return v_res_2682_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(
    mut v_00_u03b2_2683_: *mut LeanObject,
    mut v_m_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
) -> u8 {
    let mut v___x_2686_: u8 = 0;
    v___x_2686_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_2684_, v_a_2685_);
    return v___x_2686_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___boxed(
    mut v_00_u03b2_2687_: *mut LeanObject,
    mut v_m_2688_: *mut LeanObject,
    mut v_a_2689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2690_: u8 = 0;
    let mut v_r_2691_: *mut LeanObject = core::ptr::null_mut();
    v_res_2690_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(v_00_u03b2_2687_, v_m_2688_, v_a_2689_);
    lean_dec(v_a_2689_);
    lean_dec_ref(v_m_2688_);
    v_r_2691_ = lean_box((v_res_2690_) as usize);
    return v_r_2691_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(
    mut v_e_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    v___x_2701_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_2692_, v_a_2693_);
    return v___x_2701_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___boxed(
    mut v_e_2702_: *mut LeanObject,
    mut v_a_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2711_: *mut LeanObject = core::ptr::null_mut();
    v_res_2711_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(v_e_2702_, v_a_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
    lean_dec(v___y_2709_);
    lean_dec_ref(v___y_2708_);
    lean_dec(v___y_2707_);
    lean_dec_ref(v___y_2706_);
    lean_dec(v___y_2705_);
    lean_dec_ref(v___y_2704_);
    lean_dec(v_a_2703_);
    return v_res_2711_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(
    mut v_e_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_2712_, v_a_2713_);
    return v___x_2721_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___boxed(
    mut v_e_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v___y_2724_: *mut LeanObject,
    mut v___y_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
    mut v___y_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2731_: *mut LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(v_e_2722_, v_a_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
    lean_dec(v___y_2729_);
    lean_dec_ref(v___y_2728_);
    lean_dec(v___y_2727_);
    lean_dec_ref(v___y_2726_);
    lean_dec(v___y_2725_);
    lean_dec_ref(v___y_2724_);
    lean_dec(v_a_2723_);
    return v_res_2731_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(
    mut v_00_u03b2_2732_: *mut LeanObject,
    mut v_m_2733_: *mut LeanObject,
    mut v_a_2734_: *mut LeanObject,
) -> u8 {
    let mut v___x_2735_: u8 = 0;
    v___x_2735_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_2733_, v_a_2734_);
    return v___x_2735_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___boxed(
    mut v_00_u03b2_2736_: *mut LeanObject,
    mut v_m_2737_: *mut LeanObject,
    mut v_a_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2739_: u8 = 0;
    let mut v_r_2740_: *mut LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(v_00_u03b2_2736_, v_m_2737_, v_a_2738_);
    lean_dec_ref(v_a_2738_);
    lean_dec_ref(v_m_2737_);
    v_r_2740_ = lean_box((v_res_2739_) as usize);
    return v_r_2740_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15(
    mut v_00_u03b2_2741_: *mut LeanObject,
    mut v_m_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_b_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    v___x_2745_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_m_2742_, v_a_2743_, v_b_2744_);
    return v___x_2745_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(
    mut v_00_u03b2_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_x_2748_: *mut LeanObject,
) -> u8 {
    let mut v___x_2749_: u8 = 0;
    v___x_2749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_2747_, v_x_2748_);
    return v___x_2749_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___boxed(
    mut v_00_u03b2_2750_: *mut LeanObject,
    mut v_a_2751_: *mut LeanObject,
    mut v_x_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2753_: u8 = 0;
    let mut v_r_2754_: *mut LeanObject = core::ptr::null_mut();
    v_res_2753_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(v_00_u03b2_2750_, v_a_2751_, v_x_2752_);
    lean_dec(v_x_2752_);
    lean_dec_ref(v_a_2751_);
    v_r_2754_ = lean_box((v_res_2753_) as usize);
    return v_r_2754_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17(
    mut v_00_u03b2_2755_: *mut LeanObject,
    mut v_data_2756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    v___x_2757_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_data_2756_);
    return v___x_2757_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18(
    mut v_00_u03b2_2758_: *mut LeanObject,
    mut v_i_2759_: *mut LeanObject,
    mut v_source_2760_: *mut LeanObject,
    mut v_target_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    v___x_2762_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v_i_2759_, v_source_2760_, v_target_2761_);
    return v___x_2762_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19(
    mut v_00_u03b2_2763_: *mut LeanObject,
    mut v_x_2764_: *mut LeanObject,
    mut v_x_2765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_x_2764_, v_x_2765_);
    return v___x_2766_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(
    mut v_k_2767_: *mut LeanObject,
    mut v_t_2768_: *mut LeanObject,
) -> u8 {
    let mut v_k_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2774_: u8 = 0;
    let mut v___x_2776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2768_) == 0 {
                    v_k_2769_ = lean_ctor_get(v_t_2768_, 1);
                    v_l_2770_ = lean_ctor_get(v_t_2768_, 3);
                    v_r_2771_ = lean_ctor_get(v_t_2768_, 4);
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
    mut v_k_2777_: *mut LeanObject,
    mut v_t_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2779_: u8 = 0;
    let mut v_r_2780_: *mut LeanObject = core::ptr::null_mut();
    v_res_2779_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_2777_, v_t_2778_);
    lean_dec(v_t_2778_);
    lean_dec(v_k_2777_);
    v_r_2780_ = lean_box((v_res_2779_) as usize);
    return v_r_2780_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(
    mut v_a_2781_: *mut LeanObject,
    mut v_as_2782_: *mut LeanObject,
    mut v_i_2783_: usize,
    mut v_stop_2784_: usize,
    mut v_b_2785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: usize = 0;
    let mut v___x_2789_: usize = 0;
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2791_ = lean_usize_dec_eq(v_i_2783_, v_stop_2784_);
                if v___x_2791_ == 0 {
                    v___x_2792_ = lean_array_uget_borrowed(v_as_2782_, v_i_2783_);
                    v___x_2793_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_2792_);
                    v___x_2794_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v___x_2793_, v_a_2781_);
                    lean_dec(v___x_2793_);
                    if v___x_2794_ == 0 {
                        lean_inc(v___x_2792_);
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
    mut v_a_2796_: *mut LeanObject,
    mut v_as_2797_: *mut LeanObject,
    mut v_i_2798_: *mut LeanObject,
    mut v_stop_2799_: *mut LeanObject,
    mut v_b_2800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2801_: usize = 0;
    let mut v_stop_boxed_2802_: usize = 0;
    let mut v_res_2803_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2801_ = lean_unbox_usize(v_i_2798_);
    lean_dec(v_i_2798_);
    v_stop_boxed_2802_ = lean_unbox_usize(v_stop_2799_);
    lean_dec(v_stop_2799_);
    v_res_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_2796_, v_as_2797_, v_i_boxed_2801_, v_stop_boxed_2802_, v_b_2800_);
    lean_dec_ref(v_as_2797_);
    lean_dec(v_a_2796_);
    return v_res_2803_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(
    mut v_as_2804_: *mut LeanObject,
    mut v_sz_2805_: usize,
    mut v_i_2806_: usize,
    mut v_b_2807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: usize = 0;
    let mut v___x_2815_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2809_ = lean_usize_dec_lt(v_i_2806_, v_sz_2805_);
                if v___x_2809_ == 0 {
                    v___x_2810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2810_, 0, v_b_2807_);
                    return v___x_2810_;
                } else {
                    v_a_2811_ = lean_array_uget_borrowed(v_as_2804_, v_i_2806_);
                    v_fvarId_2812_ = lean_ctor_get(v_a_2811_, 0);
                    lean_inc(v_fvarId_2812_);
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
    mut v_as_2817_: *mut LeanObject,
    mut v_sz_2818_: *mut LeanObject,
    mut v_i_2819_: *mut LeanObject,
    mut v_b_2820_: *mut LeanObject,
    mut v___y_2821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2822_: usize = 0;
    let mut v_i_boxed_2823_: usize = 0;
    let mut v_res_2824_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2822_ = lean_unbox_usize(v_sz_2818_);
    lean_dec(v_sz_2818_);
    v_i_boxed_2823_ = lean_unbox_usize(v_i_2819_);
    lean_dec(v_i_2819_);
    v_res_2824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_2817_, v_sz_boxed_2822_, v_i_boxed_2823_, v_b_2820_);
    lean_dec_ref(v_as_2817_);
    return v_res_2824_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    v___x_2827_ = l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0;
    v___x_2828_ = l_Lean_instEmptyCollectionFVarIdHashSet;
    v___x_2829_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2829_, 0, v___x_2828_);
    lean_ctor_set(v___x_2829_, 1, v___x_2827_);
    lean_ctor_set(v___x_2829_, 2, v___x_2827_);
    return v___x_2829_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_run___redArg(
    mut v_x_2830_: *mut LeanObject,
    mut v_inScope_2831_: *mut LeanObject,
    mut v_abstract_2832_: *mut LeanObject,
    mut v_a_2833_: *mut LeanObject,
    mut v_a_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
    mut v_a_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2849_: usize = 0;
    let mut v___x_2850_: usize = 0;
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___y_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: usize = 0;
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v_a_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2838_ = lean_unsigned_to_nat(0);
                v___x_2839_ = l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0;
                v___x_2840_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1,
                );
                v___x_2841_ = lean_st_mk_ref(v___x_2840_);
                v___x_2842_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2842_, 0, v_inScope_2831_);
                lean_ctor_set(v___x_2842_, 1, v_abstract_2832_);
                lean_inc(v_a_2836_);
                lean_inc_ref(v_a_2835_);
                lean_inc(v_a_2834_);
                lean_inc_ref(v_a_2833_);
                lean_inc(v___x_2841_);
                v___x_2843_ = lean_apply_7(
                    v_x_2830_,
                    v___x_2842_,
                    v___x_2841_,
                    v_a_2833_,
                    v_a_2834_,
                    v_a_2835_,
                    v_a_2836_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2843_) == 0 {
                    v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
                    lean_inc(v_a_2844_);
                    lean_dec_ref_known(v___x_2843_, 1);
                    v___x_2845_ = lean_st_ref_get(v___x_2841_);
                    lean_dec(v___x_2841_);
                    v_params_2846_ = lean_ctor_get(v___x_2845_, 1);
                    lean_inc_ref(v_params_2846_);
                    v_decls_2847_ = lean_ctor_get(v___x_2845_, 2);
                    lean_inc_ref(v_decls_2847_);
                    lean_dec(v___x_2845_);
                    v___x_2848_ = lean_box(1);
                    v_sz_2849_ = lean_array_size(v_params_2846_);
                    v___x_2850_ = 0usize;
                    v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_params_2846_, v_sz_2849_, v___x_2850_, v___x_2848_);
                    if lean_obj_tag(v___x_2851_) == 0 {
                        v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
                        v_isSharedCheck_2870_ = (!lean_is_exclusive(v___x_2851_)) as u8;
                        if v_isSharedCheck_2870_ == 0 {
                            v___x_2854_ = v___x_2851_;
                            v_isShared_2855_ = v_isSharedCheck_2870_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2852_);
                            lean_dec(v___x_2851_);
                            v___x_2854_ = lean_box(0);
                            v_isShared_2855_ = v_isSharedCheck_2870_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_decls_2847_);
                        lean_dec_ref(v_params_2846_);
                        lean_dec(v_a_2844_);
                        v_a_2871_ = lean_ctor_get(v___x_2851_, 0);
                        v_isSharedCheck_2878_ = (!lean_is_exclusive(v___x_2851_)) as u8;
                        if v_isSharedCheck_2878_ == 0 {
                            v___x_2873_ = v___x_2851_;
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2871_);
                            lean_dec(v___x_2851_);
                            v___x_2873_ = lean_box(0);
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2841_);
                    v_a_2879_ = lean_ctor_get(v___x_2843_, 0);
                    v_isSharedCheck_2886_ = (!lean_is_exclusive(v___x_2843_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2881_ = v___x_2843_;
                        v_isShared_2882_ = v_isSharedCheck_2886_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2879_);
                        lean_dec(v___x_2843_);
                        v___x_2881_ = lean_box(0);
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
                    lean_dec(v_a_2852_);
                    lean_dec_ref(v_decls_2847_);
                    v___y_2857_ = v___x_2839_;
                    state = 2;
                    continue;
                } else {
                    v___x_2865_ = lean_nat_dec_le(v___x_2863_, v___x_2863_);
                    if v___x_2865_ == 0 {
                        if v___x_2864_ == 0 {
                            lean_dec(v_a_2852_);
                            lean_dec_ref(v_decls_2847_);
                            v___y_2857_ = v___x_2839_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2866_ = lean_usize_of_nat(v___x_2863_);
                            v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_2852_, v_decls_2847_, v___x_2850_, v___x_2866_, v___x_2839_);
                            lean_dec_ref(v_decls_2847_);
                            lean_dec(v_a_2852_);
                            v___y_2857_ = v___x_2867_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2868_ = lean_usize_of_nat(v___x_2863_);
                        v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_2852_, v_decls_2847_, v___x_2850_, v___x_2868_, v___x_2839_);
                        lean_dec_ref(v_decls_2847_);
                        lean_dec(v_a_2852_);
                        v___y_2857_ = v___x_2869_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2858_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2858_, 0, v_params_2846_);
                lean_ctor_set(v___x_2858_, 1, v___y_2857_);
                v___x_2859_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2859_, 0, v_a_2844_);
                lean_ctor_set(v___x_2859_, 1, v___x_2858_);
                if v_isShared_2855_ == 0 {
                    lean_ctor_set(v___x_2854_, 0, v___x_2859_);
                    v___x_2861_ = v___x_2854_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
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
                    v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
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
                    v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
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
    mut v_x_2887_: *mut LeanObject,
    mut v_inScope_2888_: *mut LeanObject,
    mut v_abstract_2889_: *mut LeanObject,
    mut v_a_2890_: *mut LeanObject,
    mut v_a_2891_: *mut LeanObject,
    mut v_a_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
    mut v_a_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2895_: *mut LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Lean_Compiler_LCNF_Closure_run___redArg(
        v_x_2887_,
        v_inScope_2888_,
        v_abstract_2889_,
        v_a_2890_,
        v_a_2891_,
        v_a_2892_,
        v_a_2893_,
    );
    lean_dec(v_a_2893_);
    lean_dec_ref(v_a_2892_);
    lean_dec(v_a_2891_);
    lean_dec_ref(v_a_2890_);
    return v_res_2895_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Closure_run(
    mut v_00_u03b1_2896_: *mut LeanObject,
    mut v_x_2897_: *mut LeanObject,
    mut v_inScope_2898_: *mut LeanObject,
    mut v_abstract_2899_: *mut LeanObject,
    mut v_a_2900_: *mut LeanObject,
    mut v_a_2901_: *mut LeanObject,
    mut v_a_2902_: *mut LeanObject,
    mut v_a_2903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2906_: *mut LeanObject,
    mut v_x_2907_: *mut LeanObject,
    mut v_inScope_2908_: *mut LeanObject,
    mut v_abstract_2909_: *mut LeanObject,
    mut v_a_2910_: *mut LeanObject,
    mut v_a_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
    mut v_a_2913_: *mut LeanObject,
    mut v_a_2914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2915_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2913_);
    lean_dec_ref(v_a_2912_);
    lean_dec(v_a_2911_);
    lean_dec_ref(v_a_2910_);
    return v_res_2915_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(
    mut v_as_2916_: *mut LeanObject,
    mut v_sz_2917_: usize,
    mut v_i_2918_: usize,
    mut v_b_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_2916_, v_sz_2917_, v_i_2918_, v_b_2919_);
    return v___x_2925_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___boxed(
    mut v_as_2926_: *mut LeanObject,
    mut v_sz_2927_: *mut LeanObject,
    mut v_i_2928_: *mut LeanObject,
    mut v_b_2929_: *mut LeanObject,
    mut v___y_2930_: *mut LeanObject,
    mut v___y_2931_: *mut LeanObject,
    mut v___y_2932_: *mut LeanObject,
    mut v___y_2933_: *mut LeanObject,
    mut v___y_2934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2935_: usize = 0;
    let mut v_i_boxed_2936_: usize = 0;
    let mut v_res_2937_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2935_ = lean_unbox_usize(v_sz_2927_);
    lean_dec(v_sz_2927_);
    v_i_boxed_2936_ = lean_unbox_usize(v_i_2928_);
    lean_dec(v_i_2928_);
    v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(v_as_2926_, v_sz_boxed_2935_, v_i_boxed_2936_, v_b_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
    lean_dec(v___y_2933_);
    lean_dec_ref(v___y_2932_);
    lean_dec(v___y_2931_);
    lean_dec_ref(v___y_2930_);
    lean_dec_ref(v_as_2926_);
    return v_res_2937_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(
    mut v_00_u03b2_2938_: *mut LeanObject,
    mut v_k_2939_: *mut LeanObject,
    mut v_t_2940_: *mut LeanObject,
) -> u8 {
    let mut v___x_2941_: u8 = 0;
    v___x_2941_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_2939_, v_t_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___boxed(
    mut v_00_u03b2_2942_: *mut LeanObject,
    mut v_k_2943_: *mut LeanObject,
    mut v_t_2944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2945_: u8 = 0;
    let mut v_r_2946_: *mut LeanObject = core::ptr::null_mut();
    v_res_2945_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(
            v_00_u03b2_2942_,
            v_k_2943_,
            v_t_2944_,
        );
    lean_dec(v_t_2944_);
    lean_dec(v_k_2943_);
    v_r_2946_ = lean_box((v_res_2945_) as usize);
    return v_r_2946_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Closure(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Closure(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Closure(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ForEachExprWhere(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Closure(builtin);
}

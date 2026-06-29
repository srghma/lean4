// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.VarRename
// Imports: Init.Data.Array.QSort Std.Data.HashSet Init.Data.Hashable
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::Array::QSort::{
    initialize_Init_Data_Array_QSort, runtime_initialize_Init_Data_Array_QSort,
};
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::UInt::BasicAux::l_UInt64_ofNat___boxed;
use crate::r#gen::Init::Prelude::{
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqNat___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg;
use crate::r#gen::Std::Data::HashSet::{
    initialize_Std_Data_HashSet, runtime_initialize_Std_Data_HashSet,
};
use crate::ffi::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_nat_shiftr;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
pub static l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instAndThenVarCollector___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instAndThenVarCollector___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instAndThenVarCollector: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMapVars___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_collectMapVars___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMapVars___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value:
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
    m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instCoeFunVarRenameForallVar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkVarRename___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkVarRename___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkVarRename___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkVarRename___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkVarRename___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkVarRename___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(
    mut v_a_500_: *mut crate::leanh::LeanObject,
    mut v_x_501_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_502_: u8 = 0;
    let mut v_key_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_501_) == 0 {
                    v___x_502_ = 0;
                    return v___x_502_;
                } else {
                    v_key_503_ = crate::leanh::lean_ctor_get(v_x_501_, 0);
                    v_tail_504_ = crate::leanh::lean_ctor_get(v_x_501_, 2);
                    v___x_505_ = lean_nat_dec_eq(v_key_503_, v_a_500_);
                    if v___x_505_ == 0 {
                        v_x_501_ = v_tail_504_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_505_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg___boxed(
    mut v_a_507_: *mut crate::leanh::LeanObject,
    mut v_x_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_509_: u8 = 0;
    let mut v_r_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_507_, v_x_508_);
    crate::leanh::lean_dec(v_x_508_);
    crate::leanh::lean_dec(v_a_507_);
    v_r_510_ = crate::leanh::lean_box((v_res_509_) as usize);
    return v_r_510_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_511_: *mut crate::leanh::LeanObject,
    mut v_x_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u64 = 0;
    let mut v___x_521_: u64 = 0;
    let mut v___x_522_: u64 = 0;
    let mut v_fold_523_: u64 = 0;
    let mut v___x_524_: u64 = 0;
    let mut v___x_525_: u64 = 0;
    let mut v___x_526_: u64 = 0;
    let mut v___x_527_: usize = 0;
    let mut v___x_528_: usize = 0;
    let mut v___x_529_: usize = 0;
    let mut v___x_530_: usize = 0;
    let mut v___x_531_: usize = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_512_) == 0 {
                    return v_x_511_;
                } else {
                    v_key_513_ = crate::leanh::lean_ctor_get(v_x_512_, 0);
                    v_value_514_ = crate::leanh::lean_ctor_get(v_x_512_, 1);
                    v_tail_515_ = crate::leanh::lean_ctor_get(v_x_512_, 2);
                    v_isSharedCheck_538_ = (!crate::leanh::lean_is_exclusive(v_x_512_)) as u8;
                    if v_isSharedCheck_538_ == 0 {
                        v___x_517_ = v_x_512_;
                        v_isShared_518_ = v_isSharedCheck_538_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_515_);
                        crate::leanh::lean_inc(v_value_514_);
                        crate::leanh::lean_inc(v_key_513_);
                        crate::leanh::lean_dec(v_x_512_);
                        v___x_517_ = crate::leanh::lean_box(0);
                        v_isShared_518_ = v_isSharedCheck_538_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_519_ = lean_array_get_size(v_x_511_);
                v___x_520_ = lean_uint64_of_nat(v_key_513_);
                v___x_521_ = 32u64;
                v___x_522_ = lean_uint64_shift_right(v___x_520_, v___x_521_);
                v_fold_523_ = lean_uint64_xor(v___x_520_, v___x_522_);
                v___x_524_ = 16u64;
                v___x_525_ = lean_uint64_shift_right(v_fold_523_, v___x_524_);
                v___x_526_ = lean_uint64_xor(v_fold_523_, v___x_525_);
                v___x_527_ = lean_uint64_to_usize(v___x_526_);
                v___x_528_ = lean_usize_of_nat(v___x_519_);
                v___x_529_ = 1usize;
                v___x_530_ = lean_usize_sub(v___x_528_, v___x_529_);
                v___x_531_ = lean_usize_land(v___x_527_, v___x_530_);
                v___x_532_ = lean_array_uget_borrowed(v_x_511_, v___x_531_);
                crate::leanh::lean_inc(v___x_532_);
                if v_isShared_518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_517_, 2, v___x_532_);
                    v___x_534_ = v___x_517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_537_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_537_, 0, v_key_513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_537_, 1, v_value_514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_537_, 2, v___x_532_);
                    v___x_534_ = v_reuseFailAlloc_537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_535_ = lean_array_uset(v_x_511_, v___x_531_, v___x_534_);
                v_x_511_ = v___x_535_;
                v_x_512_ = v_tail_515_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(
    mut v_i_539_: *mut crate::leanh::LeanObject,
    mut v_source_540_: *mut crate::leanh::LeanObject,
    mut v_target_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    let mut v_es_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_542_ = lean_array_get_size(v_source_540_);
                v___x_543_ = lean_nat_dec_lt(v_i_539_, v___x_542_);
                if v___x_543_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_540_);
                    crate::leanh::lean_dec(v_i_539_);
                    return v_target_541_;
                } else {
                    v_es_544_ = lean_array_fget(v_source_540_, v_i_539_);
                    v___x_545_ = crate::leanh::lean_box(0);
                    v_source_546_ = lean_array_fset(v_source_540_, v_i_539_, v___x_545_);
                    v_target_547_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_541_, v_es_544_);
                    v___x_548_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_549_ = lean_nat_add(v_i_539_, v___x_548_);
                    crate::leanh::lean_dec(v_i_539_);
                    v_i_539_ = v___x_549_;
                    v_source_540_ = v_source_546_;
                    v_target_541_ = v_target_547_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(
    mut v_data_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = lean_array_get_size(v_data_551_);
    v___x_553_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_554_ = lean_nat_mul(v___x_552_, v___x_553_);
    v___x_555_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_556_ = crate::leanh::lean_box(0);
    v___x_557_ = lean_mk_array(v_nbuckets_554_, v___x_556_);
    v___x_558_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v___x_555_, v_data_551_, v___x_557_);
    return v___x_558_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(
    mut v_m_559_: *mut crate::leanh::LeanObject,
    mut v_a_560_: *mut crate::leanh::LeanObject,
    mut v_b_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u64 = 0;
    let mut v___x_566_: u64 = 0;
    let mut v___x_567_: u64 = 0;
    let mut v_fold_568_: u64 = 0;
    let mut v___x_569_: u64 = 0;
    let mut v___x_570_: u64 = 0;
    let mut v___x_571_: u64 = 0;
    let mut v___x_572_: usize = 0;
    let mut v___x_573_: usize = 0;
    let mut v___x_574_: usize = 0;
    let mut v___x_575_: usize = 0;
    let mut v___x_576_: usize = 0;
    let mut v_bkt_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: u8 = 0;
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_581_: u8 = 0;
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: u8 = 0;
    let mut v_val_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_unused_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_562_ = crate::leanh::lean_ctor_get(v_m_559_, 0);
                v_buckets_563_ = crate::leanh::lean_ctor_get(v_m_559_, 1);
                v___x_564_ = lean_array_get_size(v_buckets_563_);
                v___x_565_ = lean_uint64_of_nat(v_a_560_);
                v___x_566_ = 32u64;
                v___x_567_ = lean_uint64_shift_right(v___x_565_, v___x_566_);
                v_fold_568_ = lean_uint64_xor(v___x_565_, v___x_567_);
                v___x_569_ = 16u64;
                v___x_570_ = lean_uint64_shift_right(v_fold_568_, v___x_569_);
                v___x_571_ = lean_uint64_xor(v_fold_568_, v___x_570_);
                v___x_572_ = lean_uint64_to_usize(v___x_571_);
                v___x_573_ = lean_usize_of_nat(v___x_564_);
                v___x_574_ = 1usize;
                v___x_575_ = lean_usize_sub(v___x_573_, v___x_574_);
                v___x_576_ = lean_usize_land(v___x_572_, v___x_575_);
                v_bkt_577_ = lean_array_uget_borrowed(v_buckets_563_, v___x_576_);
                v___x_578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_560_, v_bkt_577_);
                if v___x_578_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_563_);
                    crate::leanh::lean_inc(v_size_562_);
                    v_isSharedCheck_599_ = (!crate::leanh::lean_is_exclusive(v_m_559_)) as u8;
                    if v_isSharedCheck_599_ == 0 {
                        v_unused_600_ = crate::leanh::lean_ctor_get(v_m_559_, 1);
                        crate::leanh::lean_dec(v_unused_600_);
                        v_unused_601_ = crate::leanh::lean_ctor_get(v_m_559_, 0);
                        crate::leanh::lean_dec(v_unused_601_);
                        v___x_580_ = v_m_559_;
                        v_isShared_581_ = v_isSharedCheck_599_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_559_);
                        v___x_580_ = crate::leanh::lean_box(0);
                        v_isShared_581_ = v_isSharedCheck_599_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_561_);
                    crate::leanh::lean_dec(v_a_560_);
                    return v_m_559_;
                }
            }
            1 => {
                v___x_582_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_583_ = lean_nat_add(v_size_562_, v___x_582_);
                crate::leanh::lean_dec(v_size_562_);
                crate::leanh::lean_inc(v_bkt_577_);
                v___x_584_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_584_, 0, v_a_560_);
                crate::leanh::lean_ctor_set(v___x_584_, 1, v_b_561_);
                crate::leanh::lean_ctor_set(v___x_584_, 2, v_bkt_577_);
                v_buckets_x27_585_ = lean_array_uset(v_buckets_563_, v___x_576_, v___x_584_);
                v___x_586_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_587_ = lean_nat_mul(v_size_x27_583_, v___x_586_);
                v___x_588_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_589_ = lean_nat_div(v___x_587_, v___x_588_);
                crate::leanh::lean_dec(v___x_587_);
                v___x_590_ = lean_array_get_size(v_buckets_x27_585_);
                v___x_591_ = lean_nat_dec_le(v___x_589_, v___x_590_);
                crate::leanh::lean_dec(v___x_589_);
                if v___x_591_ == 0 {
                    v_val_592_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_585_);
                    if v_isShared_581_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_580_, 1, v_val_592_);
                        crate::leanh::lean_ctor_set(v___x_580_, 0, v_size_x27_583_);
                        v___x_594_ = v___x_580_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 0, v_size_x27_583_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 1, v_val_592_);
                        v___x_594_ = v_reuseFailAlloc_595_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_581_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_580_, 1, v_buckets_x27_585_);
                        crate::leanh::lean_ctor_set(v___x_580_, 0, v_size_x27_583_);
                        v___x_597_ = v___x_580_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 0, v_size_x27_583_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 1, v_buckets_x27_585_);
                        v___x_597_ = v_reuseFailAlloc_598_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_594_;
            }
            3 => {
                return v___x_597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_collectVar(
    mut v_x_602_: *mut crate::leanh::LeanObject,
    mut v_x_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = crate::leanh::lean_box(0);
    v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_x_603_, v_x_602_, v___x_604_);
    return v___x_605_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0(
    mut v_00_u03b2_606_: *mut crate::leanh::LeanObject,
    mut v_m_607_: *mut crate::leanh::LeanObject,
    mut v_a_608_: *mut crate::leanh::LeanObject,
    mut v_b_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_m_607_, v_a_608_, v_b_609_);
    return v___x_610_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(
    mut v_00_u03b2_611_: *mut crate::leanh::LeanObject,
    mut v_a_612_: *mut crate::leanh::LeanObject,
    mut v_x_613_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_614_: u8 = 0;
    v___x_614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_612_, v_x_613_);
    return v___x_614_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_615_: *mut crate::leanh::LeanObject,
    mut v_a_616_: *mut crate::leanh::LeanObject,
    mut v_x_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_618_: u8 = 0;
    let mut v_r_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_618_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(v_00_u03b2_615_, v_a_616_, v_x_617_);
    crate::leanh::lean_dec(v_x_617_);
    crate::leanh::lean_dec(v_a_616_);
    v_r_619_ = crate::leanh::lean_box((v_res_618_) as usize);
    return v_r_619_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1(
    mut v_00_u03b2_620_: *mut crate::leanh::LeanObject,
    mut v_data_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_data_621_);
    return v___x_622_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2(
    mut v_00_u03b2_623_: *mut crate::leanh::LeanObject,
    mut v_i_624_: *mut crate::leanh::LeanObject,
    mut v_source_625_: *mut crate::leanh::LeanObject,
    mut v_target_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_627_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v_i_624_, v_source_625_, v_target_626_);
    return v___x_627_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_628_: *mut crate::leanh::LeanObject,
    mut v_x_629_: *mut crate::leanh::LeanObject,
    mut v_x_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_629_, v_x_630_);
    return v___x_631_;
}
pub unsafe fn l_Lean_Meta_Grind_instAndThenVarCollector___lam__0(
    mut v_c_u2081_632_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_633_: *mut crate::leanh::LeanObject,
    mut v_s_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_635_ = crate::leanh::lean_box(0);
    v___x_636_ = crate::leanh::lean_apply_1(v_c_u2081_632_, v_s_634_);
    v___x_637_ = crate::leanh::lean_apply_2(v_c_u2082_633_, v___x_635_, v___x_636_);
    return v___x_637_;
}
pub unsafe fn l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(
    mut v_k_640_: *mut crate::leanh::LeanObject,
    mut v_a_641_: *mut crate::leanh::LeanObject,
    mut v_b_642_: *mut crate::leanh::LeanObject,
    mut v_acc_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = crate::leanh::lean_apply_2(v_k_640_, v_a_641_, v_acc_643_);
    v___x_645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_645_, 0, v___x_644_);
    return v___x_645_;
}
pub unsafe fn l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed(
    mut v_k_646_: *mut crate::leanh::LeanObject,
    mut v_a_647_: *mut crate::leanh::LeanObject,
    mut v_b_648_: *mut crate::leanh::LeanObject,
    mut v_acc_649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_650_ = l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(
        v_k_646_, v_a_647_, v_b_648_, v_acc_649_,
    );
    crate::leanh::lean_dec(v_b_648_);
    return v_res_650_;
}
pub unsafe fn l_Lean_Meta_Grind_collectMapVars___redArg___lam__1(
    mut v___x_651_: *mut crate::leanh::LeanObject,
    mut v___f_652_: *mut crate::leanh::LeanObject,
    mut v_a_653_: *mut crate::leanh::LeanObject,
    mut v_x_654_: *mut crate::leanh::LeanObject,
    mut v___y_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_651_, v___f_652_, v_a_653_, v___y_655_);
    return v___x_656_;
}
pub unsafe fn l_Lean_Meta_Grind_collectMapVars___redArg(
    mut v_m_676_: *mut crate::leanh::LeanObject,
    mut v_k_677_: *mut crate::leanh::LeanObject,
    mut v_s_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_683_: usize = 0;
    let mut v___x_684_: usize = 0;
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = l_Lean_Meta_Grind_collectMapVars___redArg___closed__9;
    v_buckets_680_ = crate::leanh::lean_ctor_get(v_m_676_, 1);
    crate::leanh::lean_inc_ref(v_buckets_680_);
    crate::leanh::lean_dec_ref(v_m_676_);
    v___f_681_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_681_, 0, v_k_677_);
    v___f_682_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_collectMapVars___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_682_, 0, v___x_679_);
    crate::leanh::lean_closure_set(v___f_682_, 1, v___f_681_);
    v_sz_683_ = lean_array_size(v_buckets_680_);
    v___x_684_ = 0usize;
    v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_679_,
        v_buckets_680_,
        v___f_682_,
        v_sz_683_,
        v___x_684_,
        v_s_678_,
    );
    return v___x_685_;
}
pub unsafe fn l_Lean_Meta_Grind_collectMapVars(
    mut v_00_u03b1_686_: *mut crate::leanh::LeanObject,
    mut v_Expr_687_: *mut crate::leanh::LeanObject,
    mut v_x_688_: *mut crate::leanh::LeanObject,
    mut v_x_689_: *mut crate::leanh::LeanObject,
    mut v_m_690_: *mut crate::leanh::LeanObject,
    mut v_k_691_: *mut crate::leanh::LeanObject,
    mut v_s_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = l_Lean_Meta_Grind_collectMapVars___redArg(v_m_690_, v_k_691_, v_s_692_);
    return v___x_693_;
}
pub unsafe fn l_Lean_Meta_Grind_collectMapVars___boxed(
    mut v_00_u03b1_694_: *mut crate::leanh::LeanObject,
    mut v_Expr_695_: *mut crate::leanh::LeanObject,
    mut v_x_696_: *mut crate::leanh::LeanObject,
    mut v_x_697_: *mut crate::leanh::LeanObject,
    mut v_m_698_: *mut crate::leanh::LeanObject,
    mut v_k_699_: *mut crate::leanh::LeanObject,
    mut v_s_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lean_Meta_Grind_collectMapVars(
        v_00_u03b1_694_,
        v_Expr_695_,
        v_x_696_,
        v_x_697_,
        v_m_698_,
        v_k_699_,
        v_s_700_,
    );
    crate::leanh::lean_dec_ref(v_x_697_);
    crate::leanh::lean_dec_ref(v_x_696_);
    return v_res_701_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(
    mut v_x_702_: *mut crate::leanh::LeanObject,
    mut v_x_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_703_) == 0 {
                    return v_x_702_;
                } else {
                    v_key_704_ = crate::leanh::lean_ctor_get(v_x_703_, 0);
                    crate::leanh::lean_inc(v_key_704_);
                    v_tail_705_ = crate::leanh::lean_ctor_get(v_x_703_, 2);
                    crate::leanh::lean_inc(v_tail_705_);
                    crate::leanh::lean_dec_ref_known(v_x_703_, 3);
                    v___x_706_ = lean_array_push(v_x_702_, v_key_704_);
                    v_x_702_ = v___x_706_;
                    v_x_703_ = v_tail_705_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(
    mut v_as_708_: *mut crate::leanh::LeanObject,
    mut v_i_709_: usize,
    mut v_stop_710_: usize,
    mut v_b_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_712_: u8 = 0;
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_712_ = lean_usize_dec_eq(v_i_709_, v_stop_710_);
                if v___x_712_ == 0 {
                    v___x_713_ = lean_array_uget_borrowed(v_as_708_, v_i_709_);
                    crate::leanh::lean_inc(v___x_713_);
                    v___x_714_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(v_b_711_, v___x_713_);
                    v___x_715_ = 1usize;
                    v___x_716_ = lean_usize_add(v_i_709_, v___x_715_);
                    v_i_709_ = v___x_716_;
                    v_b_711_ = v___x_714_;
                    state = 0;
                    continue;
                } else {
                    return v_b_711_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2___boxed(
    mut v_as_718_: *mut crate::leanh::LeanObject,
    mut v_i_719_: *mut crate::leanh::LeanObject,
    mut v_stop_720_: *mut crate::leanh::LeanObject,
    mut v_b_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_722_: usize = 0;
    let mut v_stop_boxed_723_: usize = 0;
    let mut v_res_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_722_ = crate::leanh::lean_unbox_usize(v_i_719_);
    crate::leanh::lean_dec(v_i_719_);
    v_stop_boxed_723_ = crate::leanh::lean_unbox_usize(v_stop_720_);
    crate::leanh::lean_dec(v_stop_720_);
    v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_as_718_, v_i_boxed_722_, v_stop_boxed_723_, v_b_721_);
    crate::leanh::lean_dec_ref(v_as_718_);
    return v_res_724_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(
    mut v_hi_725_: *mut crate::leanh::LeanObject,
    mut v_pivot_726_: *mut crate::leanh::LeanObject,
    mut v_as_727_: *mut crate::leanh::LeanObject,
    mut v_i_728_: *mut crate::leanh::LeanObject,
    mut v_k_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_730_: u8 = 0;
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_730_ = lean_nat_dec_lt(v_k_729_, v_hi_725_);
                if v___x_730_ == 0 {
                    crate::leanh::lean_dec(v_k_729_);
                    v___x_731_ = lean_array_fswap(v_as_727_, v_i_728_, v_hi_725_);
                    v___x_732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_732_, 0, v_i_728_);
                    crate::leanh::lean_ctor_set(v___x_732_, 1, v___x_731_);
                    return v___x_732_;
                } else {
                    v___x_733_ = lean_array_fget_borrowed(v_as_727_, v_k_729_);
                    v___x_734_ = lean_nat_dec_lt(v___x_733_, v_pivot_726_);
                    if v___x_734_ == 0 {
                        v___x_735_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_736_ = lean_nat_add(v_k_729_, v___x_735_);
                        crate::leanh::lean_dec(v_k_729_);
                        v_k_729_ = v___x_736_;
                        state = 0;
                        continue;
                    } else {
                        v___x_738_ = lean_array_fswap(v_as_727_, v_i_728_, v_k_729_);
                        v___x_739_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_740_ = lean_nat_add(v_i_728_, v___x_739_);
                        crate::leanh::lean_dec(v_i_728_);
                        v___x_741_ = lean_nat_add(v_k_729_, v___x_739_);
                        crate::leanh::lean_dec(v_k_729_);
                        v_as_727_ = v___x_738_;
                        v_i_728_ = v___x_740_;
                        v_k_729_ = v___x_741_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg___boxed(
    mut v_hi_743_: *mut crate::leanh::LeanObject,
    mut v_pivot_744_: *mut crate::leanh::LeanObject,
    mut v_as_745_: *mut crate::leanh::LeanObject,
    mut v_i_746_: *mut crate::leanh::LeanObject,
    mut v_k_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_743_, v_pivot_744_, v_as_745_, v_i_746_, v_k_747_);
    crate::leanh::lean_dec(v_pivot_744_);
    crate::leanh::lean_dec(v_hi_743_);
    return v_res_748_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(
    mut v_n_749_: *mut crate::leanh::LeanObject,
    mut v_as_750_: *mut crate::leanh::LeanObject,
    mut v_lo_751_: *mut crate::leanh::LeanObject,
    mut v_hi_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u8 = 0;
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: u8 = 0;
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: u8 = 0;
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u8 = 0;
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_764_ = lean_nat_dec_lt(v_lo_751_, v_hi_752_);
                if v___x_764_ == 0 {
                    crate::leanh::lean_dec(v_lo_751_);
                    return v_as_750_;
                } else {
                    v___x_765_ = lean_nat_add(v_lo_751_, v_hi_752_);
                    v___x_766_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_767_ = lean_nat_shiftr(v___x_765_, v___x_766_);
                    crate::leanh::lean_dec(v___x_765_);
                    v___x_780_ = lean_array_fget_borrowed(v_as_750_, v_mid_767_);
                    v___x_781_ = lean_array_fget_borrowed(v_as_750_, v_lo_751_);
                    v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
                    if v___x_782_ == 0 {
                        v___y_775_ = v_as_750_;
                        state = 3;
                        continue;
                    } else {
                        v___x_783_ = lean_array_fswap(v_as_750_, v_lo_751_, v_mid_767_);
                        v___y_775_ = v___x_783_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_755_ = lean_array_fget(v___y_754_, v_hi_752_);
                crate::leanh::lean_inc_n(v_lo_751_, 2);
                v___x_756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_752_, v_pivot_755_, v___y_754_, v_lo_751_, v_lo_751_);
                crate::leanh::lean_dec(v_pivot_755_);
                v_fst_757_ = crate::leanh::lean_ctor_get(v___x_756_, 0);
                crate::leanh::lean_inc(v_fst_757_);
                v_snd_758_ = crate::leanh::lean_ctor_get(v___x_756_, 1);
                crate::leanh::lean_inc(v_snd_758_);
                crate::leanh::lean_dec_ref(v___x_756_);
                v___x_759_ = lean_nat_dec_le(v_hi_752_, v_fst_757_);
                if v___x_759_ == 0 {
                    v___x_760_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_749_, v_snd_758_, v_lo_751_, v_fst_757_);
                    v___x_761_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_762_ = lean_nat_add(v_fst_757_, v___x_761_);
                    crate::leanh::lean_dec(v_fst_757_);
                    v_as_750_ = v___x_760_;
                    v_lo_751_ = v___x_762_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_757_);
                    crate::leanh::lean_dec(v_lo_751_);
                    return v_snd_758_;
                }
            }
            2 => {
                v___x_770_ = lean_array_fget_borrowed(v___y_769_, v_mid_767_);
                v___x_771_ = lean_array_fget_borrowed(v___y_769_, v_hi_752_);
                v___x_772_ = lean_nat_dec_lt(v___x_770_, v___x_771_);
                if v___x_772_ == 0 {
                    crate::leanh::lean_dec(v_mid_767_);
                    v___y_754_ = v___y_769_;
                    state = 1;
                    continue;
                } else {
                    v___x_773_ = lean_array_fswap(v___y_769_, v_mid_767_, v_hi_752_);
                    crate::leanh::lean_dec(v_mid_767_);
                    v___y_754_ = v___x_773_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_776_ = lean_array_fget_borrowed(v___y_775_, v_hi_752_);
                v___x_777_ = lean_array_fget_borrowed(v___y_775_, v_lo_751_);
                v___x_778_ = lean_nat_dec_lt(v___x_776_, v___x_777_);
                if v___x_778_ == 0 {
                    v___y_769_ = v___y_775_;
                    state = 2;
                    continue;
                } else {
                    v___x_779_ = lean_array_fswap(v___y_775_, v_lo_751_, v_hi_752_);
                    v___y_769_ = v___x_779_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___boxed(
    mut v_n_784_: *mut crate::leanh::LeanObject,
    mut v_as_785_: *mut crate::leanh::LeanObject,
    mut v_lo_786_: *mut crate::leanh::LeanObject,
    mut v_hi_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_784_, v_as_785_, v_lo_786_, v_hi_787_);
    crate::leanh::lean_dec(v_hi_787_);
    crate::leanh::lean_dec(v_n_784_);
    return v_res_788_;
}
pub unsafe fn l_Lean_Meta_Grind_FoundVars_toArray(
    mut v_s_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: u8 = 0;
    let mut v_size_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: u8 = 0;
    let mut v___x_813_: usize = 0;
    let mut v___x_814_: usize = 0;
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: usize = 0;
    let mut v___x_817_: usize = 0;
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_806_ = crate::leanh::lean_ctor_get(v_s_789_, 0);
                v_buckets_807_ = crate::leanh::lean_ctor_get(v_s_789_, 1);
                v___x_808_ = lean_mk_empty_array_with_capacity(v_size_806_);
                v___x_809_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_810_ = lean_array_get_size(v_buckets_807_);
                v___x_811_ = lean_nat_dec_lt(v___x_809_, v___x_810_);
                if v___x_811_ == 0 {
                    v___y_799_ = v___x_808_;
                    state = 2;
                    continue;
                } else {
                    v___x_812_ = lean_nat_dec_le(v___x_810_, v___x_810_);
                    if v___x_812_ == 0 {
                        if v___x_811_ == 0 {
                            v___y_799_ = v___x_808_;
                            state = 2;
                            continue;
                        } else {
                            v___x_813_ = 0usize;
                            v___x_814_ = lean_usize_of_nat(v___x_810_);
                            v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_807_, v___x_813_, v___x_814_, v___x_808_);
                            v___y_799_ = v___x_815_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_816_ = 0usize;
                        v___x_817_ = lean_usize_of_nat(v___x_810_);
                        v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_807_, v___x_816_, v___x_817_, v___x_808_);
                        v___y_799_ = v___x_818_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_795_ = lean_nat_dec_le(v___y_794_, v___y_793_);
                if v___x_795_ == 0 {
                    crate::leanh::lean_dec(v___y_793_);
                    crate::leanh::lean_inc(v___y_794_);
                    v___x_796_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_791_, v___y_792_, v___y_794_, v___y_794_);
                    crate::leanh::lean_dec(v___y_794_);
                    crate::leanh::lean_dec(v___y_791_);
                    return v___x_796_;
                } else {
                    v___x_797_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_791_, v___y_792_, v___y_794_, v___y_793_);
                    crate::leanh::lean_dec(v___y_793_);
                    crate::leanh::lean_dec(v___y_791_);
                    return v___x_797_;
                }
            }
            2 => {
                v___x_800_ = lean_array_get_size(v___y_799_);
                v___x_801_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_802_ = lean_nat_dec_eq(v___x_800_, v___x_801_);
                if v___x_802_ == 0 {
                    v___x_803_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_804_ = lean_nat_sub(v___x_800_, v___x_803_);
                    v___x_805_ = lean_nat_dec_le(v___x_801_, v___x_804_);
                    if v___x_805_ == 0 {
                        crate::leanh::lean_inc(v___x_804_);
                        v___y_791_ = v___x_800_;
                        v___y_792_ = v___y_799_;
                        v___y_793_ = v___x_804_;
                        v___y_794_ = v___x_804_;
                        state = 1;
                        continue;
                    } else {
                        v___y_791_ = v___x_800_;
                        v___y_792_ = v___y_799_;
                        v___y_793_ = v___x_804_;
                        v___y_794_ = v___x_801_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_799_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_FoundVars_toArray___boxed(
    mut v_s_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l_Lean_Meta_Grind_FoundVars_toArray(v_s_819_);
    crate::leanh::lean_dec_ref(v_s_819_);
    return v_res_820_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(
    mut v_n_821_: *mut crate::leanh::LeanObject,
    mut v_as_822_: *mut crate::leanh::LeanObject,
    mut v_lo_823_: *mut crate::leanh::LeanObject,
    mut v_hi_824_: *mut crate::leanh::LeanObject,
    mut v_w_825_: *mut crate::leanh::LeanObject,
    mut v_hlo_826_: *mut crate::leanh::LeanObject,
    mut v_hhi_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_821_, v_as_822_, v_lo_823_, v_hi_824_);
    return v___x_828_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(
    mut v_n_829_: *mut crate::leanh::LeanObject,
    mut v_as_830_: *mut crate::leanh::LeanObject,
    mut v_lo_831_: *mut crate::leanh::LeanObject,
    mut v_hi_832_: *mut crate::leanh::LeanObject,
    mut v_w_833_: *mut crate::leanh::LeanObject,
    mut v_hlo_834_: *mut crate::leanh::LeanObject,
    mut v_hhi_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(v_n_829_, v_as_830_, v_lo_831_, v_hi_832_, v_w_833_, v_hlo_834_, v_hhi_835_);
    crate::leanh::lean_dec(v_hi_832_);
    crate::leanh::lean_dec(v_n_829_);
    return v_res_836_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(
    mut v_n_837_: *mut crate::leanh::LeanObject,
    mut v_lo_838_: *mut crate::leanh::LeanObject,
    mut v_hi_839_: *mut crate::leanh::LeanObject,
    mut v_hhi_840_: *mut crate::leanh::LeanObject,
    mut v_pivot_841_: *mut crate::leanh::LeanObject,
    mut v_as_842_: *mut crate::leanh::LeanObject,
    mut v_i_843_: *mut crate::leanh::LeanObject,
    mut v_k_844_: *mut crate::leanh::LeanObject,
    mut v_ilo_845_: *mut crate::leanh::LeanObject,
    mut v_ik_846_: *mut crate::leanh::LeanObject,
    mut v_w_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_839_, v_pivot_841_, v_as_842_, v_i_843_, v_k_844_);
    return v___x_848_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___boxed(
    mut v_n_849_: *mut crate::leanh::LeanObject,
    mut v_lo_850_: *mut crate::leanh::LeanObject,
    mut v_hi_851_: *mut crate::leanh::LeanObject,
    mut v_hhi_852_: *mut crate::leanh::LeanObject,
    mut v_pivot_853_: *mut crate::leanh::LeanObject,
    mut v_as_854_: *mut crate::leanh::LeanObject,
    mut v_i_855_: *mut crate::leanh::LeanObject,
    mut v_k_856_: *mut crate::leanh::LeanObject,
    mut v_ilo_857_: *mut crate::leanh::LeanObject,
    mut v_ik_858_: *mut crate::leanh::LeanObject,
    mut v_w_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(v_n_849_, v_lo_850_, v_hi_851_, v_hhi_852_, v_pivot_853_, v_as_854_, v_i_855_, v_k_856_, v_ilo_857_, v_ik_858_, v_w_859_);
    crate::leanh::lean_dec(v_pivot_853_);
    crate::leanh::lean_dec(v_hi_851_);
    crate::leanh::lean_dec(v_lo_850_);
    crate::leanh::lean_dec(v_n_849_);
    return v_res_860_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_862_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_862_, 0, v___x_861_);
    return v___f_862_;
}
pub unsafe fn l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(
    mut v___f_863_: *mut crate::leanh::LeanObject,
    mut v_s_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_866_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0,
    );
    v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_866_, v___f_863_, v_s_864_, v_x_865_,
    );
    if crate::leanh::lean_obj_tag(v___x_867_) == 0 {
        let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_868_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_868_;
    } else {
        let mut v_val_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_869_ = crate::leanh::lean_ctor_get(v___x_867_, 0);
        crate::leanh::lean_inc(v_val_869_);
        crate::leanh::lean_dec_ref_known(v___x_867_, 1);
        return v_val_869_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed(
    mut v___f_870_: *mut crate::leanh::LeanObject,
    mut v_s_871_: *mut crate::leanh::LeanObject,
    mut v_x_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ =
        l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(v___f_870_, v_s_871_, v_x_872_);
    crate::leanh::lean_dec_ref(v_s_871_);
    return v_res_873_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(
    mut v_a_878_: *mut crate::leanh::LeanObject,
    mut v_b_879_: *mut crate::leanh::LeanObject,
    mut v_x_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_886_: u8 = 0;
    let mut v___x_887_: u8 = 0;
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_880_) == 0 {
                    crate::leanh::lean_dec(v_b_879_);
                    crate::leanh::lean_dec(v_a_878_);
                    return v_x_880_;
                } else {
                    v_key_881_ = crate::leanh::lean_ctor_get(v_x_880_, 0);
                    v_value_882_ = crate::leanh::lean_ctor_get(v_x_880_, 1);
                    v_tail_883_ = crate::leanh::lean_ctor_get(v_x_880_, 2);
                    v_isSharedCheck_895_ = (!crate::leanh::lean_is_exclusive(v_x_880_)) as u8;
                    if v_isSharedCheck_895_ == 0 {
                        v___x_885_ = v_x_880_;
                        v_isShared_886_ = v_isSharedCheck_895_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_883_);
                        crate::leanh::lean_inc(v_value_882_);
                        crate::leanh::lean_inc(v_key_881_);
                        crate::leanh::lean_dec(v_x_880_);
                        v___x_885_ = crate::leanh::lean_box(0);
                        v_isShared_886_ = v_isSharedCheck_895_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_887_ = lean_nat_dec_eq(v_key_881_, v_a_878_);
                if v___x_887_ == 0 {
                    v___x_888_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_878_, v_b_879_, v_tail_883_);
                    if v_isShared_886_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_885_, 2, v___x_888_);
                        v___x_890_ = v___x_885_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_891_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 0, v_key_881_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 1, v_value_882_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 2, v___x_888_);
                        v___x_890_ = v_reuseFailAlloc_891_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_882_);
                    crate::leanh::lean_dec(v_key_881_);
                    if v_isShared_886_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_885_, 1, v_b_879_);
                        crate::leanh::lean_ctor_set(v___x_885_, 0, v_a_878_);
                        v___x_893_ = v___x_885_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_894_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_878_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 1, v_b_879_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 2, v_tail_883_);
                        v___x_893_ = v_reuseFailAlloc_894_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_890_;
            }
            3 => {
                return v___x_893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(
    mut v_m_896_: *mut crate::leanh::LeanObject,
    mut v_a_897_: *mut crate::leanh::LeanObject,
    mut v_b_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u64 = 0;
    let mut v___x_906_: u64 = 0;
    let mut v___x_907_: u64 = 0;
    let mut v_fold_908_: u64 = 0;
    let mut v___x_909_: u64 = 0;
    let mut v___x_910_: u64 = 0;
    let mut v___x_911_: u64 = 0;
    let mut v___x_912_: usize = 0;
    let mut v___x_913_: usize = 0;
    let mut v___x_914_: usize = 0;
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: usize = 0;
    let mut v_bkt_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: u8 = 0;
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: u8 = 0;
    let mut v_val_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_899_ = crate::leanh::lean_ctor_get(v_m_896_, 0);
                v_buckets_900_ = crate::leanh::lean_ctor_get(v_m_896_, 1);
                v_isSharedCheck_943_ = (!crate::leanh::lean_is_exclusive(v_m_896_)) as u8;
                if v_isSharedCheck_943_ == 0 {
                    v___x_902_ = v_m_896_;
                    v_isShared_903_ = v_isSharedCheck_943_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_900_);
                    crate::leanh::lean_inc(v_size_899_);
                    crate::leanh::lean_dec(v_m_896_);
                    v___x_902_ = crate::leanh::lean_box(0);
                    v_isShared_903_ = v_isSharedCheck_943_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_904_ = lean_array_get_size(v_buckets_900_);
                v___x_905_ = lean_uint64_of_nat(v_a_897_);
                v___x_906_ = 32u64;
                v___x_907_ = lean_uint64_shift_right(v___x_905_, v___x_906_);
                v_fold_908_ = lean_uint64_xor(v___x_905_, v___x_907_);
                v___x_909_ = 16u64;
                v___x_910_ = lean_uint64_shift_right(v_fold_908_, v___x_909_);
                v___x_911_ = lean_uint64_xor(v_fold_908_, v___x_910_);
                v___x_912_ = lean_uint64_to_usize(v___x_911_);
                v___x_913_ = lean_usize_of_nat(v___x_904_);
                v___x_914_ = 1usize;
                v___x_915_ = lean_usize_sub(v___x_913_, v___x_914_);
                v___x_916_ = lean_usize_land(v___x_912_, v___x_915_);
                v_bkt_917_ = lean_array_uget_borrowed(v_buckets_900_, v___x_916_);
                v___x_918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_897_, v_bkt_917_);
                if v___x_918_ == 0 {
                    v___x_919_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_920_ = lean_nat_add(v_size_899_, v___x_919_);
                    crate::leanh::lean_dec(v_size_899_);
                    crate::leanh::lean_inc(v_bkt_917_);
                    v___x_921_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_921_, 0, v_a_897_);
                    crate::leanh::lean_ctor_set(v___x_921_, 1, v_b_898_);
                    crate::leanh::lean_ctor_set(v___x_921_, 2, v_bkt_917_);
                    v_buckets_x27_922_ = lean_array_uset(v_buckets_900_, v___x_916_, v___x_921_);
                    v___x_923_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_924_ = lean_nat_mul(v_size_x27_920_, v___x_923_);
                    v___x_925_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_926_ = lean_nat_div(v___x_924_, v___x_925_);
                    crate::leanh::lean_dec(v___x_924_);
                    v___x_927_ = lean_array_get_size(v_buckets_x27_922_);
                    v___x_928_ = lean_nat_dec_le(v___x_926_, v___x_927_);
                    crate::leanh::lean_dec(v___x_926_);
                    if v___x_928_ == 0 {
                        v_val_929_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_922_);
                        if v_isShared_903_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_902_, 1, v_val_929_);
                            crate::leanh::lean_ctor_set(v___x_902_, 0, v_size_x27_920_);
                            v___x_931_ = v___x_902_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v_size_x27_920_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 1, v_val_929_);
                            v___x_931_ = v_reuseFailAlloc_932_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_903_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_902_, 1, v_buckets_x27_922_);
                            crate::leanh::lean_ctor_set(v___x_902_, 0, v_size_x27_920_);
                            v___x_934_ = v___x_902_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_935_, 0, v_size_x27_920_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_935_,
                                1,
                                v_buckets_x27_922_,
                            );
                            v___x_934_ = v_reuseFailAlloc_935_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_917_);
                    v___x_936_ = crate::leanh::lean_box(0);
                    v_buckets_x27_937_ = lean_array_uset(v_buckets_900_, v___x_916_, v___x_936_);
                    v___x_938_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_897_, v_b_898_, v_bkt_917_);
                    v___x_939_ = lean_array_uset(v_buckets_x27_937_, v___x_916_, v___x_938_);
                    if v_isShared_903_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_902_, 1, v___x_939_);
                        v___x_941_ = v___x_902_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_942_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_942_, 0, v_size_899_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_939_);
                        v___x_941_ = v_reuseFailAlloc_942_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_931_;
            }
            3 => {
                return v___x_934_;
            }
            4 => {
                return v___x_941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(
    mut v_as_944_: *mut crate::leanh::LeanObject,
    mut v_sz_945_: usize,
    mut v_i_946_: usize,
    mut v_b_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_948_: u8 = 0;
    let mut v_fst_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_953_: u8 = 0;
    let mut v_a_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: usize = 0;
    let mut v___x_961_: usize = 0;
    let mut v_reuseFailAlloc_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_948_ = lean_usize_dec_lt(v_i_946_, v_sz_945_);
                if v___x_948_ == 0 {
                    return v_b_947_;
                } else {
                    v_fst_949_ = crate::leanh::lean_ctor_get(v_b_947_, 0);
                    v_snd_950_ = crate::leanh::lean_ctor_get(v_b_947_, 1);
                    v_isSharedCheck_964_ = (!crate::leanh::lean_is_exclusive(v_b_947_)) as u8;
                    if v_isSharedCheck_964_ == 0 {
                        v___x_952_ = v_b_947_;
                        v_isShared_953_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_950_);
                        crate::leanh::lean_inc(v_fst_949_);
                        crate::leanh::lean_dec(v_b_947_);
                        v___x_952_ = crate::leanh::lean_box(0);
                        v_isShared_953_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_954_ = lean_array_uget_borrowed(v_as_944_, v_i_946_);
                crate::leanh::lean_inc(v_snd_950_);
                crate::leanh::lean_inc(v_a_954_);
                v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_fst_949_, v_a_954_, v_snd_950_);
                v___x_956_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_957_ = lean_nat_add(v_snd_950_, v___x_956_);
                crate::leanh::lean_dec(v_snd_950_);
                if v_isShared_953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_952_, 1, v___x_957_);
                    crate::leanh::lean_ctor_set(v___x_952_, 0, v___x_955_);
                    v___x_959_ = v___x_952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_957_);
                    v___x_959_ = v_reuseFailAlloc_963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_960_ = 1usize;
                v___x_961_ = lean_usize_add(v_i_946_, v___x_960_);
                v_i_946_ = v___x_961_;
                v_b_947_ = v___x_959_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1___boxed(
    mut v_as_965_: *mut crate::leanh::LeanObject,
    mut v_sz_966_: *mut crate::leanh::LeanObject,
    mut v_i_967_: *mut crate::leanh::LeanObject,
    mut v_b_968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_969_: usize = 0;
    let mut v_i_boxed_970_: usize = 0;
    let mut v_res_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_969_ = crate::leanh::lean_unbox_usize(v_sz_966_);
    crate::leanh::lean_dec(v_sz_966_);
    v_i_boxed_970_ = crate::leanh::lean_unbox_usize(v_i_967_);
    crate::leanh::lean_dec(v_i_967_);
    v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_as_965_, v_sz_boxed_969_, v_i_boxed_970_, v_b_968_);
    crate::leanh::lean_dec_ref(v_as_965_);
    return v_res_971_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkVarRename___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = crate::leanh::lean_box(0);
    v___x_973_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_974_ = lean_mk_array(v___x_973_, v___x_972_);
    return v___x_974_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkVarRename___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old2new_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_975_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkVarRename___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkVarRename___closed__0_once),
        _init_l_Lean_Meta_Grind_mkVarRename___closed__0,
    );
    v___x_976_ = crate::leanh::lean_unsigned_to_nat(0);
    v_old2new_977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_old2new_977_, 0, v___x_976_);
    crate::leanh::lean_ctor_set(v_old2new_977_, 1, v___x_975_);
    return v_old2new_977_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkVarRename___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old2new_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = crate::leanh::lean_unsigned_to_nat(0);
    v_old2new_979_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkVarRename___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkVarRename___closed__1_once),
        _init_l_Lean_Meta_Grind_mkVarRename___closed__1,
    );
    v___x_980_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_980_, 0, v_old2new_979_);
    crate::leanh::lean_ctor_set(v___x_980_, 1, v___x_978_);
    return v___x_980_;
}
pub unsafe fn l_Lean_Meta_Grind_mkVarRename(
    mut v_new2old_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_983_: usize = 0;
    let mut v___x_984_: usize = 0;
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkVarRename___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkVarRename___closed__2_once),
        _init_l_Lean_Meta_Grind_mkVarRename___closed__2,
    );
    v_sz_983_ = lean_array_size(v_new2old_981_);
    v___x_984_ = 0usize;
    v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_new2old_981_, v_sz_983_, v___x_984_, v___x_982_);
    v_fst_986_ = crate::leanh::lean_ctor_get(v___x_985_, 0);
    crate::leanh::lean_inc(v_fst_986_);
    crate::leanh::lean_dec_ref(v___x_985_);
    return v_fst_986_;
}
pub unsafe fn l_Lean_Meta_Grind_mkVarRename___boxed(
    mut v_new2old_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_Lean_Meta_Grind_mkVarRename(v_new2old_987_);
    crate::leanh::lean_dec_ref(v_new2old_987_);
    return v_res_988_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0(
    mut v_00_u03b2_989_: *mut crate::leanh::LeanObject,
    mut v_m_990_: *mut crate::leanh::LeanObject,
    mut v_a_991_: *mut crate::leanh::LeanObject,
    mut v_b_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_m_990_, v_a_991_, v_b_992_);
    return v___x_993_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0(
    mut v_00_u03b2_994_: *mut crate::leanh::LeanObject,
    mut v_a_995_: *mut crate::leanh::LeanObject,
    mut v_b_996_: *mut crate::leanh::LeanObject,
    mut v_x_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_995_, v_b_996_, v_x_997_);
    return v___x_998_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_QSort(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_VarRename(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_VarRename(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_QSort(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
}

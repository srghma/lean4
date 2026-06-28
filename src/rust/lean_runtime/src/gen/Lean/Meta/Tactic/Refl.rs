// Lean compiler output
// Module: Lean.Meta.Tactic.Refl
// Imports: Lean.Meta.Reduce Lean.Meta.Tactic.Apply
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshLevelMVar,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::Reduce::{
    initialize_Lean_Meta_Reduce, runtime_initialize_Lean_Meta_Reduce,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::{
    initialize_Lean_Meta_Tactic_Apply, l_Lean_MVarId_apply,
    runtime_initialize_Lean_Meta_Tactic_Apply,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getType_x27, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_refl___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_MVarId_refl___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_refl___lam__0___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [114, 102, 108, 0],
    };
static mut l_Lean_MVarId_refl___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_refl___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17342663138809293389 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_refl___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_refl___lam__0___closed__3_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 113, 117, 97, 108, 105, 116, 121, 32, 108, 104, 115, 0],
    };
static mut l_Lean_MVarId_refl___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_refl___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_refl___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_refl___lam__0___closed__5_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
            97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 114, 104, 115, 0,
        ],
    };
static mut l_Lean_MVarId_refl___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_refl___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_refl___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_refl___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_refl___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_refl___lam__0___closed__8_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            101, 113, 117, 97, 108, 105, 116, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_MVarId_refl___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_refl___lam__0___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_refl___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_refl___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [114, 101, 102, 108, 0],
    };
static mut l_Lean_MVarId_refl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_refl___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_refl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16107927835509634124 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_refl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_refl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_heqOfEq___lam__0___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [104, 101, 113, 95, 111, 102, 95, 101, 113, 0],
    };
static mut l_Lean_MVarId_heqOfEq___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_heqOfEq___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_heqOfEq___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_heqOfEq___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9778815885342864204 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_heqOfEq___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_heqOfEq___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_heqOfEq___lam__0___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [16777472 as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_MVarId_heqOfEq___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_heqOfEq___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_eqOfHEq___lam__0___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [101, 113, 95, 111, 102, 95, 104, 101, 113, 0],
    };
static mut l_Lean_MVarId_eqOfHEq___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_eqOfHEq___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_eqOfHEq___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_eqOfHEq___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12895495887625141542 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_eqOfHEq___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_eqOfHEq___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_hrefl___lam__0___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [72, 69, 113, 0],
    };
static mut l_Lean_MVarId_hrefl___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hrefl___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_hrefl___lam__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_hrefl___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13589827700912665667 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_hrefl___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_hrefl___lam__0___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_refl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2990354745633524404 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_hrefl___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hrefl___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_hrefl___lam__1___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [104, 114, 101, 102, 108, 0],
    };
static mut l_Lean_MVarId_hrefl___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hrefl___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_hrefl___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_hrefl___lam__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6950870149023334600 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_hrefl___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hrefl___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(
    mut v_e_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_881_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_887_: u8 = 0;
    let mut v_unused_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_867_ = l_Lean_Expr_hasMVar(v_e_864_);
                if v___x_867_ == 0 {
                    v___x_868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_868_, 0, v_e_864_);
                    return v___x_868_;
                } else {
                    v___x_869_ = lean_st_ref_get(v___y_865_);
                    v_mctx_870_ = crate::leanh::lean_ctor_get(v___x_869_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_870_);
                    crate::leanh::lean_dec(v___x_869_);
                    v___x_871_ = l_Lean_instantiateMVarsCore(v_mctx_870_, v_e_864_);
                    v_fst_872_ = crate::leanh::lean_ctor_get(v___x_871_, 0);
                    crate::leanh::lean_inc(v_fst_872_);
                    v_snd_873_ = crate::leanh::lean_ctor_get(v___x_871_, 1);
                    crate::leanh::lean_inc(v_snd_873_);
                    crate::leanh::lean_dec_ref(v___x_871_);
                    v___x_874_ = lean_st_ref_take(v___y_865_);
                    v_cache_875_ = crate::leanh::lean_ctor_get(v___x_874_, 1);
                    v_zetaDeltaFVarIds_876_ = crate::leanh::lean_ctor_get(v___x_874_, 2);
                    v_postponed_877_ = crate::leanh::lean_ctor_get(v___x_874_, 3);
                    v_diag_878_ = crate::leanh::lean_ctor_get(v___x_874_, 4);
                    v_isSharedCheck_887_ = (!crate::leanh::lean_is_exclusive(v___x_874_)) as u8;
                    if v_isSharedCheck_887_ == 0 {
                        v_unused_888_ = crate::leanh::lean_ctor_get(v___x_874_, 0);
                        crate::leanh::lean_dec(v_unused_888_);
                        v___x_880_ = v___x_874_;
                        v_isShared_881_ = v_isSharedCheck_887_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_878_);
                        crate::leanh::lean_inc(v_postponed_877_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_876_);
                        crate::leanh::lean_inc(v_cache_875_);
                        crate::leanh::lean_dec(v___x_874_);
                        v___x_880_ = crate::leanh::lean_box(0);
                        v_isShared_881_ = v_isSharedCheck_887_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_880_, 0, v_snd_873_);
                    v___x_883_ = v___x_880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_886_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 0, v_snd_873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 1, v_cache_875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 2, v_zetaDeltaFVarIds_876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 3, v_postponed_877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 4, v_diag_878_);
                    v___x_883_ = v_reuseFailAlloc_886_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_884_ = lean_st_ref_set(v___y_865_, v___x_883_);
                v___x_885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_885_, 0, v_fst_872_);
                return v___x_885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg___boxed(
    mut v_e_889_: *mut crate::leanh::LeanObject,
    mut v___y_890_: *mut crate::leanh::LeanObject,
    mut v___y_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_892_ =
        l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v_e_889_, v___y_890_);
    crate::leanh::lean_dec(v___y_890_);
    return v_res_892_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0(
    mut v_e_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
    mut v___y_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ =
        l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v_e_893_, v___y_895_);
    return v___x_899_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___boxed(
    mut v_e_900_: *mut crate::leanh::LeanObject,
    mut v___y_901_: *mut crate::leanh::LeanObject,
    mut v___y_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
    mut v___y_904_: *mut crate::leanh::LeanObject,
    mut v___y_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0(
        v_e_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_,
    );
    crate::leanh::lean_dec(v___y_904_);
    crate::leanh::lean_dec_ref(v___y_903_);
    crate::leanh::lean_dec(v___y_902_);
    crate::leanh::lean_dec_ref(v___y_901_);
    return v_res_906_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(
    mut v_mvarId_907_: *mut crate::leanh::LeanObject,
    mut v_x_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: *mut crate::leanh::LeanObject,
    mut v___y_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_918_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut v_a_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_926_: u8 = 0;
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_914_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_907_,
                    v_x_908_,
                    v___y_909_,
                    v___y_910_,
                    v___y_911_,
                    v___y_912_,
                );
                if crate::leanh::lean_obj_tag(v___x_914_) == 0 {
                    v_a_915_ = crate::leanh::lean_ctor_get(v___x_914_, 0);
                    v_isSharedCheck_922_ = (!crate::leanh::lean_is_exclusive(v___x_914_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v___x_917_ = v___x_914_;
                        v_isShared_918_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_915_);
                        crate::leanh::lean_dec(v___x_914_);
                        v___x_917_ = crate::leanh::lean_box(0);
                        v_isShared_918_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_923_ = crate::leanh::lean_ctor_get(v___x_914_, 0);
                    v_isSharedCheck_930_ = (!crate::leanh::lean_is_exclusive(v___x_914_)) as u8;
                    if v_isSharedCheck_930_ == 0 {
                        v___x_925_ = v___x_914_;
                        v_isShared_926_ = v_isSharedCheck_930_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_923_);
                        crate::leanh::lean_dec(v___x_914_);
                        v___x_925_ = crate::leanh::lean_box(0);
                        v_isShared_926_ = v_isSharedCheck_930_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_918_ == 0 {
                    v___x_920_ = v___x_917_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
                    v___x_920_ = v_reuseFailAlloc_921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_920_;
            }
            3 => {
                if v_isShared_926_ == 0 {
                    v___x_928_ = v___x_925_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
                    v___x_928_ = v_reuseFailAlloc_929_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg___boxed(
    mut v_mvarId_931_: *mut crate::leanh::LeanObject,
    mut v_x_932_: *mut crate::leanh::LeanObject,
    mut v___y_933_: *mut crate::leanh::LeanObject,
    mut v___y_934_: *mut crate::leanh::LeanObject,
    mut v___y_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(
        v_mvarId_931_,
        v_x_932_,
        v___y_933_,
        v___y_934_,
        v___y_935_,
        v___y_936_,
    );
    crate::leanh::lean_dec(v___y_936_);
    crate::leanh::lean_dec_ref(v___y_935_);
    crate::leanh::lean_dec(v___y_934_);
    crate::leanh::lean_dec_ref(v___y_933_);
    return v_res_938_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2(
    mut v_00_u03b1_939_: *mut crate::leanh::LeanObject,
    mut v_mvarId_940_: *mut crate::leanh::LeanObject,
    mut v_x_941_: *mut crate::leanh::LeanObject,
    mut v___y_942_: *mut crate::leanh::LeanObject,
    mut v___y_943_: *mut crate::leanh::LeanObject,
    mut v___y_944_: *mut crate::leanh::LeanObject,
    mut v___y_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(
        v_mvarId_940_,
        v_x_941_,
        v___y_942_,
        v___y_943_,
        v___y_944_,
        v___y_945_,
    );
    return v___x_947_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___boxed(
    mut v_00_u03b1_948_: *mut crate::leanh::LeanObject,
    mut v_mvarId_949_: *mut crate::leanh::LeanObject,
    mut v_x_950_: *mut crate::leanh::LeanObject,
    mut v___y_951_: *mut crate::leanh::LeanObject,
    mut v___y_952_: *mut crate::leanh::LeanObject,
    mut v___y_953_: *mut crate::leanh::LeanObject,
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v___y_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2(
        v_00_u03b1_948_,
        v_mvarId_949_,
        v_x_950_,
        v___y_951_,
        v___y_952_,
        v___y_953_,
        v___y_954_,
    );
    crate::leanh::lean_dec(v___y_954_);
    crate::leanh::lean_dec_ref(v___y_953_);
    crate::leanh::lean_dec(v___y_952_);
    crate::leanh::lean_dec_ref(v___y_951_);
    return v_res_956_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_957_: *mut crate::leanh::LeanObject,
    mut v_x_958_: *mut crate::leanh::LeanObject,
    mut v_x_959_: *mut crate::leanh::LeanObject,
    mut v_x_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_961_ = crate::leanh::lean_ctor_get(v_x_957_, 0);
                v_vs_962_ = crate::leanh::lean_ctor_get(v_x_957_, 1);
                v_isSharedCheck_986_ = (!crate::leanh::lean_is_exclusive(v_x_957_)) as u8;
                if v_isSharedCheck_986_ == 0 {
                    v___x_964_ = v_x_957_;
                    v_isShared_965_ = v_isSharedCheck_986_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_962_);
                    crate::leanh::lean_inc(v_ks_961_);
                    crate::leanh::lean_dec(v_x_957_);
                    v___x_964_ = crate::leanh::lean_box(0);
                    v_isShared_965_ = v_isSharedCheck_986_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_966_ = lean_array_get_size(v_ks_961_);
                v___x_967_ = lean_nat_dec_lt(v_x_958_, v___x_966_);
                if v___x_967_ == 0 {
                    crate::leanh::lean_dec(v_x_958_);
                    v___x_968_ = lean_array_push(v_ks_961_, v_x_959_);
                    v___x_969_ = lean_array_push(v_vs_962_, v_x_960_);
                    if v_isShared_965_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_964_, 1, v___x_969_);
                        crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_968_);
                        v___x_971_ = v___x_964_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_972_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_968_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_969_);
                        v___x_971_ = v_reuseFailAlloc_972_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_973_ = lean_array_fget_borrowed(v_ks_961_, v_x_958_);
                    v___x_974_ = l_Lean_instBEqMVarId_beq(v_x_959_, v_k_x27_973_);
                    if v___x_974_ == 0 {
                        if v_isShared_965_ == 0 {
                            v___x_976_ = v___x_964_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_980_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_980_, 0, v_ks_961_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_980_, 1, v_vs_962_);
                            v___x_976_ = v_reuseFailAlloc_980_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_981_ = lean_array_fset(v_ks_961_, v_x_958_, v_x_959_);
                        v___x_982_ = lean_array_fset(v_vs_962_, v_x_958_, v_x_960_);
                        crate::leanh::lean_dec(v_x_958_);
                        if v_isShared_965_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_964_, 1, v___x_982_);
                            crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_981_);
                            v___x_984_ = v___x_964_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_985_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_981_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_982_);
                            v___x_984_ = v_reuseFailAlloc_985_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_971_;
            }
            3 => {
                v___x_977_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_978_ = lean_nat_add(v_x_958_, v___x_977_);
                crate::leanh::lean_dec(v_x_958_);
                v_x_957_ = v___x_976_;
                v_x_958_ = v___x_978_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(
    mut v_n_987_: *mut crate::leanh::LeanObject,
    mut v_k_988_: *mut crate::leanh::LeanObject,
    mut v_v_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_990_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_991_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_987_, v___x_990_, v_k_988_, v_v_989_);
    return v___x_991_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_992_: usize = 0;
    let mut v___x_993_: usize = 0;
    let mut v___x_994_: usize = 0;
    v___x_992_ = 5usize;
    v___x_993_ = 1usize;
    v___x_994_ = lean_usize_shift_left(v___x_993_, v___x_992_);
    return v___x_994_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_995_: usize = 0;
    let mut v___x_996_: usize = 0;
    let mut v___x_997_: usize = 0;
    v___x_995_ = 1usize;
    v___x_996_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_997_ = lean_usize_sub(v___x_996_, v___x_995_);
    return v___x_997_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_998_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(
    mut v_x_999_: *mut crate::leanh::LeanObject,
    mut v_x_1000_: usize,
    mut v_x_1001_: usize,
    mut v_x_1002_: *mut crate::leanh::LeanObject,
    mut v_x_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: usize = 0;
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut v_j_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: u8 = 0;
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v_v_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1028_: u8 = 0;
    let mut v___x_1029_: u8 = 0;
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1035_: u8 = 0;
    let mut v_node_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v___x_1040_: usize = 0;
    let mut v___x_1041_: usize = 0;
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1046_: u8 = 0;
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1048_: u8 = 0;
    let mut v_unused_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1054_: u8 = 0;
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1059_: u8 = 0;
    let mut v_ks_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: u8 = 0;
    let mut v_reuseFailAlloc_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_999_) == 0 {
                    v_es_1004_ = crate::leanh::lean_ctor_get(v_x_999_, 0);
                    v___x_1005_ = 5usize;
                    v___x_1006_ = 1usize;
                    v___x_1007_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1);
                    v___x_1008_ = lean_usize_land(v_x_1000_, v___x_1007_);
                    v_j_1009_ = lean_usize_to_nat(v___x_1008_);
                    v___x_1010_ = lean_array_get_size(v_es_1004_);
                    v___x_1011_ = lean_nat_dec_lt(v_j_1009_, v___x_1010_);
                    if v___x_1011_ == 0 {
                        crate::leanh::lean_dec(v_j_1009_);
                        crate::leanh::lean_dec(v_x_1003_);
                        crate::leanh::lean_dec(v_x_1002_);
                        return v_x_999_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1004_);
                        v_isSharedCheck_1048_ = (!crate::leanh::lean_is_exclusive(v_x_999_)) as u8;
                        if v_isSharedCheck_1048_ == 0 {
                            v_unused_1049_ = crate::leanh::lean_ctor_get(v_x_999_, 0);
                            crate::leanh::lean_dec(v_unused_1049_);
                            v___x_1013_ = v_x_999_;
                            v_isShared_1014_ = v_isSharedCheck_1048_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_999_);
                            v___x_1013_ = crate::leanh::lean_box(0);
                            v_isShared_1014_ = v_isSharedCheck_1048_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1050_ = crate::leanh::lean_ctor_get(v_x_999_, 0);
                    v_vs_1051_ = crate::leanh::lean_ctor_get(v_x_999_, 1);
                    v_isSharedCheck_1071_ = (!crate::leanh::lean_is_exclusive(v_x_999_)) as u8;
                    if v_isSharedCheck_1071_ == 0 {
                        v___x_1053_ = v_x_999_;
                        v_isShared_1054_ = v_isSharedCheck_1071_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1051_);
                        crate::leanh::lean_inc(v_ks_1050_);
                        crate::leanh::lean_dec(v_x_999_);
                        v___x_1053_ = crate::leanh::lean_box(0);
                        v_isShared_1054_ = v_isSharedCheck_1071_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1015_ = lean_array_fget(v_es_1004_, v_j_1009_);
                v___x_1016_ = crate::leanh::lean_box(0);
                v_xs_x27_1017_ = lean_array_fset(v_es_1004_, v_j_1009_, v___x_1016_);
                match crate::leanh::lean_obj_tag(v_v_1015_) {
                    0 => {
                        v_key_1024_ = crate::leanh::lean_ctor_get(v_v_1015_, 0);
                        v_val_1025_ = crate::leanh::lean_ctor_get(v_v_1015_, 1);
                        v_isSharedCheck_1035_ = (!crate::leanh::lean_is_exclusive(v_v_1015_)) as u8;
                        if v_isSharedCheck_1035_ == 0 {
                            v___x_1027_ = v_v_1015_;
                            v_isShared_1028_ = v_isSharedCheck_1035_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1025_);
                            crate::leanh::lean_inc(v_key_1024_);
                            crate::leanh::lean_dec(v_v_1015_);
                            v___x_1027_ = crate::leanh::lean_box(0);
                            v_isShared_1028_ = v_isSharedCheck_1035_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1036_ = crate::leanh::lean_ctor_get(v_v_1015_, 0);
                        v_isSharedCheck_1046_ = (!crate::leanh::lean_is_exclusive(v_v_1015_)) as u8;
                        if v_isSharedCheck_1046_ == 0 {
                            v___x_1038_ = v_v_1015_;
                            v_isShared_1039_ = v_isSharedCheck_1046_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1036_);
                            crate::leanh::lean_dec(v_v_1015_);
                            v___x_1038_ = crate::leanh::lean_box(0);
                            v_isShared_1039_ = v_isSharedCheck_1046_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1047_, 0, v_x_1002_);
                        crate::leanh::lean_ctor_set(v___x_1047_, 1, v_x_1003_);
                        v___y_1019_ = v___x_1047_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1020_ = lean_array_fset(v_xs_x27_1017_, v_j_1009_, v___y_1019_);
                crate::leanh::lean_dec(v_j_1009_);
                if v_isShared_1014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1020_);
                    v___x_1022_ = v___x_1013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
                    v___x_1022_ = v_reuseFailAlloc_1023_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1022_;
            }
            4 => {
                v___x_1029_ = l_Lean_instBEqMVarId_beq(v_x_1002_, v_key_1024_);
                if v___x_1029_ == 0 {
                    crate::leanh::lean_del_object(v___x_1027_);
                    v___x_1030_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1024_,
                        v_val_1025_,
                        v_x_1002_,
                        v_x_1003_,
                    );
                    v___x_1031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1031_, 0, v___x_1030_);
                    v___y_1019_ = v___x_1031_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1025_);
                    crate::leanh::lean_dec(v_key_1024_);
                    if v_isShared_1028_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1027_, 1, v_x_1003_);
                        crate::leanh::lean_ctor_set(v___x_1027_, 0, v_x_1002_);
                        v___x_1033_ = v___x_1027_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_x_1002_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_x_1003_);
                        v___x_1033_ = v_reuseFailAlloc_1034_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1019_ = v___x_1033_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1040_ = lean_usize_shift_right(v_x_1000_, v___x_1005_);
                v___x_1041_ = lean_usize_add(v_x_1001_, v___x_1006_);
                v___x_1042_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_node_1036_, v___x_1040_, v___x_1041_, v_x_1002_, v_x_1003_);
                if v_isShared_1039_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1038_, 0, v___x_1042_);
                    v___x_1044_ = v___x_1038_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1045_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
                    v___x_1044_ = v_reuseFailAlloc_1045_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1019_ = v___x_1044_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1054_ == 0 {
                    v___x_1056_ = v___x_1053_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_ks_1050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_vs_1051_);
                    v___x_1056_ = v_reuseFailAlloc_1070_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1057_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v___x_1056_, v_x_1002_, v_x_1003_);
                v___x_1065_ = 7usize;
                v___x_1066_ = lean_usize_dec_le(v___x_1065_, v_x_1001_);
                if v___x_1066_ == 0 {
                    v___x_1067_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1057_);
                    v___x_1068_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1069_ = lean_nat_dec_lt(v___x_1067_, v___x_1068_);
                    crate::leanh::lean_dec(v___x_1067_);
                    v___y_1059_ = v___x_1069_;
                    state = 10;
                    continue;
                } else {
                    v___y_1059_ = v___x_1066_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1059_ == 0 {
                    v_ks_1060_ = crate::leanh::lean_ctor_get(v_newNode_1057_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1060_);
                    v_vs_1061_ = crate::leanh::lean_ctor_get(v_newNode_1057_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1061_);
                    crate::leanh::lean_dec_ref(v_newNode_1057_);
                    v___x_1062_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1063_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2);
                    v___x_1064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_x_1001_, v_ks_1060_, v_vs_1061_, v___x_1062_, v___x_1063_);
                    crate::leanh::lean_dec_ref(v_vs_1061_);
                    crate::leanh::lean_dec_ref(v_ks_1060_);
                    return v___x_1064_;
                } else {
                    return v_newNode_1057_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(
    mut v_depth_1072_: usize,
    mut v_keys_1073_: *mut crate::leanh::LeanObject,
    mut v_vals_1074_: *mut crate::leanh::LeanObject,
    mut v_i_1075_: *mut crate::leanh::LeanObject,
    mut v_entries_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: u8 = 0;
    let mut v_k_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u64 = 0;
    let mut v_h_1082_: usize = 0;
    let mut v___x_1083_: usize = 0;
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: usize = 0;
    let mut v___x_1086_: usize = 0;
    let mut v___x_1087_: usize = 0;
    let mut v_h_1088_: usize = 0;
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1077_ = lean_array_get_size(v_keys_1073_);
                v___x_1078_ = lean_nat_dec_lt(v_i_1075_, v___x_1077_);
                if v___x_1078_ == 0 {
                    crate::leanh::lean_dec(v_i_1075_);
                    return v_entries_1076_;
                } else {
                    v_k_1079_ = lean_array_fget_borrowed(v_keys_1073_, v_i_1075_);
                    v_v_1080_ = lean_array_fget_borrowed(v_vals_1074_, v_i_1075_);
                    v___x_1081_ = l_Lean_instHashableMVarId_hash(v_k_1079_);
                    v_h_1082_ = lean_uint64_to_usize(v___x_1081_);
                    v___x_1083_ = 5usize;
                    v___x_1084_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1085_ = 1usize;
                    v___x_1086_ = lean_usize_sub(v_depth_1072_, v___x_1085_);
                    v___x_1087_ = lean_usize_mul(v___x_1083_, v___x_1086_);
                    v_h_1088_ = lean_usize_shift_right(v_h_1082_, v___x_1087_);
                    v___x_1089_ = lean_nat_add(v_i_1075_, v___x_1084_);
                    crate::leanh::lean_dec(v_i_1075_);
                    crate::leanh::lean_inc(v_v_1080_);
                    crate::leanh::lean_inc(v_k_1079_);
                    v___x_1090_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_entries_1076_, v_h_1088_, v_depth_1072_, v_k_1079_, v_v_1080_);
                    v_i_1075_ = v___x_1089_;
                    v_entries_1076_ = v___x_1090_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_depth_1092_: *mut crate::leanh::LeanObject,
    mut v_keys_1093_: *mut crate::leanh::LeanObject,
    mut v_vals_1094_: *mut crate::leanh::LeanObject,
    mut v_i_1095_: *mut crate::leanh::LeanObject,
    mut v_entries_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1097_: usize = 0;
    let mut v_res_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1097_ = crate::leanh::lean_unbox_usize(v_depth_1092_);
    crate::leanh::lean_dec(v_depth_1092_);
    v_res_1098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_1097_, v_keys_1093_, v_vals_1094_, v_i_1095_, v_entries_1096_);
    crate::leanh::lean_dec_ref(v_vals_1094_);
    crate::leanh::lean_dec_ref(v_keys_1093_);
    return v_res_1098_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_1099_: *mut crate::leanh::LeanObject,
    mut v_x_1100_: *mut crate::leanh::LeanObject,
    mut v_x_1101_: *mut crate::leanh::LeanObject,
    mut v_x_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2584__boxed_1104_: usize = 0;
    let mut v_x_2585__boxed_1105_: usize = 0;
    let mut v_res_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2584__boxed_1104_ = crate::leanh::lean_unbox_usize(v_x_1100_);
    crate::leanh::lean_dec(v_x_1100_);
    v_x_2585__boxed_1105_ = crate::leanh::lean_unbox_usize(v_x_1101_);
    crate::leanh::lean_dec(v_x_1101_);
    v_res_1106_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_1099_, v_x_2584__boxed_1104_, v_x_2585__boxed_1105_, v_x_1102_, v_x_1103_);
    return v_res_1106_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(
    mut v_x_1107_: *mut crate::leanh::LeanObject,
    mut v_x_1108_: *mut crate::leanh::LeanObject,
    mut v_x_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: u64 = 0;
    let mut v___x_1111_: usize = 0;
    let mut v___x_1112_: usize = 0;
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lean_instHashableMVarId_hash(v_x_1108_);
    v___x_1111_ = lean_uint64_to_usize(v___x_1110_);
    v___x_1112_ = 1usize;
    v___x_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_1107_, v___x_1111_, v___x_1112_, v_x_1108_, v_x_1109_);
    return v___x_1113_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(
    mut v_mvarId_1114_: *mut crate::leanh::LeanObject,
    mut v_val_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1126_: u8 = 0;
    let mut v_depth_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1150_: u8 = 0;
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1118_ = lean_st_ref_take(v___y_1116_);
                v_mctx_1119_ = crate::leanh::lean_ctor_get(v___x_1118_, 0);
                v_cache_1120_ = crate::leanh::lean_ctor_get(v___x_1118_, 1);
                v_zetaDeltaFVarIds_1121_ = crate::leanh::lean_ctor_get(v___x_1118_, 2);
                v_postponed_1122_ = crate::leanh::lean_ctor_get(v___x_1118_, 3);
                v_diag_1123_ = crate::leanh::lean_ctor_get(v___x_1118_, 4);
                v_isSharedCheck_1151_ = (!crate::leanh::lean_is_exclusive(v___x_1118_)) as u8;
                if v_isSharedCheck_1151_ == 0 {
                    v___x_1125_ = v___x_1118_;
                    v_isShared_1126_ = v_isSharedCheck_1151_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1123_);
                    crate::leanh::lean_inc(v_postponed_1122_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1121_);
                    crate::leanh::lean_inc(v_cache_1120_);
                    crate::leanh::lean_inc(v_mctx_1119_);
                    crate::leanh::lean_dec(v___x_1118_);
                    v___x_1125_ = crate::leanh::lean_box(0);
                    v_isShared_1126_ = v_isSharedCheck_1151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1127_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 0);
                v_levelAssignDepth_1128_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 1);
                v_lmvarCounter_1129_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 2);
                v_mvarCounter_1130_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 3);
                v_lDecls_1131_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 4);
                v_decls_1132_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 5);
                v_userNames_1133_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 6);
                v_lAssignment_1134_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 7);
                v_eAssignment_1135_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 8);
                v_dAssignment_1136_ = crate::leanh::lean_ctor_get(v_mctx_1119_, 9);
                v_isSharedCheck_1150_ = (!crate::leanh::lean_is_exclusive(v_mctx_1119_)) as u8;
                if v_isSharedCheck_1150_ == 0 {
                    v___x_1138_ = v_mctx_1119_;
                    v_isShared_1139_ = v_isSharedCheck_1150_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1136_);
                    crate::leanh::lean_inc(v_eAssignment_1135_);
                    crate::leanh::lean_inc(v_lAssignment_1134_);
                    crate::leanh::lean_inc(v_userNames_1133_);
                    crate::leanh::lean_inc(v_decls_1132_);
                    crate::leanh::lean_inc(v_lDecls_1131_);
                    crate::leanh::lean_inc(v_mvarCounter_1130_);
                    crate::leanh::lean_inc(v_lmvarCounter_1129_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1128_);
                    crate::leanh::lean_inc(v_depth_1127_);
                    crate::leanh::lean_dec(v_mctx_1119_);
                    v___x_1138_ = crate::leanh::lean_box(0);
                    v_isShared_1139_ = v_isSharedCheck_1150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1140_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_eAssignment_1135_, v_mvarId_1114_, v_val_1115_);
                if v_isShared_1139_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1138_, 8, v___x_1140_);
                    v___x_1142_ = v___x_1138_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1149_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_depth_1127_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1149_,
                        1,
                        v_levelAssignDepth_1128_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_lmvarCounter_1129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_mvarCounter_1130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_lDecls_1131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_decls_1132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 6, v_userNames_1133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 7, v_lAssignment_1134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 8, v___x_1140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 9, v_dAssignment_1136_);
                    v___x_1142_ = v_reuseFailAlloc_1149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1125_, 0, v___x_1142_);
                    v___x_1144_ = v___x_1125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1148_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_cache_1120_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1148_,
                        2,
                        v_zetaDeltaFVarIds_1121_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_postponed_1122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_diag_1123_);
                    v___x_1144_ = v_reuseFailAlloc_1148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1145_ = lean_st_ref_set(v___y_1116_, v___x_1144_);
                v___x_1146_ = crate::leanh::lean_box(0);
                v___x_1147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1147_, 0, v___x_1146_);
                return v___x_1147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg___boxed(
    mut v_mvarId_1152_: *mut crate::leanh::LeanObject,
    mut v_val_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(
        v_mvarId_1152_,
        v_val_1153_,
        v___y_1154_,
    );
    crate::leanh::lean_dec(v___y_1154_);
    return v_res_1156_;
}
pub unsafe fn _init_l_Lean_MVarId_refl___lam__0___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = l_Lean_MVarId_refl___lam__0___closed__3;
    v___x_1163_ = l_Lean_stringToMessageData(v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn _init_l_Lean_MVarId_refl___lam__0___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = l_Lean_MVarId_refl___lam__0___closed__5;
    v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
    return v___x_1166_;
}
pub unsafe fn _init_l_Lean_MVarId_refl___lam__0___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lean_MVarId_refl___lam__0___closed__8;
    v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_Lean_MVarId_refl___lam__0(
    mut v_mvarId_1172_: *mut crate::leanh::LeanObject,
    mut v___x_1173_: *mut crate::leanh::LeanObject,
    mut v___x_1174_: *mut crate::leanh::LeanObject,
    mut v_check_1175_: u8,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1217_: u8 = 0;
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: u8 = 0;
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1256_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1260_: u8 = 0;
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_unused_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1172_);
                v___x_1181_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1172_,
                    v___x_1173_,
                    v___y_1176_,
                    v___y_1177_,
                    v___y_1178_,
                    v___y_1179_,
                );
                if crate::leanh::lean_obj_tag(v___x_1181_) == 0 {
                    v_isSharedCheck_1261_ = (!crate::leanh::lean_is_exclusive(v___x_1181_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v_unused_1262_ = crate::leanh::lean_ctor_get(v___x_1181_, 0);
                        crate::leanh::lean_dec(v_unused_1262_);
                        v___x_1183_ = v___x_1181_;
                        v_isShared_1184_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1181_);
                        v___x_1183_ = crate::leanh::lean_box(0);
                        v_isShared_1184_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1174_);
                    crate::leanh::lean_dec(v_mvarId_1172_);
                    return v___x_1181_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_mvarId_1172_);
                v___x_1185_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_1172_,
                    v___y_1176_,
                    v___y_1177_,
                    v___y_1178_,
                    v___y_1179_,
                );
                if crate::leanh::lean_obj_tag(v___x_1185_) == 0 {
                    v_a_1186_ = crate::leanh::lean_ctor_get(v___x_1185_, 0);
                    crate::leanh::lean_inc(v_a_1186_);
                    crate::leanh::lean_dec_ref_known(v___x_1185_, 1);
                    v___x_1242_ = l_Lean_MVarId_refl___lam__0___closed__7;
                    v___x_1243_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1244_ = l_Lean_Expr_isAppOfArity(v_a_1186_, v___x_1242_, v___x_1243_);
                    if v___x_1244_ == 0 {
                        v___x_1245_ = l_Lean_MVarId_refl___lam__0___closed__2;
                        v___x_1246_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_refl___lam__0___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_refl___lam__0___closed__9_once),
                            _init_l_Lean_MVarId_refl___lam__0___closed__9,
                        );
                        crate::leanh::lean_inc(v_a_1186_);
                        v___x_1247_ = l_Lean_indentExpr(v_a_1186_);
                        v___x_1248_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1246_);
                        crate::leanh::lean_ctor_set(v___x_1248_, 1, v___x_1247_);
                        if v_isShared_1184_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1183_, 1);
                            crate::leanh::lean_ctor_set(v___x_1183_, 0, v___x_1248_);
                            v___x_1250_ = v___x_1183_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_1252_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1248_);
                            v___x_1250_ = v_reuseFailAlloc_1252_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1183_);
                        v___y_1204_ = v___y_1176_;
                        v___y_1205_ = v___y_1177_;
                        v___y_1206_ = v___y_1178_;
                        v___y_1207_ = v___y_1179_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1183_);
                    crate::leanh::lean_dec_ref(v___x_1174_);
                    crate::leanh::lean_dec(v_mvarId_1172_);
                    v_a_1253_ = crate::leanh::lean_ctor_get(v___x_1185_, 0);
                    v_isSharedCheck_1260_ = (!crate::leanh::lean_is_exclusive(v___x_1185_)) as u8;
                    if v_isSharedCheck_1260_ == 0 {
                        v___x_1255_ = v___x_1185_;
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1253_);
                        crate::leanh::lean_dec(v___x_1185_);
                        v___x_1255_ = crate::leanh::lean_box(0);
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1194_ = l_Lean_Expr_getAppFn(v_a_1186_);
                crate::leanh::lean_dec(v_a_1186_);
                v___x_1195_ = l_Lean_Expr_constLevels_x21(v___x_1194_);
                crate::leanh::lean_dec_ref(v___x_1194_);
                v___x_1196_ = l_Lean_Expr_appFn_x21(v___y_1188_);
                crate::leanh::lean_dec_ref(v___y_1188_);
                v___x_1197_ = l_Lean_Expr_appArg_x21(v___x_1196_);
                crate::leanh::lean_dec_ref(v___x_1196_);
                v___x_1198_ = l_Lean_MVarId_refl___lam__0___closed__0;
                v___x_1199_ = l_Lean_Name_mkStr2(v___x_1198_, v___x_1174_);
                v___x_1200_ = l_Lean_mkConst(v___x_1199_, v___x_1195_);
                v___x_1201_ = l_Lean_mkAppB(v___x_1200_, v___x_1197_, v___y_1189_);
                v___x_1202_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(
                    v_mvarId_1172_,
                    v___x_1201_,
                    v___y_1191_,
                );
                return v___x_1202_;
            }
            3 => {
                v___x_1208_ = l_Lean_Expr_appFn_x21(v_a_1186_);
                v___x_1209_ = l_Lean_Expr_appArg_x21(v___x_1208_);
                v___x_1210_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(
                    v___x_1209_,
                    v___y_1205_,
                );
                v_a_1211_ = crate::leanh::lean_ctor_get(v___x_1210_, 0);
                crate::leanh::lean_inc(v_a_1211_);
                crate::leanh::lean_dec_ref(v___x_1210_);
                v___x_1212_ = l_Lean_Expr_appArg_x21(v_a_1186_);
                v___x_1213_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(
                    v___x_1212_,
                    v___y_1205_,
                );
                if v_check_1175_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1213_);
                    v___y_1188_ = v___x_1208_;
                    v___y_1189_ = v_a_1211_;
                    v___y_1190_ = v___y_1204_;
                    v___y_1191_ = v___y_1205_;
                    v___y_1192_ = v___y_1206_;
                    v___y_1193_ = v___y_1207_;
                    state = 2;
                    continue;
                } else {
                    v_a_1214_ = crate::leanh::lean_ctor_get(v___x_1213_, 0);
                    v_isSharedCheck_1241_ = (!crate::leanh::lean_is_exclusive(v___x_1213_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1216_ = v___x_1213_;
                        v_isShared_1217_ = v_isSharedCheck_1241_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1214_);
                        crate::leanh::lean_dec(v___x_1213_);
                        v___x_1216_ = crate::leanh::lean_box(0);
                        v_isShared_1217_ = v_isSharedCheck_1241_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_1214_);
                crate::leanh::lean_inc(v_a_1211_);
                v___x_1218_ = l_Lean_Meta_isExprDefEq(
                    v_a_1211_,
                    v_a_1214_,
                    v___y_1204_,
                    v___y_1205_,
                    v___y_1206_,
                    v___y_1207_,
                );
                if crate::leanh::lean_obj_tag(v___x_1218_) == 0 {
                    v_a_1219_ = crate::leanh::lean_ctor_get(v___x_1218_, 0);
                    crate::leanh::lean_inc(v_a_1219_);
                    crate::leanh::lean_dec_ref_known(v___x_1218_, 1);
                    v___x_1220_ = (crate::leanh::lean_unbox(v_a_1219_) as u8);
                    crate::leanh::lean_dec(v_a_1219_);
                    if v___x_1220_ == 0 {
                        v___x_1221_ = l_Lean_MVarId_refl___lam__0___closed__2;
                        v___x_1222_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_refl___lam__0___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_refl___lam__0___closed__4_once),
                            _init_l_Lean_MVarId_refl___lam__0___closed__4,
                        );
                        crate::leanh::lean_inc(v_a_1211_);
                        v___x_1223_ = l_Lean_indentExpr(v_a_1211_);
                        v___x_1224_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1224_, 0, v___x_1222_);
                        crate::leanh::lean_ctor_set(v___x_1224_, 1, v___x_1223_);
                        v___x_1225_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_refl___lam__0___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_refl___lam__0___closed__6_once),
                            _init_l_Lean_MVarId_refl___lam__0___closed__6,
                        );
                        v___x_1226_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1224_);
                        crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
                        v___x_1227_ = l_Lean_indentExpr(v_a_1214_);
                        v___x_1228_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1228_, 0, v___x_1226_);
                        crate::leanh::lean_ctor_set(v___x_1228_, 1, v___x_1227_);
                        if v_isShared_1217_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1216_, 1);
                            crate::leanh::lean_ctor_set(v___x_1216_, 0, v___x_1228_);
                            v___x_1230_ = v___x_1216_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1232_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1228_);
                            v___x_1230_ = v_reuseFailAlloc_1232_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1216_);
                        crate::leanh::lean_dec(v_a_1214_);
                        v___y_1188_ = v___x_1208_;
                        v___y_1189_ = v_a_1211_;
                        v___y_1190_ = v___y_1204_;
                        v___y_1191_ = v___y_1205_;
                        v___y_1192_ = v___y_1206_;
                        v___y_1193_ = v___y_1207_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1216_);
                    crate::leanh::lean_dec(v_a_1214_);
                    crate::leanh::lean_dec(v_a_1211_);
                    crate::leanh::lean_dec_ref(v___x_1208_);
                    crate::leanh::lean_dec(v_a_1186_);
                    crate::leanh::lean_dec_ref(v___x_1174_);
                    crate::leanh::lean_dec(v_mvarId_1172_);
                    v_a_1233_ = crate::leanh::lean_ctor_get(v___x_1218_, 0);
                    v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v___x_1218_)) as u8;
                    if v_isSharedCheck_1240_ == 0 {
                        v___x_1235_ = v___x_1218_;
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1233_);
                        crate::leanh::lean_dec(v___x_1218_);
                        v___x_1235_ = crate::leanh::lean_box(0);
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_mvarId_1172_);
                v___x_1231_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1221_,
                    v_mvarId_1172_,
                    v___x_1230_,
                    v___y_1204_,
                    v___y_1205_,
                    v___y_1206_,
                    v___y_1207_,
                );
                if crate::leanh::lean_obj_tag(v___x_1231_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1231_, 1);
                    v___y_1188_ = v___x_1208_;
                    v___y_1189_ = v_a_1211_;
                    v___y_1190_ = v___y_1204_;
                    v___y_1191_ = v___y_1205_;
                    v___y_1192_ = v___y_1206_;
                    v___y_1193_ = v___y_1207_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1211_);
                    crate::leanh::lean_dec_ref(v___x_1208_);
                    crate::leanh::lean_dec(v_a_1186_);
                    crate::leanh::lean_dec_ref(v___x_1174_);
                    crate::leanh::lean_dec(v_mvarId_1172_);
                    return v___x_1231_;
                }
            }
            6 => {
                if v_isShared_1236_ == 0 {
                    v___x_1238_ = v___x_1235_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
                    v___x_1238_ = v_reuseFailAlloc_1239_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1238_;
            }
            8 => {
                crate::leanh::lean_inc(v_mvarId_1172_);
                v___x_1251_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1245_,
                    v_mvarId_1172_,
                    v___x_1250_,
                    v___y_1176_,
                    v___y_1177_,
                    v___y_1178_,
                    v___y_1179_,
                );
                if crate::leanh::lean_obj_tag(v___x_1251_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1251_, 1);
                    v___y_1204_ = v___y_1176_;
                    v___y_1205_ = v___y_1177_;
                    v___y_1206_ = v___y_1178_;
                    v___y_1207_ = v___y_1179_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1186_);
                    crate::leanh::lean_dec_ref(v___x_1174_);
                    crate::leanh::lean_dec(v_mvarId_1172_);
                    return v___x_1251_;
                }
            }
            9 => {
                if v_isShared_1256_ == 0 {
                    v___x_1258_ = v___x_1255_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
                    v___x_1258_ = v_reuseFailAlloc_1259_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_refl___lam__0___boxed(
    mut v_mvarId_1263_: *mut crate::leanh::LeanObject,
    mut v___x_1264_: *mut crate::leanh::LeanObject,
    mut v___x_1265_: *mut crate::leanh::LeanObject,
    mut v_check_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_boxed_1272_: u8 = 0;
    let mut v_res_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_boxed_1272_ = (crate::leanh::lean_unbox(v_check_1266_) as u8);
    v_res_1273_ = l_Lean_MVarId_refl___lam__0(
        v_mvarId_1263_,
        v___x_1264_,
        v___x_1265_,
        v_check_boxed_1272_,
        v___y_1267_,
        v___y_1268_,
        v___y_1269_,
        v___y_1270_,
    );
    crate::leanh::lean_dec(v___y_1270_);
    crate::leanh::lean_dec_ref(v___y_1269_);
    crate::leanh::lean_dec(v___y_1268_);
    crate::leanh::lean_dec_ref(v___y_1267_);
    return v_res_1273_;
}
pub unsafe fn l_Lean_MVarId_refl(
    mut v_mvarId_1277_: *mut crate::leanh::LeanObject,
    mut v_check_1278_: u8,
    mut v_a_1279_: *mut crate::leanh::LeanObject,
    mut v_a_1280_: *mut crate::leanh::LeanObject,
    mut v_a_1281_: *mut crate::leanh::LeanObject,
    mut v_a_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = l_Lean_MVarId_refl___closed__0;
    v___x_1285_ = l_Lean_MVarId_refl___closed__1;
    v___x_1286_ = crate::leanh::lean_box((v_check_1278_) as usize);
    crate::leanh::lean_inc(v_mvarId_1277_);
    v___f_1287_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_refl___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1287_, 0, v_mvarId_1277_);
    crate::leanh::lean_closure_set(v___f_1287_, 1, v___x_1285_);
    crate::leanh::lean_closure_set(v___f_1287_, 2, v___x_1284_);
    crate::leanh::lean_closure_set(v___f_1287_, 3, v___x_1286_);
    v___x_1288_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(
        v_mvarId_1277_,
        v___f_1287_,
        v_a_1279_,
        v_a_1280_,
        v_a_1281_,
        v_a_1282_,
    );
    return v___x_1288_;
}
pub unsafe fn l_Lean_MVarId_refl___boxed(
    mut v_mvarId_1289_: *mut crate::leanh::LeanObject,
    mut v_check_1290_: *mut crate::leanh::LeanObject,
    mut v_a_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_boxed_1296_: u8 = 0;
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_boxed_1296_ = (crate::leanh::lean_unbox(v_check_1290_) as u8);
    v_res_1297_ = l_Lean_MVarId_refl(
        v_mvarId_1289_,
        v_check_boxed_1296_,
        v_a_1291_,
        v_a_1292_,
        v_a_1293_,
        v_a_1294_,
    );
    crate::leanh::lean_dec(v_a_1294_);
    crate::leanh::lean_dec_ref(v_a_1293_);
    crate::leanh::lean_dec(v_a_1292_);
    crate::leanh::lean_dec_ref(v_a_1291_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(
    mut v_mvarId_1298_: *mut crate::leanh::LeanObject,
    mut v_val_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(
        v_mvarId_1298_,
        v_val_1299_,
        v___y_1301_,
    );
    return v___x_1305_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___boxed(
    mut v_mvarId_1306_: *mut crate::leanh::LeanObject,
    mut v_val_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(
        v_mvarId_1306_,
        v_val_1307_,
        v___y_1308_,
        v___y_1309_,
        v___y_1310_,
        v___y_1311_,
    );
    crate::leanh::lean_dec(v___y_1311_);
    crate::leanh::lean_dec_ref(v___y_1310_);
    crate::leanh::lean_dec(v___y_1309_);
    crate::leanh::lean_dec_ref(v___y_1308_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1(
    mut v_00_u03b2_1314_: *mut crate::leanh::LeanObject,
    mut v_x_1315_: *mut crate::leanh::LeanObject,
    mut v_x_1316_: *mut crate::leanh::LeanObject,
    mut v_x_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1318_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_x_1315_, v_x_1316_, v_x_1317_);
    return v___x_1318_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(
    mut v_00_u03b2_1319_: *mut crate::leanh::LeanObject,
    mut v_x_1320_: *mut crate::leanh::LeanObject,
    mut v_x_1321_: usize,
    mut v_x_1322_: usize,
    mut v_x_1323_: *mut crate::leanh::LeanObject,
    mut v_x_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_1320_, v_x_1321_, v_x_1322_, v_x_1323_, v_x_1324_);
    return v___x_1325_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_1326_: *mut crate::leanh::LeanObject,
    mut v_x_1327_: *mut crate::leanh::LeanObject,
    mut v_x_1328_: *mut crate::leanh::LeanObject,
    mut v_x_1329_: *mut crate::leanh::LeanObject,
    mut v_x_1330_: *mut crate::leanh::LeanObject,
    mut v_x_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3093__boxed_1332_: usize = 0;
    let mut v_x_3094__boxed_1333_: usize = 0;
    let mut v_res_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3093__boxed_1332_ = crate::leanh::lean_unbox_usize(v_x_1328_);
    crate::leanh::lean_dec(v_x_1328_);
    v_x_3094__boxed_1333_ = crate::leanh::lean_unbox_usize(v_x_1329_);
    crate::leanh::lean_dec(v_x_1329_);
    v_res_1334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(v_00_u03b2_1326_, v_x_1327_, v_x_3093__boxed_1332_, v_x_3094__boxed_1333_, v_x_1330_, v_x_1331_);
    return v_res_1334_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1335_: *mut crate::leanh::LeanObject,
    mut v_n_1336_: *mut crate::leanh::LeanObject,
    mut v_k_1337_: *mut crate::leanh::LeanObject,
    mut v_v_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1336_, v_k_1337_, v_v_1338_);
    return v___x_1339_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(
    mut v_00_u03b2_1340_: *mut crate::leanh::LeanObject,
    mut v_depth_1341_: usize,
    mut v_keys_1342_: *mut crate::leanh::LeanObject,
    mut v_vals_1343_: *mut crate::leanh::LeanObject,
    mut v_heq_1344_: *mut crate::leanh::LeanObject,
    mut v_i_1345_: *mut crate::leanh::LeanObject,
    mut v_entries_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1341_, v_keys_1342_, v_vals_1343_, v_i_1345_, v_entries_1346_);
    return v___x_1347_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b2_1348_: *mut crate::leanh::LeanObject,
    mut v_depth_1349_: *mut crate::leanh::LeanObject,
    mut v_keys_1350_: *mut crate::leanh::LeanObject,
    mut v_vals_1351_: *mut crate::leanh::LeanObject,
    mut v_heq_1352_: *mut crate::leanh::LeanObject,
    mut v_i_1353_: *mut crate::leanh::LeanObject,
    mut v_entries_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1355_: usize = 0;
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1355_ = crate::leanh::lean_unbox_usize(v_depth_1349_);
    crate::leanh::lean_dec(v_depth_1349_);
    v_res_1356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1348_, v_depth_boxed_1355_, v_keys_1350_, v_vals_1351_, v_heq_1352_, v_i_1353_, v_entries_1354_);
    crate::leanh::lean_dec_ref(v_vals_1351_);
    crate::leanh::lean_dec_ref(v_keys_1350_);
    return v_res_1356_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1357_: *mut crate::leanh::LeanObject,
    mut v_x_1358_: *mut crate::leanh::LeanObject,
    mut v_x_1359_: *mut crate::leanh::LeanObject,
    mut v_x_1360_: *mut crate::leanh::LeanObject,
    mut v_x_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1358_, v_x_1359_, v_x_1360_, v_x_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(
    mut v_x_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1380_: u8 = 0;
    let mut v_a_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1384_: u8 = 0;
    let mut v___y_1386_: u8 = 0;
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_unused_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1404_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: u8 = 0;
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_a_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1369_ = l_Lean_Meta_saveState___redArg(v___y_1365_, v___y_1367_);
                if crate::leanh::lean_obj_tag(v___x_1369_) == 0 {
                    v_a_1370_ = crate::leanh::lean_ctor_get(v___x_1369_, 0);
                    crate::leanh::lean_inc(v_a_1370_);
                    crate::leanh::lean_dec_ref_known(v___x_1369_, 1);
                    crate::leanh::lean_inc(v___y_1367_);
                    crate::leanh::lean_inc_ref(v___y_1366_);
                    crate::leanh::lean_inc(v___y_1365_);
                    crate::leanh::lean_inc_ref(v___y_1364_);
                    v___x_1371_ = crate::leanh::lean_apply_5(
                        v_x_1363_,
                        v___y_1364_,
                        v___y_1365_,
                        v___y_1366_,
                        v___y_1367_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1371_) == 0 {
                        crate::leanh::lean_dec(v_a_1370_);
                        v_a_1372_ = crate::leanh::lean_ctor_get(v___x_1371_, 0);
                        v_isSharedCheck_1380_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1371_)) as u8;
                        if v_isSharedCheck_1380_ == 0 {
                            v___x_1374_ = v___x_1371_;
                            v_isShared_1375_ = v_isSharedCheck_1380_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1372_);
                            crate::leanh::lean_dec(v___x_1371_);
                            v___x_1374_ = crate::leanh::lean_box(0);
                            v_isShared_1375_ = v_isSharedCheck_1380_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1381_ = crate::leanh::lean_ctor_get(v___x_1371_, 0);
                        v_isSharedCheck_1410_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1371_)) as u8;
                        if v_isSharedCheck_1410_ == 0 {
                            v___x_1383_ = v___x_1371_;
                            v_isShared_1384_ = v_isSharedCheck_1410_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1381_);
                            crate::leanh::lean_dec(v___x_1371_);
                            v___x_1383_ = crate::leanh::lean_box(0);
                            v_isShared_1384_ = v_isSharedCheck_1410_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1363_);
                    v_a_1411_ = crate::leanh::lean_ctor_get(v___x_1369_, 0);
                    v_isSharedCheck_1418_ = (!crate::leanh::lean_is_exclusive(v___x_1369_)) as u8;
                    if v_isSharedCheck_1418_ == 0 {
                        v___x_1413_ = v___x_1369_;
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1411_);
                        crate::leanh::lean_dec(v___x_1369_);
                        v___x_1413_ = crate::leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1376_, 0, v_a_1372_);
                if v_isShared_1375_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1374_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1374_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
                    v___x_1378_ = v_reuseFailAlloc_1379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1378_;
            }
            3 => {
                v___x_1408_ = l_Lean_Exception_isInterrupt(v_a_1381_);
                if v___x_1408_ == 0 {
                    crate::leanh::lean_inc(v_a_1381_);
                    v___x_1409_ = l_Lean_Exception_isRuntime(v_a_1381_);
                    v___y_1386_ = v___x_1409_;
                    state = 4;
                    continue;
                } else {
                    v___y_1386_ = v___x_1408_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_1386_ == 0 {
                    crate::leanh::lean_del_object(v___x_1383_);
                    crate::leanh::lean_dec(v_a_1381_);
                    v___x_1387_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_1370_,
                        v___y_1365_,
                        v___y_1367_,
                    );
                    crate::leanh::lean_dec(v_a_1370_);
                    if crate::leanh::lean_obj_tag(v___x_1387_) == 0 {
                        v_isSharedCheck_1395_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1387_)) as u8;
                        if v_isSharedCheck_1395_ == 0 {
                            v_unused_1396_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                            crate::leanh::lean_dec(v_unused_1396_);
                            v___x_1389_ = v___x_1387_;
                            v_isShared_1390_ = v_isSharedCheck_1395_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1387_);
                            v___x_1389_ = crate::leanh::lean_box(0);
                            v_isShared_1390_ = v_isSharedCheck_1395_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1397_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                        v_isSharedCheck_1404_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1387_)) as u8;
                        if v_isSharedCheck_1404_ == 0 {
                            v___x_1399_ = v___x_1387_;
                            v_isShared_1400_ = v_isSharedCheck_1404_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1397_);
                            crate::leanh::lean_dec(v___x_1387_);
                            v___x_1399_ = crate::leanh::lean_box(0);
                            v_isShared_1400_ = v_isSharedCheck_1404_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1370_);
                    if v_isShared_1384_ == 0 {
                        v___x_1406_ = v___x_1383_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1381_);
                        v___x_1406_ = v_reuseFailAlloc_1407_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1391_ = crate::leanh::lean_box(0);
                if v_isShared_1390_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1389_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1389_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
                    v___x_1393_ = v_reuseFailAlloc_1394_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1393_;
            }
            7 => {
                if v_isShared_1400_ == 0 {
                    v___x_1402_ = v___x_1399_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
                    v___x_1402_ = v_reuseFailAlloc_1403_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1402_;
            }
            9 => {
                return v___x_1406_;
            }
            10 => {
                if v_isShared_1414_ == 0 {
                    v___x_1416_ = v___x_1413_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
                    v___x_1416_ = v_reuseFailAlloc_1417_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg___boxed(
    mut v_x_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(
        v_x_1419_,
        v___y_1420_,
        v___y_1421_,
        v___y_1422_,
        v___y_1423_,
    );
    crate::leanh::lean_dec(v___y_1423_);
    crate::leanh::lean_dec_ref(v___y_1422_);
    crate::leanh::lean_dec(v___y_1421_);
    crate::leanh::lean_dec_ref(v___y_1420_);
    return v_res_1425_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(
    mut v_00_u03b1_1426_: *mut crate::leanh::LeanObject,
    mut v_x_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(
        v_x_1427_,
        v___y_1428_,
        v___y_1429_,
        v___y_1430_,
        v___y_1431_,
    );
    return v___x_1433_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___boxed(
    mut v_00_u03b1_1434_: *mut crate::leanh::LeanObject,
    mut v_x_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(
        v_00_u03b1_1434_,
        v_x_1435_,
        v___y_1436_,
        v___y_1437_,
        v___y_1438_,
        v___y_1439_,
    );
    crate::leanh::lean_dec(v___y_1439_);
    crate::leanh::lean_dec_ref(v___y_1438_);
    crate::leanh::lean_dec(v___y_1437_);
    crate::leanh::lean_dec_ref(v___y_1436_);
    return v_res_1441_;
}
pub unsafe fn l_Lean_MVarId_heqOfEq___lam__0(
    mut v_mvarId_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1455_ = l_Lean_Meta_mkFreshLevelMVar(
                    v___y_1450_,
                    v___y_1451_,
                    v___y_1452_,
                    v___y_1453_,
                );
                if crate::leanh::lean_obj_tag(v___x_1455_) == 0 {
                    v_a_1456_ = crate::leanh::lean_ctor_get(v___x_1455_, 0);
                    crate::leanh::lean_inc(v_a_1456_);
                    crate::leanh::lean_dec_ref_known(v___x_1455_, 1);
                    v___x_1457_ = l_Lean_MVarId_heqOfEq___lam__0___closed__1;
                    v___x_1458_ = crate::leanh::lean_box(0);
                    v___x_1459_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1459_, 0, v_a_1456_);
                    crate::leanh::lean_ctor_set(v___x_1459_, 1, v___x_1458_);
                    v___x_1460_ = l_Lean_mkConst(v___x_1457_, v___x_1459_);
                    v___x_1461_ = l_Lean_MVarId_heqOfEq___lam__0___closed__2;
                    v___x_1462_ = crate::leanh::lean_box(0);
                    v___x_1463_ = l_Lean_MVarId_apply(
                        v_mvarId_1449_,
                        v___x_1460_,
                        v___x_1461_,
                        v___x_1462_,
                        v___y_1450_,
                        v___y_1451_,
                        v___y_1452_,
                        v___y_1453_,
                    );
                    return v___x_1463_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_1449_);
                    v_a_1464_ = crate::leanh::lean_ctor_get(v___x_1455_, 0);
                    v_isSharedCheck_1471_ = (!crate::leanh::lean_is_exclusive(v___x_1455_)) as u8;
                    if v_isSharedCheck_1471_ == 0 {
                        v___x_1466_ = v___x_1455_;
                        v_isShared_1467_ = v_isSharedCheck_1471_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1464_);
                        crate::leanh::lean_dec(v___x_1455_);
                        v___x_1466_ = crate::leanh::lean_box(0);
                        v_isShared_1467_ = v_isSharedCheck_1471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1467_ == 0 {
                    v___x_1469_ = v___x_1466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
                    v___x_1469_ = v_reuseFailAlloc_1470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_heqOfEq___lam__0___boxed(
    mut v_mvarId_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Lean_MVarId_heqOfEq___lam__0(
        v_mvarId_1472_,
        v___y_1473_,
        v___y_1474_,
        v___y_1475_,
        v___y_1476_,
    );
    crate::leanh::lean_dec(v___y_1476_);
    crate::leanh::lean_dec_ref(v___y_1475_);
    crate::leanh::lean_dec(v___y_1474_);
    crate::leanh::lean_dec_ref(v___y_1473_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_MVarId_heqOfEq___lam__1(
    mut v___f_1479_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v_val_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut v_a_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1486_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(
                    v___f_1479_,
                    v___y_1481_,
                    v___y_1482_,
                    v___y_1483_,
                    v___y_1484_,
                );
                if crate::leanh::lean_obj_tag(v___x_1486_) == 0 {
                    v_a_1487_ = crate::leanh::lean_ctor_get(v___x_1486_, 0);
                    v_isSharedCheck_1506_ = (!crate::leanh::lean_is_exclusive(v___x_1486_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v___x_1489_ = v___x_1486_;
                        v_isShared_1490_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1487_);
                        crate::leanh::lean_dec(v___x_1486_);
                        v___x_1489_ = crate::leanh::lean_box(0);
                        v_isShared_1490_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1480_);
                    v_a_1507_ = crate::leanh::lean_ctor_get(v___x_1486_, 0);
                    v_isSharedCheck_1514_ = (!crate::leanh::lean_is_exclusive(v___x_1486_)) as u8;
                    if v_isSharedCheck_1514_ == 0 {
                        v___x_1509_ = v___x_1486_;
                        v_isShared_1510_ = v_isSharedCheck_1514_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1507_);
                        crate::leanh::lean_dec(v___x_1486_);
                        v___x_1509_ = crate::leanh::lean_box(0);
                        v_isShared_1510_ = v_isSharedCheck_1514_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1487_) == 1 {
                    v_val_1491_ = crate::leanh::lean_ctor_get(v_a_1487_, 0);
                    crate::leanh::lean_inc(v_val_1491_);
                    crate::leanh::lean_dec_ref_known(v_a_1487_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1491_) == 1 {
                        v_tail_1492_ = crate::leanh::lean_ctor_get(v_val_1491_, 1);
                        if crate::leanh::lean_obj_tag(v_tail_1492_) == 0 {
                            crate::leanh::lean_dec(v_mvarId_1480_);
                            v_head_1493_ = crate::leanh::lean_ctor_get(v_val_1491_, 0);
                            crate::leanh::lean_inc(v_head_1493_);
                            crate::leanh::lean_dec_ref_known(v_val_1491_, 2);
                            if v_isShared_1490_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1489_, 0, v_head_1493_);
                                v___x_1495_ = v___x_1489_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1496_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1496_,
                                    0,
                                    v_head_1493_,
                                );
                                v___x_1495_ = v_reuseFailAlloc_1496_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_val_1491_, 2);
                            if v_isShared_1490_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1489_, 0, v_mvarId_1480_);
                                v___x_1498_ = v___x_1489_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1499_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1499_,
                                    0,
                                    v_mvarId_1480_,
                                );
                                v___x_1498_ = v_reuseFailAlloc_1499_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1491_);
                        if v_isShared_1490_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1489_, 0, v_mvarId_1480_);
                            v___x_1501_ = v___x_1489_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1502_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_mvarId_1480_);
                            v___x_1501_ = v_reuseFailAlloc_1502_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1487_);
                    if v_isShared_1490_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1489_, 0, v_mvarId_1480_);
                        v___x_1504_ = v___x_1489_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1505_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_mvarId_1480_);
                        v___x_1504_ = v_reuseFailAlloc_1505_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1495_;
            }
            3 => {
                return v___x_1498_;
            }
            4 => {
                return v___x_1501_;
            }
            5 => {
                return v___x_1504_;
            }
            6 => {
                if v_isShared_1510_ == 0 {
                    v___x_1512_ = v___x_1509_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
                    v___x_1512_ = v_reuseFailAlloc_1513_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_heqOfEq___lam__1___boxed(
    mut v___f_1515_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Lean_MVarId_heqOfEq___lam__1(
        v___f_1515_,
        v_mvarId_1516_,
        v___y_1517_,
        v___y_1518_,
        v___y_1519_,
        v___y_1520_,
    );
    crate::leanh::lean_dec(v___y_1520_);
    crate::leanh::lean_dec_ref(v___y_1519_);
    crate::leanh::lean_dec(v___y_1518_);
    crate::leanh::lean_dec_ref(v___y_1517_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_MVarId_heqOfEq(
    mut v_mvarId_1523_: *mut crate::leanh::LeanObject,
    mut v_a_1524_: *mut crate::leanh::LeanObject,
    mut v_a_1525_: *mut crate::leanh::LeanObject,
    mut v_a_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_mvarId_1523_, 2);
    v___f_1529_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_heqOfEq___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1529_, 0, v_mvarId_1523_);
    v___f_1530_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_heqOfEq___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1530_, 0, v___f_1529_);
    crate::leanh::lean_closure_set(v___f_1530_, 1, v_mvarId_1523_);
    v___x_1531_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(
        v_mvarId_1523_,
        v___f_1530_,
        v_a_1524_,
        v_a_1525_,
        v_a_1526_,
        v_a_1527_,
    );
    return v___x_1531_;
}
pub unsafe fn l_Lean_MVarId_heqOfEq___boxed(
    mut v_mvarId_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
    mut v_a_1534_: *mut crate::leanh::LeanObject,
    mut v_a_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1538_ = l_Lean_MVarId_heqOfEq(v_mvarId_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
    crate::leanh::lean_dec(v_a_1536_);
    crate::leanh::lean_dec_ref(v_a_1535_);
    crate::leanh::lean_dec(v_a_1534_);
    crate::leanh::lean_dec_ref(v_a_1533_);
    return v_res_1538_;
}
pub unsafe fn l_Lean_MVarId_eqOfHEq___lam__0(
    mut v_mvarId_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
    mut v___y_1544_: *mut crate::leanh::LeanObject,
    mut v___y_1545_: *mut crate::leanh::LeanObject,
    mut v___y_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1548_ = l_Lean_Meta_mkFreshLevelMVar(
                    v___y_1543_,
                    v___y_1544_,
                    v___y_1545_,
                    v___y_1546_,
                );
                if crate::leanh::lean_obj_tag(v___x_1548_) == 0 {
                    v_a_1549_ = crate::leanh::lean_ctor_get(v___x_1548_, 0);
                    crate::leanh::lean_inc(v_a_1549_);
                    crate::leanh::lean_dec_ref_known(v___x_1548_, 1);
                    v___x_1550_ = l_Lean_MVarId_eqOfHEq___lam__0___closed__1;
                    v___x_1551_ = crate::leanh::lean_box(0);
                    v___x_1552_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1552_, 0, v_a_1549_);
                    crate::leanh::lean_ctor_set(v___x_1552_, 1, v___x_1551_);
                    v___x_1553_ = l_Lean_mkConst(v___x_1550_, v___x_1552_);
                    v___x_1554_ = l_Lean_MVarId_heqOfEq___lam__0___closed__2;
                    v___x_1555_ = crate::leanh::lean_box(0);
                    v___x_1556_ = l_Lean_MVarId_apply(
                        v_mvarId_1542_,
                        v___x_1553_,
                        v___x_1554_,
                        v___x_1555_,
                        v___y_1543_,
                        v___y_1544_,
                        v___y_1545_,
                        v___y_1546_,
                    );
                    return v___x_1556_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_1542_);
                    v_a_1557_ = crate::leanh::lean_ctor_get(v___x_1548_, 0);
                    v_isSharedCheck_1564_ = (!crate::leanh::lean_is_exclusive(v___x_1548_)) as u8;
                    if v_isSharedCheck_1564_ == 0 {
                        v___x_1559_ = v___x_1548_;
                        v_isShared_1560_ = v_isSharedCheck_1564_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1557_);
                        crate::leanh::lean_dec(v___x_1548_);
                        v___x_1559_ = crate::leanh::lean_box(0);
                        v_isShared_1560_ = v_isSharedCheck_1564_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1560_ == 0 {
                    v___x_1562_ = v___x_1559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1563_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
                    v___x_1562_ = v_reuseFailAlloc_1563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_eqOfHEq___lam__0___boxed(
    mut v_mvarId_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
    mut v___y_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Lean_MVarId_eqOfHEq___lam__0(
        v_mvarId_1565_,
        v___y_1566_,
        v___y_1567_,
        v___y_1568_,
        v___y_1569_,
    );
    crate::leanh::lean_dec(v___y_1569_);
    crate::leanh::lean_dec_ref(v___y_1568_);
    crate::leanh::lean_dec(v___y_1567_);
    crate::leanh::lean_dec_ref(v___y_1566_);
    return v_res_1571_;
}
pub unsafe fn l_Lean_MVarId_eqOfHEq___lam__1(
    mut v___f_1572_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
    mut v___y_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v_val_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1579_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(
                    v___f_1572_,
                    v___y_1574_,
                    v___y_1575_,
                    v___y_1576_,
                    v___y_1577_,
                );
                if crate::leanh::lean_obj_tag(v___x_1579_) == 0 {
                    v_a_1580_ = crate::leanh::lean_ctor_get(v___x_1579_, 0);
                    v_isSharedCheck_1599_ = (!crate::leanh::lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1599_ == 0 {
                        v___x_1582_ = v___x_1579_;
                        v_isShared_1583_ = v_isSharedCheck_1599_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1580_);
                        crate::leanh::lean_dec(v___x_1579_);
                        v___x_1582_ = crate::leanh::lean_box(0);
                        v_isShared_1583_ = v_isSharedCheck_1599_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1573_);
                    v_a_1600_ = crate::leanh::lean_ctor_get(v___x_1579_, 0);
                    v_isSharedCheck_1607_ = (!crate::leanh::lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1607_ == 0 {
                        v___x_1602_ = v___x_1579_;
                        v_isShared_1603_ = v_isSharedCheck_1607_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1600_);
                        crate::leanh::lean_dec(v___x_1579_);
                        v___x_1602_ = crate::leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1607_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1580_) == 1 {
                    v_val_1584_ = crate::leanh::lean_ctor_get(v_a_1580_, 0);
                    crate::leanh::lean_inc(v_val_1584_);
                    crate::leanh::lean_dec_ref_known(v_a_1580_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1584_) == 1 {
                        v_tail_1585_ = crate::leanh::lean_ctor_get(v_val_1584_, 1);
                        if crate::leanh::lean_obj_tag(v_tail_1585_) == 0 {
                            crate::leanh::lean_dec(v_mvarId_1573_);
                            v_head_1586_ = crate::leanh::lean_ctor_get(v_val_1584_, 0);
                            crate::leanh::lean_inc(v_head_1586_);
                            crate::leanh::lean_dec_ref_known(v_val_1584_, 2);
                            if v_isShared_1583_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1582_, 0, v_head_1586_);
                                v___x_1588_ = v___x_1582_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1589_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1589_,
                                    0,
                                    v_head_1586_,
                                );
                                v___x_1588_ = v_reuseFailAlloc_1589_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_val_1584_, 2);
                            if v_isShared_1583_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1582_, 0, v_mvarId_1573_);
                                v___x_1591_ = v___x_1582_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1592_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1592_,
                                    0,
                                    v_mvarId_1573_,
                                );
                                v___x_1591_ = v_reuseFailAlloc_1592_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1584_);
                        if v_isShared_1583_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1582_, 0, v_mvarId_1573_);
                            v___x_1594_ = v___x_1582_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1595_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_mvarId_1573_);
                            v___x_1594_ = v_reuseFailAlloc_1595_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1580_);
                    if v_isShared_1583_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1582_, 0, v_mvarId_1573_);
                        v___x_1597_ = v___x_1582_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_mvarId_1573_);
                        v___x_1597_ = v_reuseFailAlloc_1598_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1588_;
            }
            3 => {
                return v___x_1591_;
            }
            4 => {
                return v___x_1594_;
            }
            5 => {
                return v___x_1597_;
            }
            6 => {
                if v_isShared_1603_ == 0 {
                    v___x_1605_ = v___x_1602_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
                    v___x_1605_ = v_reuseFailAlloc_1606_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_eqOfHEq___lam__1___boxed(
    mut v___f_1608_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1615_ = l_Lean_MVarId_eqOfHEq___lam__1(
        v___f_1608_,
        v_mvarId_1609_,
        v___y_1610_,
        v___y_1611_,
        v___y_1612_,
        v___y_1613_,
    );
    crate::leanh::lean_dec(v___y_1613_);
    crate::leanh::lean_dec_ref(v___y_1612_);
    crate::leanh::lean_dec(v___y_1611_);
    crate::leanh::lean_dec_ref(v___y_1610_);
    return v_res_1615_;
}
pub unsafe fn l_Lean_MVarId_eqOfHEq(
    mut v_mvarId_1616_: *mut crate::leanh::LeanObject,
    mut v_a_1617_: *mut crate::leanh::LeanObject,
    mut v_a_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_mvarId_1616_, 2);
    v___f_1622_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_eqOfHEq___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1622_, 0, v_mvarId_1616_);
    v___f_1623_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_eqOfHEq___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1623_, 0, v___f_1622_);
    crate::leanh::lean_closure_set(v___f_1623_, 1, v_mvarId_1616_);
    v___x_1624_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(
        v_mvarId_1616_,
        v___f_1623_,
        v_a_1617_,
        v_a_1618_,
        v_a_1619_,
        v_a_1620_,
    );
    return v___x_1624_;
}
pub unsafe fn l_Lean_MVarId_eqOfHEq___boxed(
    mut v_mvarId_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_MVarId_eqOfHEq(v_mvarId_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
    crate::leanh::lean_dec(v_a_1629_);
    crate::leanh::lean_dec_ref(v_a_1628_);
    crate::leanh::lean_dec(v_a_1627_);
    crate::leanh::lean_dec_ref(v_a_1626_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_MVarId_hrefl___lam__0(
    mut v_mvarId_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1642_ = l_Lean_Meta_mkFreshLevelMVar(
                    v___y_1637_,
                    v___y_1638_,
                    v___y_1639_,
                    v___y_1640_,
                );
                if crate::leanh::lean_obj_tag(v___x_1642_) == 0 {
                    v_a_1643_ = crate::leanh::lean_ctor_get(v___x_1642_, 0);
                    crate::leanh::lean_inc(v_a_1643_);
                    crate::leanh::lean_dec_ref_known(v___x_1642_, 1);
                    v___x_1644_ = l_Lean_MVarId_hrefl___lam__0___closed__1;
                    v___x_1645_ = crate::leanh::lean_box(0);
                    v___x_1646_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1646_, 0, v_a_1643_);
                    crate::leanh::lean_ctor_set(v___x_1646_, 1, v___x_1645_);
                    v___x_1647_ = l_Lean_mkConst(v___x_1644_, v___x_1646_);
                    v___x_1648_ = l_Lean_MVarId_heqOfEq___lam__0___closed__2;
                    v___x_1649_ = crate::leanh::lean_box(0);
                    v___x_1650_ = l_Lean_MVarId_apply(
                        v_mvarId_1636_,
                        v___x_1647_,
                        v___x_1648_,
                        v___x_1649_,
                        v___y_1637_,
                        v___y_1638_,
                        v___y_1639_,
                        v___y_1640_,
                    );
                    return v___x_1650_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_1636_);
                    v_a_1651_ = crate::leanh::lean_ctor_get(v___x_1642_, 0);
                    v_isSharedCheck_1658_ = (!crate::leanh::lean_is_exclusive(v___x_1642_)) as u8;
                    if v_isSharedCheck_1658_ == 0 {
                        v___x_1653_ = v___x_1642_;
                        v_isShared_1654_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1651_);
                        crate::leanh::lean_dec(v___x_1642_);
                        v___x_1653_ = crate::leanh::lean_box(0);
                        v_isShared_1654_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1654_ == 0 {
                    v___x_1656_ = v___x_1653_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
                    v___x_1656_ = v_reuseFailAlloc_1657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_hrefl___lam__0___boxed(
    mut v_mvarId_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Lean_MVarId_hrefl___lam__0(
        v_mvarId_1659_,
        v___y_1660_,
        v___y_1661_,
        v___y_1662_,
        v___y_1663_,
    );
    crate::leanh::lean_dec(v___y_1663_);
    crate::leanh::lean_dec_ref(v___y_1662_);
    crate::leanh::lean_dec(v___y_1661_);
    crate::leanh::lean_dec_ref(v___y_1660_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_MVarId_hrefl___lam__1(
    mut v___f_1669_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___y_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut v_a_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1698_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1676_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(
                    v___f_1669_,
                    v___y_1671_,
                    v___y_1672_,
                    v___y_1673_,
                    v___y_1674_,
                );
                if crate::leanh::lean_obj_tag(v___x_1676_) == 0 {
                    v_a_1677_ = crate::leanh::lean_ctor_get(v___x_1676_, 0);
                    v_isSharedCheck_1694_ = (!crate::leanh::lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1694_ == 0 {
                        v___x_1679_ = v___x_1676_;
                        v_isShared_1680_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1677_);
                        crate::leanh::lean_dec(v___x_1676_);
                        v___x_1679_ = crate::leanh::lean_box(0);
                        v_isShared_1680_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1670_);
                    v_a_1695_ = crate::leanh::lean_ctor_get(v___x_1676_, 0);
                    v_isSharedCheck_1702_ = (!crate::leanh::lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1702_ == 0 {
                        v___x_1697_ = v___x_1676_;
                        v_isShared_1698_ = v_isSharedCheck_1702_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1695_);
                        crate::leanh::lean_dec(v___x_1676_);
                        v___x_1697_ = crate::leanh::lean_box(0);
                        v_isShared_1698_ = v_isSharedCheck_1702_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1677_) == 1 {
                    v_val_1689_ = crate::leanh::lean_ctor_get(v_a_1677_, 0);
                    crate::leanh::lean_inc(v_val_1689_);
                    crate::leanh::lean_dec_ref_known(v_a_1677_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1689_) == 0 {
                        crate::leanh::lean_dec(v_mvarId_1670_);
                        v___x_1690_ = crate::leanh::lean_box(0);
                        if v_isShared_1680_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1690_);
                            v___x_1692_ = v___x_1679_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1693_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
                            v___x_1692_ = v_reuseFailAlloc_1693_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1689_);
                        crate::leanh::lean_del_object(v___x_1679_);
                        v___y_1682_ = v___y_1671_;
                        v___y_1683_ = v___y_1672_;
                        v___y_1684_ = v___y_1673_;
                        v___y_1685_ = v___y_1674_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1679_);
                    crate::leanh::lean_dec(v_a_1677_);
                    v___y_1682_ = v___y_1671_;
                    v___y_1683_ = v___y_1672_;
                    v___y_1684_ = v___y_1673_;
                    v___y_1685_ = v___y_1674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1686_ = l_Lean_MVarId_hrefl___lam__1___closed__1;
                v___x_1687_ = crate::leanh::lean_box(0);
                v___x_1688_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1686_,
                    v_mvarId_1670_,
                    v___x_1687_,
                    v___y_1682_,
                    v___y_1683_,
                    v___y_1684_,
                    v___y_1685_,
                );
                return v___x_1688_;
            }
            3 => {
                return v___x_1692_;
            }
            4 => {
                if v_isShared_1698_ == 0 {
                    v___x_1700_ = v___x_1697_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
                    v___x_1700_ = v_reuseFailAlloc_1701_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_hrefl___lam__1___boxed(
    mut v___f_1703_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lean_MVarId_hrefl___lam__1(
        v___f_1703_,
        v_mvarId_1704_,
        v___y_1705_,
        v___y_1706_,
        v___y_1707_,
        v___y_1708_,
    );
    crate::leanh::lean_dec(v___y_1708_);
    crate::leanh::lean_dec_ref(v___y_1707_);
    crate::leanh::lean_dec(v___y_1706_);
    crate::leanh::lean_dec_ref(v___y_1705_);
    return v_res_1710_;
}
pub unsafe fn l_Lean_MVarId_hrefl(
    mut v_mvarId_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_a_1714_: *mut crate::leanh::LeanObject,
    mut v_a_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_mvarId_1711_, 2);
    v___f_1717_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_hrefl___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1717_, 0, v_mvarId_1711_);
    v___f_1718_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_hrefl___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1718_, 0, v___f_1717_);
    crate::leanh::lean_closure_set(v___f_1718_, 1, v_mvarId_1711_);
    v___x_1719_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(
        v_mvarId_1711_,
        v___f_1718_,
        v_a_1712_,
        v_a_1713_,
        v_a_1714_,
        v_a_1715_,
    );
    return v___x_1719_;
}
pub unsafe fn l_Lean_MVarId_hrefl___boxed(
    mut v_mvarId_1720_: *mut crate::leanh::LeanObject,
    mut v_a_1721_: *mut crate::leanh::LeanObject,
    mut v_a_1722_: *mut crate::leanh::LeanObject,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
    mut v_a_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Lean_MVarId_hrefl(v_mvarId_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
    crate::leanh::lean_dec(v_a_1724_);
    crate::leanh::lean_dec_ref(v_a_1723_);
    crate::leanh::lean_dec(v_a_1722_);
    crate::leanh::lean_dec_ref(v_a_1721_);
    return v_res_1726_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Refl(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Reduce(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Refl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Refl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Reduce(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Refl(builtin);
}

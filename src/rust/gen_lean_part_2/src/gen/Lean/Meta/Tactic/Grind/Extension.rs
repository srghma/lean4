// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Extension
// Imports: Lean.Meta.Tactic.Grind.Theorems
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set,
    lean_array_to_list, lean_expr_eqv, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_string_length, lean_uint64_mix_hash,
    lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_eraseIdx___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{l_Lean_mkAtom, l_instInhabitedOfMonad___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_empty, l_Lean_NameSet_insert};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_isUnaryNode___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_const___override, l_Lean_instReprExpr_repr};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Tactic::Grind::Theorems::{
    initialize_Lean_Meta_Tactic_Grind_Theorems, l_Lean_Meta_Grind_Origin_key,
    l_Lean_Meta_Grind_Theorems_mkEmpty, l_Lean_Meta_Grind_instInhabitedOrigin_default,
    l_Lean_Meta_Grind_instInhabitedTheorems_default,
    runtime_initialize_Lean_Meta_Tactic_Grind_Theorems,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_registerSimpleScopedEnvExtension___redArg;
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCasesTypes: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqEMatchTheoremKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 114, 105, 103, 104, 116,
        76, 101, 102, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 108, 101, 102, 116, 82,
        105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 101, 113, 66, 119, 100,
        0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 102, 119, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value:
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 117, 115, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 101, 113, 76, 104, 115,
        0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 101, 113, 82, 104, 115,
        0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 101, 113, 66, 111, 116,
        104, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 98, 119, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 100, 101, 102, 97, 117,
        108, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9: u64 = 0;
pub static l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0_value:
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
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqCnstrRHS: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [108, 101, 118, 101, 108, 78, 97, 109, 101, 115, 0],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [110, 117, 109, 77, 86, 97, 114, 115, 0],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value:
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
    m_data: [101, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instReprCnstrRHS___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instReprCnstrRHS: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 110, 111, 116, 68, 101, 102, 69, 113, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 100, 101, 102, 69, 113, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value:
    leanh::LeanStringObject<47> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 115, 105, 122, 101, 76, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 100, 101, 112, 116, 104, 76, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 103, 101, 110, 76, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 105, 115, 71, 114, 111, 117, 110, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 105, 115, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 109, 97, 120, 73, 110, 115, 116, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 103, 117, 97, 114, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 99, 104, 101, 99, 107, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116,
        46, 110, 111, 116, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value:
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
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEntry_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedExtensionState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject;
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 84, 104, 101, 111, 114, 101, 109, 115, 46, 105, 110, 115, 101, 114, 116, 0]};
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value:
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__5_value:
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__9_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value:
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
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value)
            as *mut leanh::LeanObject,
        14997215300048349804 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value)
            as *mut leanh::LeanObject,
        7677164612348466033 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__17_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_mkExtension___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___lam__0___closed__0_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105,
        110, 100, 46, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___lam__0___closed__1_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 69, 120,
        116, 101, 110, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_mkExtension___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_mkExtension___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_mkExtension___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_mkExtension___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_ExtensionState_addEntry as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_mkExtension___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 109, 97, 114, 107, 101, 100, 32, 119, 105, 116,
        104, 32, 116, 104, 101, 32, 96, 91, 103, 114, 105, 110, 100, 93, 96, 32, 97, 116, 116, 114,
        105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2680_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2680_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once),
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0,
    );
    v___x_2682_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2682_, 0, v___x_2681_);
    return v___x_2682_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default()
-> *mut leanh::LeanObject {
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once),
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1,
    );
    return v___x_2683_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes() -> *mut leanh::LeanObject {
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2684_ = l_Lean_Meta_Grind_instInhabitedCasesTypes_default;
    return v___x_2684_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2685_: *mut leanh::LeanObject,
    mut v_x_2686_: *mut leanh::LeanObject,
    mut v_x_2687_: *mut leanh::LeanObject,
    mut v_x_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: u8 = 0;
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2689_ = leanh::lean_ctor_get(v_x_2685_, 0);
                v_vs_2690_ = leanh::lean_ctor_get(v_x_2685_, 1);
                v_isSharedCheck_2714_ = (!leanh::lean_is_exclusive(v_x_2685_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v___x_2692_ = v_x_2685_;
                    v_isShared_2693_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2690_);
                    leanh::lean_inc(v_ks_2689_);
                    leanh::lean_dec(v_x_2685_);
                    v___x_2692_ = leanh::lean_box(0);
                    v_isShared_2693_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2694_ = lean_array_get_size(v_ks_2689_);
                v___x_2695_ = lean_nat_dec_lt(v_x_2686_, v___x_2694_);
                if v___x_2695_ == 0 {
                    leanh::lean_dec(v_x_2686_);
                    v___x_2696_ = lean_array_push(v_ks_2689_, v_x_2687_);
                    v___x_2697_ = lean_array_push(v_vs_2690_, v_x_2688_);
                    if v_isShared_2693_ == 0 {
                        leanh::lean_ctor_set(v___x_2692_, 1, v___x_2697_);
                        leanh::lean_ctor_set(v___x_2692_, 0, v___x_2696_);
                        v___x_2699_ = v___x_2692_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2700_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2697_);
                        v___x_2699_ = v_reuseFailAlloc_2700_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2701_ = lean_array_fget_borrowed(v_ks_2689_, v_x_2686_);
                    v___x_2702_ = lean_name_eq(v_x_2687_, v_k_x27_2701_);
                    if v___x_2702_ == 0 {
                        if v_isShared_2693_ == 0 {
                            v___x_2704_ = v___x_2692_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2708_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_ks_2689_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_vs_2690_);
                            v___x_2704_ = v_reuseFailAlloc_2708_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2709_ = lean_array_fset(v_ks_2689_, v_x_2686_, v_x_2687_);
                        v___x_2710_ = lean_array_fset(v_vs_2690_, v_x_2686_, v_x_2688_);
                        leanh::lean_dec(v_x_2686_);
                        if v_isShared_2693_ == 0 {
                            leanh::lean_ctor_set(v___x_2692_, 1, v___x_2710_);
                            leanh::lean_ctor_set(v___x_2692_, 0, v___x_2709_);
                            v___x_2712_ = v___x_2692_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2713_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2709_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2710_);
                            v___x_2712_ = v_reuseFailAlloc_2713_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2699_;
            }
            3 => {
                v___x_2705_ = leanh::lean_unsigned_to_nat(1);
                v___x_2706_ = lean_nat_add(v_x_2686_, v___x_2705_);
                leanh::lean_dec(v_x_2686_);
                v_x_2685_ = v___x_2704_;
                v_x_2686_ = v___x_2706_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(
    mut v_n_2715_: *mut leanh::LeanObject,
    mut v_k_2716_: *mut leanh::LeanObject,
    mut v_v_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2718_ = leanh::lean_unsigned_to_nat(0);
    v___x_2719_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2715_, v___x_2718_, v_k_2716_, v_v_2717_);
    return v___x_2719_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: u64 = 0;
    v___x_2720_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2721_ = lean_uint64_of_nat(v___x_2720_);
    return v___x_2721_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2722_: usize = 0;
    let mut v___x_2723_: usize = 0;
    let mut v___x_2724_: usize = 0;
    v___x_2722_ = 5usize;
    v___x_2723_ = 1usize;
    v___x_2724_ = lean_usize_shift_left(v___x_2723_, v___x_2722_);
    return v___x_2724_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2725_: usize = 0;
    let mut v___x_2726_: usize = 0;
    let mut v___x_2727_: usize = 0;
    v___x_2725_ = 1usize;
    v___x_2726_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
    v___x_2727_ = lean_usize_sub(v___x_2726_, v___x_2725_);
    return v___x_2727_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2728_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(
    mut v_x_2729_: *mut leanh::LeanObject,
    mut v_x_2730_: usize,
    mut v_x_2731_: usize,
    mut v_x_2732_: *mut leanh::LeanObject,
    mut v_x_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: usize = 0;
    let mut v___x_2736_: usize = 0;
    let mut v___x_2737_: usize = 0;
    let mut v___x_2738_: usize = 0;
    let mut v_j_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v_v_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2765_: u8 = 0;
    let mut v_node_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2769_: u8 = 0;
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2778_: u8 = 0;
    let mut v_unused_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: u8 = 0;
    let mut v_ks_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: usize = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: u8 = 0;
    let mut v_reuseFailAlloc_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2729_) == 0 {
                    v_es_2734_ = leanh::lean_ctor_get(v_x_2729_, 0);
                    v___x_2735_ = 5usize;
                    v___x_2736_ = 1usize;
                    v___x_2737_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_2738_ = lean_usize_land(v_x_2730_, v___x_2737_);
                    v_j_2739_ = lean_usize_to_nat(v___x_2738_);
                    v___x_2740_ = lean_array_get_size(v_es_2734_);
                    v___x_2741_ = lean_nat_dec_lt(v_j_2739_, v___x_2740_);
                    if v___x_2741_ == 0 {
                        leanh::lean_dec(v_j_2739_);
                        leanh::lean_dec(v_x_2733_);
                        leanh::lean_dec(v_x_2732_);
                        return v_x_2729_;
                    } else {
                        leanh::lean_inc_ref(v_es_2734_);
                        v_isSharedCheck_2778_ = (!leanh::lean_is_exclusive(v_x_2729_)) as u8;
                        if v_isSharedCheck_2778_ == 0 {
                            v_unused_2779_ = leanh::lean_ctor_get(v_x_2729_, 0);
                            leanh::lean_dec(v_unused_2779_);
                            v___x_2743_ = v_x_2729_;
                            v_isShared_2744_ = v_isSharedCheck_2778_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2729_);
                            v___x_2743_ = leanh::lean_box(0);
                            v_isShared_2744_ = v_isSharedCheck_2778_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2780_ = leanh::lean_ctor_get(v_x_2729_, 0);
                    v_vs_2781_ = leanh::lean_ctor_get(v_x_2729_, 1);
                    v_isSharedCheck_2801_ = (!leanh::lean_is_exclusive(v_x_2729_)) as u8;
                    if v_isSharedCheck_2801_ == 0 {
                        v___x_2783_ = v_x_2729_;
                        v_isShared_2784_ = v_isSharedCheck_2801_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2781_);
                        leanh::lean_inc(v_ks_2780_);
                        leanh::lean_dec(v_x_2729_);
                        v___x_2783_ = leanh::lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2801_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2745_ = lean_array_fget(v_es_2734_, v_j_2739_);
                v___x_2746_ = leanh::lean_box(0);
                v_xs_x27_2747_ = lean_array_fset(v_es_2734_, v_j_2739_, v___x_2746_);
                match leanh::lean_obj_tag(v_v_2745_) {
                    0 => {
                        v_key_2754_ = leanh::lean_ctor_get(v_v_2745_, 0);
                        v_val_2755_ = leanh::lean_ctor_get(v_v_2745_, 1);
                        v_isSharedCheck_2765_ = (!leanh::lean_is_exclusive(v_v_2745_)) as u8;
                        if v_isSharedCheck_2765_ == 0 {
                            v___x_2757_ = v_v_2745_;
                            v_isShared_2758_ = v_isSharedCheck_2765_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2755_);
                            leanh::lean_inc(v_key_2754_);
                            leanh::lean_dec(v_v_2745_);
                            v___x_2757_ = leanh::lean_box(0);
                            v_isShared_2758_ = v_isSharedCheck_2765_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2766_ = leanh::lean_ctor_get(v_v_2745_, 0);
                        v_isSharedCheck_2776_ = (!leanh::lean_is_exclusive(v_v_2745_)) as u8;
                        if v_isSharedCheck_2776_ == 0 {
                            v___x_2768_ = v_v_2745_;
                            v_isShared_2769_ = v_isSharedCheck_2776_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2766_);
                            leanh::lean_dec(v_v_2745_);
                            v___x_2768_ = leanh::lean_box(0);
                            v_isShared_2769_ = v_isSharedCheck_2776_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2777_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2777_, 0, v_x_2732_);
                        leanh::lean_ctor_set(v___x_2777_, 1, v_x_2733_);
                        v___y_2749_ = v___x_2777_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2750_ = lean_array_fset(v_xs_x27_2747_, v_j_2739_, v___y_2749_);
                leanh::lean_dec(v_j_2739_);
                if v_isShared_2744_ == 0 {
                    leanh::lean_ctor_set(v___x_2743_, 0, v___x_2750_);
                    v___x_2752_ = v___x_2743_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2753_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
                    v___x_2752_ = v_reuseFailAlloc_2753_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2752_;
            }
            4 => {
                v___x_2759_ = lean_name_eq(v_x_2732_, v_key_2754_);
                if v___x_2759_ == 0 {
                    leanh::lean_del_object(v___x_2757_);
                    v___x_2760_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2754_,
                        v_val_2755_,
                        v_x_2732_,
                        v_x_2733_,
                    );
                    v___x_2761_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2761_, 0, v___x_2760_);
                    v___y_2749_ = v___x_2761_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2755_);
                    leanh::lean_dec(v_key_2754_);
                    if v_isShared_2758_ == 0 {
                        leanh::lean_ctor_set(v___x_2757_, 1, v_x_2733_);
                        leanh::lean_ctor_set(v___x_2757_, 0, v_x_2732_);
                        v___x_2763_ = v___x_2757_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2764_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_x_2732_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_x_2733_);
                        v___x_2763_ = v_reuseFailAlloc_2764_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2749_ = v___x_2763_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2770_ = lean_usize_shift_right(v_x_2730_, v___x_2735_);
                v___x_2771_ = lean_usize_add(v_x_2731_, v___x_2736_);
                v___x_2772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_node_2766_, v___x_2770_, v___x_2771_, v_x_2732_, v_x_2733_);
                if v_isShared_2769_ == 0 {
                    leanh::lean_ctor_set(v___x_2768_, 0, v___x_2772_);
                    v___x_2774_ = v___x_2768_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
                    v___x_2774_ = v_reuseFailAlloc_2775_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2749_ = v___x_2774_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2784_ == 0 {
                    v___x_2786_ = v___x_2783_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2800_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_ks_2780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_vs_2781_);
                    v___x_2786_ = v_reuseFailAlloc_2800_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2787_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v___x_2786_, v_x_2732_, v_x_2733_);
                v___x_2795_ = 7usize;
                v___x_2796_ = lean_usize_dec_le(v___x_2795_, v_x_2731_);
                if v___x_2796_ == 0 {
                    v___x_2797_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2787_);
                    v___x_2798_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2799_ = lean_nat_dec_lt(v___x_2797_, v___x_2798_);
                    leanh::lean_dec(v___x_2797_);
                    v___y_2789_ = v___x_2799_;
                    state = 10;
                    continue;
                } else {
                    v___y_2789_ = v___x_2796_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2789_ == 0 {
                    v_ks_2790_ = leanh::lean_ctor_get(v_newNode_2787_, 0);
                    leanh::lean_inc_ref(v_ks_2790_);
                    v_vs_2791_ = leanh::lean_ctor_get(v_newNode_2787_, 1);
                    leanh::lean_inc_ref(v_vs_2791_);
                    leanh::lean_dec_ref(v_newNode_2787_);
                    v___x_2792_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2793_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2);
                    v___x_2794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_x_2731_, v_ks_2790_, v_vs_2791_, v___x_2792_, v___x_2793_);
                    leanh::lean_dec_ref(v_vs_2791_);
                    leanh::lean_dec_ref(v_ks_2790_);
                    return v___x_2794_;
                } else {
                    return v_newNode_2787_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(
    mut v_depth_2802_: usize,
    mut v_keys_2803_: *mut leanh::LeanObject,
    mut v_vals_2804_: *mut leanh::LeanObject,
    mut v_i_2805_: *mut leanh::LeanObject,
    mut v_entries_2806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v_k_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: u64 = 0;
    let mut v_h_2813_: usize = 0;
    let mut v___x_2814_: usize = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: usize = 0;
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: usize = 0;
    let mut v_h_2819_: usize = 0;
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: u64 = 0;
    let mut v_hash_2824_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2807_ = lean_array_get_size(v_keys_2803_);
                v___x_2808_ = lean_nat_dec_lt(v_i_2805_, v___x_2807_);
                if v___x_2808_ == 0 {
                    leanh::lean_dec(v_i_2805_);
                    return v_entries_2806_;
                } else {
                    v_k_2809_ = lean_array_fget_borrowed(v_keys_2803_, v_i_2805_);
                    v_v_2810_ = lean_array_fget_borrowed(v_vals_2804_, v_i_2805_);
                    if leanh::lean_obj_tag(v_k_2809_) == 0 {
                        v___x_2823_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_2812_ = v___x_2823_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2824_ = leanh::lean_ctor_get_uint64(
                            v_k_2809_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2812_ = v_hash_2824_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2813_ = lean_uint64_to_usize(v___y_2812_);
                v___x_2814_ = 5usize;
                v___x_2815_ = leanh::lean_unsigned_to_nat(1);
                v___x_2816_ = 1usize;
                v___x_2817_ = lean_usize_sub(v_depth_2802_, v___x_2816_);
                v___x_2818_ = lean_usize_mul(v___x_2814_, v___x_2817_);
                v_h_2819_ = lean_usize_shift_right(v_h_2813_, v___x_2818_);
                v___x_2820_ = lean_nat_add(v_i_2805_, v___x_2815_);
                leanh::lean_dec(v_i_2805_);
                leanh::lean_inc(v_v_2810_);
                leanh::lean_inc(v_k_2809_);
                v___x_2821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_entries_2806_, v_h_2819_, v_depth_2802_, v_k_2809_, v_v_2810_);
                v_i_2805_ = v___x_2820_;
                v_entries_2806_ = v___x_2821_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_2825_: *mut leanh::LeanObject,
    mut v_keys_2826_: *mut leanh::LeanObject,
    mut v_vals_2827_: *mut leanh::LeanObject,
    mut v_i_2828_: *mut leanh::LeanObject,
    mut v_entries_2829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2830_: usize = 0;
    let mut v_res_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2830_ = leanh::lean_unbox_usize(v_depth_2825_);
    leanh::lean_dec(v_depth_2825_);
    v_res_2831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2830_, v_keys_2826_, v_vals_2827_, v_i_2828_, v_entries_2829_);
    leanh::lean_dec_ref(v_vals_2827_);
    leanh::lean_dec_ref(v_keys_2826_);
    return v_res_2831_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_2832_: *mut leanh::LeanObject,
    mut v_x_2833_: *mut leanh::LeanObject,
    mut v_x_2834_: *mut leanh::LeanObject,
    mut v_x_2835_: *mut leanh::LeanObject,
    mut v_x_2836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_371__boxed_2837_: usize = 0;
    let mut v_x_372__boxed_2838_: usize = 0;
    let mut v_res_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_371__boxed_2837_ = leanh::lean_unbox_usize(v_x_2833_);
    leanh::lean_dec(v_x_2833_);
    v_x_372__boxed_2838_ = leanh::lean_unbox_usize(v_x_2834_);
    leanh::lean_dec(v_x_2834_);
    v_res_2839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_2832_, v_x_371__boxed_2837_, v_x_372__boxed_2838_, v_x_2835_, v_x_2836_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
    mut v_x_2840_: *mut leanh::LeanObject,
    mut v_x_2841_: *mut leanh::LeanObject,
    mut v_x_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2844_: u64 = 0;
    let mut v___x_2845_: usize = 0;
    let mut v___x_2846_: usize = 0;
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: u64 = 0;
    let mut v_hash_2849_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2841_) == 0 {
                    v___x_2848_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2844_ = v___x_2848_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2849_ = leanh::lean_ctor_get_uint64(
                        v_x_2841_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2844_ = v_hash_2849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2845_ = lean_uint64_to_usize(v___y_2844_);
                v___x_2846_ = 1usize;
                v___x_2847_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_2840_, v___x_2845_, v___x_2846_, v_x_2841_, v_x_2842_);
                return v___x_2847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_insert(
    mut v_s_2850_: *mut leanh::LeanObject,
    mut v_declName_2851_: *mut leanh::LeanObject,
    mut v_eager_2852_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = leanh::lean_box((v_eager_2852_) as usize);
    v___x_2854_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
            v_s_2850_,
            v_declName_2851_,
            v___x_2853_,
        );
    return v___x_2854_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_insert___boxed(
    mut v_s_2855_: *mut leanh::LeanObject,
    mut v_declName_2856_: *mut leanh::LeanObject,
    mut v_eager_2857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eager_boxed_2858_: u8 = 0;
    let mut v_res_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eager_boxed_2858_ = (leanh::lean_unbox(v_eager_2857_) as u8);
    v_res_2859_ =
        l_Lean_Meta_Grind_CasesTypes_insert(v_s_2855_, v_declName_2856_, v_eager_boxed_2858_);
    return v_res_2859_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(
    mut v_00_u03b2_2860_: *mut leanh::LeanObject,
    mut v_x_2861_: *mut leanh::LeanObject,
    mut v_x_2862_: *mut leanh::LeanObject,
    mut v_x_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2864_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
            v_x_2861_, v_x_2862_, v_x_2863_,
        );
    return v___x_2864_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(
    mut v_00_u03b2_2865_: *mut leanh::LeanObject,
    mut v_x_2866_: *mut leanh::LeanObject,
    mut v_x_2867_: usize,
    mut v_x_2868_: usize,
    mut v_x_2869_: *mut leanh::LeanObject,
    mut v_x_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_2866_, v_x_2867_, v_x_2868_, v_x_2869_, v_x_2870_);
    return v___x_2871_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_2872_: *mut leanh::LeanObject,
    mut v_x_2873_: *mut leanh::LeanObject,
    mut v_x_2874_: *mut leanh::LeanObject,
    mut v_x_2875_: *mut leanh::LeanObject,
    mut v_x_2876_: *mut leanh::LeanObject,
    mut v_x_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_570__boxed_2878_: usize = 0;
    let mut v_x_571__boxed_2879_: usize = 0;
    let mut v_res_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_570__boxed_2878_ = leanh::lean_unbox_usize(v_x_2874_);
    leanh::lean_dec(v_x_2874_);
    v_x_571__boxed_2879_ = leanh::lean_unbox_usize(v_x_2875_);
    leanh::lean_dec(v_x_2875_);
    v_res_2880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(v_00_u03b2_2872_, v_x_2873_, v_x_570__boxed_2878_, v_x_571__boxed_2879_, v_x_2876_, v_x_2877_);
    return v_res_2880_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2881_: *mut leanh::LeanObject,
    mut v_n_2882_: *mut leanh::LeanObject,
    mut v_k_2883_: *mut leanh::LeanObject,
    mut v_v_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v_n_2882_, v_k_2883_, v_v_2884_);
    return v___x_2885_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2886_: *mut leanh::LeanObject,
    mut v_depth_2887_: usize,
    mut v_keys_2888_: *mut leanh::LeanObject,
    mut v_vals_2889_: *mut leanh::LeanObject,
    mut v_heq_2890_: *mut leanh::LeanObject,
    mut v_i_2891_: *mut leanh::LeanObject,
    mut v_entries_2892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_2887_, v_keys_2888_, v_vals_2889_, v_i_2891_, v_entries_2892_);
    return v___x_2893_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2894_: *mut leanh::LeanObject,
    mut v_depth_2895_: *mut leanh::LeanObject,
    mut v_keys_2896_: *mut leanh::LeanObject,
    mut v_vals_2897_: *mut leanh::LeanObject,
    mut v_heq_2898_: *mut leanh::LeanObject,
    mut v_i_2899_: *mut leanh::LeanObject,
    mut v_entries_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2901_: usize = 0;
    let mut v_res_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2901_ = leanh::lean_unbox_usize(v_depth_2895_);
    leanh::lean_dec(v_depth_2895_);
    v_res_2902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(v_00_u03b2_2894_, v_depth_boxed_2901_, v_keys_2896_, v_vals_2897_, v_heq_2898_, v_i_2899_, v_entries_2900_);
    leanh::lean_dec_ref(v_vals_2897_);
    leanh::lean_dec_ref(v_keys_2896_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2903_: *mut leanh::LeanObject,
    mut v_x_2904_: *mut leanh::LeanObject,
    mut v_x_2905_: *mut leanh::LeanObject,
    mut v_x_2906_: *mut leanh::LeanObject,
    mut v_x_2907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2908_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2904_, v_x_2905_, v_x_2906_, v_x_2907_);
    return v___x_2908_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2909_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2910_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0,
    );
    v___x_2911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2911_, 0, v___x_2910_);
    return v___x_2911_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default()
-> *mut leanh::LeanObject {
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2912_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1,
    );
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities()
-> *mut leanh::LeanObject {
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ = l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default;
    return v___x_2913_;
}
pub unsafe fn l_Lean_Meta_Grind_SymbolPriorities_insert(
    mut v_s_2914_: *mut leanh::LeanObject,
    mut v_declName_2915_: *mut leanh::LeanObject,
    mut v_prio_2916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
            v_s_2914_,
            v_declName_2915_,
            v_prio_2916_,
        );
    return v___x_2917_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(
    mut v_x_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2918_) {
        0 => {
            let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2919_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2919_;
        }
        1 => {
            let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2920_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2920_;
        }
        2 => {
            let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2921_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2921_;
        }
        3 => {
            let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2922_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2922_;
        }
        4 => {
            let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2923_ = leanh::lean_unsigned_to_nat(4);
            return v___x_2923_;
        }
        5 => {
            let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2924_ = leanh::lean_unsigned_to_nat(5);
            return v___x_2924_;
        }
        6 => {
            let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2925_ = leanh::lean_unsigned_to_nat(6);
            return v___x_2925_;
        }
        7 => {
            let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2926_ = leanh::lean_unsigned_to_nat(7);
            return v___x_2926_;
        }
        8 => {
            let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2927_ = leanh::lean_unsigned_to_nat(8);
            return v___x_2927_;
        }
        _ => {
            let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2928_ = leanh::lean_unsigned_to_nat(9);
            return v___x_2928_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___boxed(
    mut v_x_2929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_2929_);
    leanh::lean_dec(v_x_2929_);
    return v_res_2930_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(
    mut v_t_2931_: *mut leanh::LeanObject,
    mut v_k_2932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2931_) {
        0 => {
            let mut v_gen_2933_: u8 = 0;
            let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_gen_2933_ = leanh::lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2934_ = leanh::lean_box((v_gen_2933_) as usize);
            v___x_2935_ = leanh::lean_apply_1(v_k_2932_, v___x_2934_);
            return v___x_2935_;
        }
        1 => {
            let mut v_gen_2936_: u8 = 0;
            let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_gen_2936_ = leanh::lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2937_ = leanh::lean_box((v_gen_2936_) as usize);
            v___x_2938_ = leanh::lean_apply_1(v_k_2932_, v___x_2937_);
            return v___x_2938_;
        }
        2 => {
            let mut v_gen_2939_: u8 = 0;
            let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_gen_2939_ = leanh::lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2940_ = leanh::lean_box((v_gen_2939_) as usize);
            v___x_2941_ = leanh::lean_apply_1(v_k_2932_, v___x_2940_);
            return v___x_2941_;
        }
        5 => {
            let mut v_gen_2942_: u8 = 0;
            let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_gen_2942_ = leanh::lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2943_ = leanh::lean_box((v_gen_2942_) as usize);
            v___x_2944_ = leanh::lean_apply_1(v_k_2932_, v___x_2943_);
            return v___x_2944_;
        }
        8 => {
            let mut v_gen_2945_: u8 = 0;
            let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_gen_2945_ = leanh::lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2946_ = leanh::lean_box((v_gen_2945_) as usize);
            v___x_2947_ = leanh::lean_apply_1(v_k_2932_, v___x_2946_);
            return v___x_2947_;
        }
        _ => {
            return v_k_2932_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(
    mut v_t_2948_: *mut leanh::LeanObject,
    mut v_k_2949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2948_, v_k_2949_);
    leanh::lean_dec(v_t_2948_);
    return v_res_2950_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(
    mut v_motive_2951_: *mut leanh::LeanObject,
    mut v_ctorIdx_2952_: *mut leanh::LeanObject,
    mut v_t_2953_: *mut leanh::LeanObject,
    mut v_h_2954_: *mut leanh::LeanObject,
    mut v_k_2955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2956_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2953_, v_k_2955_);
    return v___x_2956_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(
    mut v_motive_2957_: *mut leanh::LeanObject,
    mut v_ctorIdx_2958_: *mut leanh::LeanObject,
    mut v_t_2959_: *mut leanh::LeanObject,
    mut v_h_2960_: *mut leanh::LeanObject,
    mut v_k_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(
        v_motive_2957_,
        v_ctorIdx_2958_,
        v_t_2959_,
        v_h_2960_,
        v_k_2961_,
    );
    leanh::lean_dec(v_t_2959_);
    leanh::lean_dec(v_ctorIdx_2958_);
    return v_res_2962_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(
    mut v_t_2963_: *mut leanh::LeanObject,
    mut v_eqLhs_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2965_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2963_, v_eqLhs_2964_);
    return v___x_2965_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(
    mut v_t_2966_: *mut leanh::LeanObject,
    mut v_eqLhs_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(v_t_2966_, v_eqLhs_2967_);
    leanh::lean_dec(v_t_2966_);
    return v_res_2968_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(
    mut v_motive_2969_: *mut leanh::LeanObject,
    mut v_t_2970_: *mut leanh::LeanObject,
    mut v_h_2971_: *mut leanh::LeanObject,
    mut v_eqLhs_2972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2970_, v_eqLhs_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(
    mut v_motive_2974_: *mut leanh::LeanObject,
    mut v_t_2975_: *mut leanh::LeanObject,
    mut v_h_2976_: *mut leanh::LeanObject,
    mut v_eqLhs_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(
        v_motive_2974_,
        v_t_2975_,
        v_h_2976_,
        v_eqLhs_2977_,
    );
    leanh::lean_dec(v_t_2975_);
    return v_res_2978_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(
    mut v_t_2979_: *mut leanh::LeanObject,
    mut v_eqRhs_2980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2981_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2979_, v_eqRhs_2980_);
    return v___x_2981_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(
    mut v_t_2982_: *mut leanh::LeanObject,
    mut v_eqRhs_2983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(v_t_2982_, v_eqRhs_2983_);
    leanh::lean_dec(v_t_2982_);
    return v_res_2984_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(
    mut v_motive_2985_: *mut leanh::LeanObject,
    mut v_t_2986_: *mut leanh::LeanObject,
    mut v_h_2987_: *mut leanh::LeanObject,
    mut v_eqRhs_2988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2986_, v_eqRhs_2988_);
    return v___x_2989_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(
    mut v_motive_2990_: *mut leanh::LeanObject,
    mut v_t_2991_: *mut leanh::LeanObject,
    mut v_h_2992_: *mut leanh::LeanObject,
    mut v_eqRhs_2993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2994_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(
        v_motive_2990_,
        v_t_2991_,
        v_h_2992_,
        v_eqRhs_2993_,
    );
    leanh::lean_dec(v_t_2991_);
    return v_res_2994_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(
    mut v_t_2995_: *mut leanh::LeanObject,
    mut v_eqBoth_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2997_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2995_, v_eqBoth_2996_);
    return v___x_2997_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(
    mut v_t_2998_: *mut leanh::LeanObject,
    mut v_eqBoth_2999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3000_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(v_t_2998_, v_eqBoth_2999_);
    leanh::lean_dec(v_t_2998_);
    return v_res_3000_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(
    mut v_motive_3001_: *mut leanh::LeanObject,
    mut v_t_3002_: *mut leanh::LeanObject,
    mut v_h_3003_: *mut leanh::LeanObject,
    mut v_eqBoth_3004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3005_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3002_, v_eqBoth_3004_);
    return v___x_3005_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(
    mut v_motive_3006_: *mut leanh::LeanObject,
    mut v_t_3007_: *mut leanh::LeanObject,
    mut v_h_3008_: *mut leanh::LeanObject,
    mut v_eqBoth_3009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(
        v_motive_3006_,
        v_t_3007_,
        v_h_3008_,
        v_eqBoth_3009_,
    );
    leanh::lean_dec(v_t_3007_);
    return v_res_3010_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(
    mut v_t_3011_: *mut leanh::LeanObject,
    mut v_eqBwd_3012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3013_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3011_, v_eqBwd_3012_);
    return v___x_3013_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(
    mut v_t_3014_: *mut leanh::LeanObject,
    mut v_eqBwd_3015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(v_t_3014_, v_eqBwd_3015_);
    leanh::lean_dec(v_t_3014_);
    return v_res_3016_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(
    mut v_motive_3017_: *mut leanh::LeanObject,
    mut v_t_3018_: *mut leanh::LeanObject,
    mut v_h_3019_: *mut leanh::LeanObject,
    mut v_eqBwd_3020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3021_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3018_, v_eqBwd_3020_);
    return v___x_3021_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(
    mut v_motive_3022_: *mut leanh::LeanObject,
    mut v_t_3023_: *mut leanh::LeanObject,
    mut v_h_3024_: *mut leanh::LeanObject,
    mut v_eqBwd_3025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(
        v_motive_3022_,
        v_t_3023_,
        v_h_3024_,
        v_eqBwd_3025_,
    );
    leanh::lean_dec(v_t_3023_);
    return v_res_3026_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(
    mut v_t_3027_: *mut leanh::LeanObject,
    mut v_fwd_3028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3029_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3027_, v_fwd_3028_);
    return v___x_3029_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(
    mut v_t_3030_: *mut leanh::LeanObject,
    mut v_fwd_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3032_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(v_t_3030_, v_fwd_3031_);
    leanh::lean_dec(v_t_3030_);
    return v_res_3032_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(
    mut v_motive_3033_: *mut leanh::LeanObject,
    mut v_t_3034_: *mut leanh::LeanObject,
    mut v_h_3035_: *mut leanh::LeanObject,
    mut v_fwd_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3037_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3034_, v_fwd_3036_);
    return v___x_3037_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(
    mut v_motive_3038_: *mut leanh::LeanObject,
    mut v_t_3039_: *mut leanh::LeanObject,
    mut v_h_3040_: *mut leanh::LeanObject,
    mut v_fwd_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(
        v_motive_3038_,
        v_t_3039_,
        v_h_3040_,
        v_fwd_3041_,
    );
    leanh::lean_dec(v_t_3039_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(
    mut v_t_3043_: *mut leanh::LeanObject,
    mut v_bwd_3044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3045_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3043_, v_bwd_3044_);
    return v___x_3045_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(
    mut v_t_3046_: *mut leanh::LeanObject,
    mut v_bwd_3047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3048_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(v_t_3046_, v_bwd_3047_);
    leanh::lean_dec(v_t_3046_);
    return v_res_3048_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(
    mut v_motive_3049_: *mut leanh::LeanObject,
    mut v_t_3050_: *mut leanh::LeanObject,
    mut v_h_3051_: *mut leanh::LeanObject,
    mut v_bwd_3052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3053_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3050_, v_bwd_3052_);
    return v___x_3053_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(
    mut v_motive_3054_: *mut leanh::LeanObject,
    mut v_t_3055_: *mut leanh::LeanObject,
    mut v_h_3056_: *mut leanh::LeanObject,
    mut v_bwd_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(
        v_motive_3054_,
        v_t_3055_,
        v_h_3056_,
        v_bwd_3057_,
    );
    leanh::lean_dec(v_t_3055_);
    return v_res_3058_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(
    mut v_t_3059_: *mut leanh::LeanObject,
    mut v_leftRight_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3061_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3059_, v_leftRight_3060_);
    return v___x_3061_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(
    mut v_t_3062_: *mut leanh::LeanObject,
    mut v_leftRight_3063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3064_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(v_t_3062_, v_leftRight_3063_);
    leanh::lean_dec(v_t_3062_);
    return v_res_3064_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(
    mut v_motive_3065_: *mut leanh::LeanObject,
    mut v_t_3066_: *mut leanh::LeanObject,
    mut v_h_3067_: *mut leanh::LeanObject,
    mut v_leftRight_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3069_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3066_, v_leftRight_3068_);
    return v___x_3069_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(
    mut v_motive_3070_: *mut leanh::LeanObject,
    mut v_t_3071_: *mut leanh::LeanObject,
    mut v_h_3072_: *mut leanh::LeanObject,
    mut v_leftRight_3073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(
        v_motive_3070_,
        v_t_3071_,
        v_h_3072_,
        v_leftRight_3073_,
    );
    leanh::lean_dec(v_t_3071_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(
    mut v_t_3075_: *mut leanh::LeanObject,
    mut v_rightLeft_3076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3077_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3075_, v_rightLeft_3076_);
    return v___x_3077_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(
    mut v_t_3078_: *mut leanh::LeanObject,
    mut v_rightLeft_3079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3080_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(v_t_3078_, v_rightLeft_3079_);
    leanh::lean_dec(v_t_3078_);
    return v_res_3080_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(
    mut v_motive_3081_: *mut leanh::LeanObject,
    mut v_t_3082_: *mut leanh::LeanObject,
    mut v_h_3083_: *mut leanh::LeanObject,
    mut v_rightLeft_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3085_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3082_, v_rightLeft_3084_);
    return v___x_3085_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(
    mut v_motive_3086_: *mut leanh::LeanObject,
    mut v_t_3087_: *mut leanh::LeanObject,
    mut v_h_3088_: *mut leanh::LeanObject,
    mut v_rightLeft_3089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3090_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(
        v_motive_3086_,
        v_t_3087_,
        v_h_3088_,
        v_rightLeft_3089_,
    );
    leanh::lean_dec(v_t_3087_);
    return v_res_3090_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(
    mut v_t_3091_: *mut leanh::LeanObject,
    mut v_default_3092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3091_, v_default_3092_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(
    mut v_t_3094_: *mut leanh::LeanObject,
    mut v_default_3095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3096_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(v_t_3094_, v_default_3095_);
    leanh::lean_dec(v_t_3094_);
    return v_res_3096_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(
    mut v_motive_3097_: *mut leanh::LeanObject,
    mut v_t_3098_: *mut leanh::LeanObject,
    mut v_h_3099_: *mut leanh::LeanObject,
    mut v_default_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3098_, v_default_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(
    mut v_motive_3102_: *mut leanh::LeanObject,
    mut v_t_3103_: *mut leanh::LeanObject,
    mut v_h_3104_: *mut leanh::LeanObject,
    mut v_default_3105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3106_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(
        v_motive_3102_,
        v_t_3103_,
        v_h_3104_,
        v_default_3105_,
    );
    leanh::lean_dec(v_t_3103_);
    return v_res_3106_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(
    mut v_t_3107_: *mut leanh::LeanObject,
    mut v_user_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3109_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3107_, v_user_3108_);
    return v___x_3109_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(
    mut v_t_3110_: *mut leanh::LeanObject,
    mut v_user_3111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3112_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(v_t_3110_, v_user_3111_);
    leanh::lean_dec(v_t_3110_);
    return v_res_3112_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(
    mut v_motive_3113_: *mut leanh::LeanObject,
    mut v_t_3114_: *mut leanh::LeanObject,
    mut v_h_3115_: *mut leanh::LeanObject,
    mut v_user_3116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3117_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3114_, v_user_3116_);
    return v___x_3117_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(
    mut v_motive_3118_: *mut leanh::LeanObject,
    mut v_t_3119_: *mut leanh::LeanObject,
    mut v_h_3120_: *mut leanh::LeanObject,
    mut v_user_3121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3122_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(
        v_motive_3118_,
        v_t_3119_,
        v_h_3120_,
        v_user_3121_,
    );
    leanh::lean_dec(v_t_3119_);
    return v_res_3122_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(
    mut v_x_3127_: *mut leanh::LeanObject,
    mut v_x_3128_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v_gen_3133_: u8 = 0;
    let mut v_gen_x27_3134_: u8 = 0;
    let mut v_gen_3135_: u8 = 0;
    let mut v_gen_3136_: u8 = 0;
    let mut v_gen_3137_: u8 = 0;
    let mut v_gen_3138_: u8 = 0;
    let mut v_gen_3139_: u8 = 0;
    let mut v_gen_3140_: u8 = 0;
    let mut v_gen_3141_: u8 = 0;
    let mut v_gen_3142_: u8 = 0;
    let mut v_gen_3143_: u8 = 0;
    let mut v_gen_3144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3129_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_3127_);
                v___x_3130_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_3128_);
                v___x_3131_ = lean_nat_dec_eq(v___x_3129_, v___x_3130_);
                leanh::lean_dec(v___x_3130_);
                leanh::lean_dec(v___x_3129_);
                if v___x_3131_ == 0 {
                    return v___x_3131_;
                } else {
                    match leanh::lean_obj_tag(v_x_3127_) {
                        0 => {
                            v_gen_3135_ = leanh::lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3136_ = leanh::lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3135_;
                            v_gen_x27_3134_ = v_gen_3136_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_gen_3137_ = leanh::lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3138_ = leanh::lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3137_;
                            v_gen_x27_3134_ = v_gen_3138_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_gen_3139_ = leanh::lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3140_ = leanh::lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3139_;
                            v_gen_x27_3134_ = v_gen_3140_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v_gen_3141_ = leanh::lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3142_ = leanh::lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3141_;
                            v_gen_x27_3134_ = v_gen_3142_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_gen_3143_ = leanh::lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3144_ = leanh::lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3143_;
                            v_gen_x27_3134_ = v_gen_3144_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            return v___x_3131_;
                        }
                    }
                }
            }
            1 => {
                if v_gen_3133_ == 0 {
                    if v_gen_x27_3134_ == 0 {
                        return v___x_3131_;
                    } else {
                        return v_gen_3133_;
                    }
                } else {
                    return v_gen_x27_3134_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed(
    mut v_x_3145_: *mut leanh::LeanObject,
    mut v_x_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3147_: u8 = 0;
    let mut v_r_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_3145_, v_x_3146_);
    leanh::lean_dec(v_x_3146_);
    leanh::lean_dec(v_x_3145_);
    v_r_3148_ = leanh::lean_box((v_res_3147_) as usize);
    return v_r_3148_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3172_ = leanh::lean_unsigned_to_nat(2);
    v___x_3173_ = lean_nat_to_int(v___x_3172_);
    return v___x_3173_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3174_ = leanh::lean_unsigned_to_nat(1);
    v___x_3175_ = lean_nat_to_int(v___x_3174_);
    return v___x_3175_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(
    mut v_x_3200_: *mut leanh::LeanObject,
    mut v_prec_3201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_3237_: u8 = 0;
    let mut v___y_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_3251_: u8 = 0;
    let mut v___y_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_3265_: u8 = 0;
    let mut v___y_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: u8 = 0;
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_3287_: u8 = 0;
    let mut v___y_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: u8 = 0;
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_3309_: u8 = 0;
    let mut v___y_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_x_3200_) {
                    0 => {
                        v_gen_3237_ = leanh::lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3247_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3248_ = lean_nat_dec_le(v___x_3247_, v_prec_3201_);
                        if v___x_3248_ == 0 {
                            v___x_3249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3239_ = v___x_3249_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3250_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3239_ = v___x_3250_;
                            state = 6;
                            continue;
                        }
                    }
                    1 => {
                        v_gen_3251_ = leanh::lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3261_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3262_ = lean_nat_dec_le(v___x_3261_, v_prec_3201_);
                        if v___x_3262_ == 0 {
                            v___x_3263_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3253_ = v___x_3263_;
                            state = 7;
                            continue;
                        } else {
                            v___x_3264_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3253_ = v___x_3264_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        v_gen_3265_ = leanh::lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3275_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3276_ = lean_nat_dec_le(v___x_3275_, v_prec_3201_);
                        if v___x_3276_ == 0 {
                            v___x_3277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3267_ = v___x_3277_;
                            state = 8;
                            continue;
                        } else {
                            v___x_3278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3267_ = v___x_3278_;
                            state = 8;
                            continue;
                        }
                    }
                    3 => {
                        v___x_3279_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3280_ = lean_nat_dec_le(v___x_3279_, v_prec_3201_);
                        if v___x_3280_ == 0 {
                            v___x_3281_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3217_ = v___x_3281_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3282_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3217_ = v___x_3282_;
                            state = 3;
                            continue;
                        }
                    }
                    4 => {
                        v___x_3283_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3284_ = lean_nat_dec_le(v___x_3283_, v_prec_3201_);
                        if v___x_3284_ == 0 {
                            v___x_3285_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3224_ = v___x_3285_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3286_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3224_ = v___x_3286_;
                            state = 4;
                            continue;
                        }
                    }
                    5 => {
                        v_gen_3287_ = leanh::lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3297_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3298_ = lean_nat_dec_le(v___x_3297_, v_prec_3201_);
                        if v___x_3298_ == 0 {
                            v___x_3299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3289_ = v___x_3299_;
                            state = 9;
                            continue;
                        } else {
                            v___x_3300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3289_ = v___x_3300_;
                            state = 9;
                            continue;
                        }
                    }
                    6 => {
                        v___x_3301_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3302_ = lean_nat_dec_le(v___x_3301_, v_prec_3201_);
                        if v___x_3302_ == 0 {
                            v___x_3303_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3210_ = v___x_3303_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3304_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3210_ = v___x_3304_;
                            state = 2;
                            continue;
                        }
                    }
                    7 => {
                        v___x_3305_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3306_ = lean_nat_dec_le(v___x_3305_, v_prec_3201_);
                        if v___x_3306_ == 0 {
                            v___x_3307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3203_ = v___x_3307_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3308_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3203_ = v___x_3308_;
                            state = 1;
                            continue;
                        }
                    }
                    8 => {
                        v_gen_3309_ = leanh::lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3319_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3320_ = lean_nat_dec_le(v___x_3319_, v_prec_3201_);
                        if v___x_3320_ == 0 {
                            v___x_3321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3311_ = v___x_3321_;
                            state = 10;
                            continue;
                        } else {
                            v___x_3322_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3311_ = v___x_3322_;
                            state = 10;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3323_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_3324_ = lean_nat_dec_le(v___x_3323_, v_prec_3201_);
                        if v___x_3324_ == 0 {
                            v___x_3325_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3231_ = v___x_3325_;
                            state = 5;
                            continue;
                        } else {
                            v___x_3326_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3231_ = v___x_3326_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3204_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1;
                leanh::lean_inc(v___y_3203_);
                v___x_3205_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3205_, 0, v___y_3203_);
                leanh::lean_ctor_set(v___x_3205_, 1, v___x_3204_);
                v___x_3206_ = 0;
                v___x_3207_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3207_, 0, v___x_3205_);
                leanh::lean_ctor_set_uint8(
                    v___x_3207_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3206_,
                );
                v___x_3208_ = l_Repr_addAppParen(v___x_3207_, v_prec_3201_);
                return v___x_3208_;
            }
            2 => {
                v___x_3211_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3;
                leanh::lean_inc(v___y_3210_);
                v___x_3212_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3212_, 0, v___y_3210_);
                leanh::lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                v___x_3213_ = 0;
                v___x_3214_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3214_, 0, v___x_3212_);
                leanh::lean_ctor_set_uint8(
                    v___x_3214_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3213_,
                );
                v___x_3215_ = l_Repr_addAppParen(v___x_3214_, v_prec_3201_);
                return v___x_3215_;
            }
            3 => {
                v___x_3218_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5;
                leanh::lean_inc(v___y_3217_);
                v___x_3219_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3219_, 0, v___y_3217_);
                leanh::lean_ctor_set(v___x_3219_, 1, v___x_3218_);
                v___x_3220_ = 0;
                v___x_3221_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3221_, 0, v___x_3219_);
                leanh::lean_ctor_set_uint8(
                    v___x_3221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3220_,
                );
                v___x_3222_ = l_Repr_addAppParen(v___x_3221_, v_prec_3201_);
                return v___x_3222_;
            }
            4 => {
                v___x_3225_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7;
                leanh::lean_inc(v___y_3224_);
                v___x_3226_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3226_, 0, v___y_3224_);
                leanh::lean_ctor_set(v___x_3226_, 1, v___x_3225_);
                v___x_3227_ = 0;
                v___x_3228_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3228_, 0, v___x_3226_);
                leanh::lean_ctor_set_uint8(
                    v___x_3228_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3227_,
                );
                v___x_3229_ = l_Repr_addAppParen(v___x_3228_, v_prec_3201_);
                return v___x_3229_;
            }
            5 => {
                v___x_3232_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9;
                leanh::lean_inc(v___y_3231_);
                v___x_3233_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3233_, 0, v___y_3231_);
                leanh::lean_ctor_set(v___x_3233_, 1, v___x_3232_);
                v___x_3234_ = 0;
                v___x_3235_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3235_, 0, v___x_3233_);
                leanh::lean_ctor_set_uint8(
                    v___x_3235_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3234_,
                );
                v___x_3236_ = l_Repr_addAppParen(v___x_3235_, v_prec_3201_);
                return v___x_3236_;
            }
            6 => {
                v___x_3240_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12;
                v___x_3241_ = l_Bool_repr___redArg(v_gen_3237_);
                v___x_3242_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3242_, 0, v___x_3240_);
                leanh::lean_ctor_set(v___x_3242_, 1, v___x_3241_);
                leanh::lean_inc(v___y_3239_);
                v___x_3243_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3243_, 0, v___y_3239_);
                leanh::lean_ctor_set(v___x_3243_, 1, v___x_3242_);
                v___x_3244_ = 0;
                v___x_3245_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3245_, 0, v___x_3243_);
                leanh::lean_ctor_set_uint8(
                    v___x_3245_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3244_,
                );
                v___x_3246_ = l_Repr_addAppParen(v___x_3245_, v_prec_3201_);
                return v___x_3246_;
            }
            7 => {
                v___x_3254_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17;
                v___x_3255_ = l_Bool_repr___redArg(v_gen_3251_);
                v___x_3256_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3256_, 0, v___x_3254_);
                leanh::lean_ctor_set(v___x_3256_, 1, v___x_3255_);
                leanh::lean_inc(v___y_3253_);
                v___x_3257_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3257_, 0, v___y_3253_);
                leanh::lean_ctor_set(v___x_3257_, 1, v___x_3256_);
                v___x_3258_ = 0;
                v___x_3259_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3259_, 0, v___x_3257_);
                leanh::lean_ctor_set_uint8(
                    v___x_3259_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3258_,
                );
                v___x_3260_ = l_Repr_addAppParen(v___x_3259_, v_prec_3201_);
                return v___x_3260_;
            }
            8 => {
                v___x_3268_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20;
                v___x_3269_ = l_Bool_repr___redArg(v_gen_3265_);
                v___x_3270_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3270_, 0, v___x_3268_);
                leanh::lean_ctor_set(v___x_3270_, 1, v___x_3269_);
                leanh::lean_inc(v___y_3267_);
                v___x_3271_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3271_, 0, v___y_3267_);
                leanh::lean_ctor_set(v___x_3271_, 1, v___x_3270_);
                v___x_3272_ = 0;
                v___x_3273_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3273_, 0, v___x_3271_);
                leanh::lean_ctor_set_uint8(
                    v___x_3273_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3272_,
                );
                v___x_3274_ = l_Repr_addAppParen(v___x_3273_, v_prec_3201_);
                return v___x_3274_;
            }
            9 => {
                v___x_3290_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23;
                v___x_3291_ = l_Bool_repr___redArg(v_gen_3287_);
                v___x_3292_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3292_, 0, v___x_3290_);
                leanh::lean_ctor_set(v___x_3292_, 1, v___x_3291_);
                leanh::lean_inc(v___y_3289_);
                v___x_3293_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3293_, 0, v___y_3289_);
                leanh::lean_ctor_set(v___x_3293_, 1, v___x_3292_);
                v___x_3294_ = 0;
                v___x_3295_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3295_, 0, v___x_3293_);
                leanh::lean_ctor_set_uint8(
                    v___x_3295_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3294_,
                );
                v___x_3296_ = l_Repr_addAppParen(v___x_3295_, v_prec_3201_);
                return v___x_3296_;
            }
            10 => {
                v___x_3312_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26;
                v___x_3313_ = l_Bool_repr___redArg(v_gen_3309_);
                v___x_3314_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3314_, 0, v___x_3312_);
                leanh::lean_ctor_set(v___x_3314_, 1, v___x_3313_);
                leanh::lean_inc(v___y_3311_);
                v___x_3315_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3315_, 0, v___y_3311_);
                leanh::lean_ctor_set(v___x_3315_, 1, v___x_3314_);
                v___x_3316_ = 0;
                v___x_3317_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3317_, 0, v___x_3315_);
                leanh::lean_ctor_set_uint8(
                    v___x_3317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3316_,
                );
                v___x_3318_ = l_Repr_addAppParen(v___x_3317_, v_prec_3201_);
                return v___x_3318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed(
    mut v_x_3327_: *mut leanh::LeanObject,
    mut v_prec_3328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(v_x_3327_, v_prec_3328_);
    leanh::lean_dec(v_prec_3328_);
    leanh::lean_dec(v_x_3327_);
    return v_res_3329_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0() -> u64 {
    let mut v___x_3332_: u64 = 0;
    let mut v___x_3333_: u64 = 0;
    let mut v___x_3334_: u64 = 0;
    v___x_3332_ = 13u64;
    v___x_3333_ = 0u64;
    v___x_3334_ = lean_uint64_mix_hash(v___x_3333_, v___x_3332_);
    return v___x_3334_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1() -> u64 {
    let mut v___x_3335_: u64 = 0;
    let mut v___x_3336_: u64 = 0;
    let mut v___x_3337_: u64 = 0;
    v___x_3335_ = 11u64;
    v___x_3336_ = 0u64;
    v___x_3337_ = lean_uint64_mix_hash(v___x_3336_, v___x_3335_);
    return v___x_3337_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2() -> u64 {
    let mut v___x_3338_: u64 = 0;
    let mut v___x_3339_: u64 = 0;
    let mut v___x_3340_: u64 = 0;
    v___x_3338_ = 13u64;
    v___x_3339_ = 1u64;
    v___x_3340_ = lean_uint64_mix_hash(v___x_3339_, v___x_3338_);
    return v___x_3340_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3() -> u64 {
    let mut v___x_3341_: u64 = 0;
    let mut v___x_3342_: u64 = 0;
    let mut v___x_3343_: u64 = 0;
    v___x_3341_ = 11u64;
    v___x_3342_ = 1u64;
    v___x_3343_ = lean_uint64_mix_hash(v___x_3342_, v___x_3341_);
    return v___x_3343_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4() -> u64 {
    let mut v___x_3344_: u64 = 0;
    let mut v___x_3345_: u64 = 0;
    let mut v___x_3346_: u64 = 0;
    v___x_3344_ = 13u64;
    v___x_3345_ = 2u64;
    v___x_3346_ = lean_uint64_mix_hash(v___x_3345_, v___x_3344_);
    return v___x_3346_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5() -> u64 {
    let mut v___x_3347_: u64 = 0;
    let mut v___x_3348_: u64 = 0;
    let mut v___x_3349_: u64 = 0;
    v___x_3347_ = 11u64;
    v___x_3348_ = 2u64;
    v___x_3349_ = lean_uint64_mix_hash(v___x_3348_, v___x_3347_);
    return v___x_3349_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6() -> u64 {
    let mut v___x_3350_: u64 = 0;
    let mut v___x_3351_: u64 = 0;
    let mut v___x_3352_: u64 = 0;
    v___x_3350_ = 13u64;
    v___x_3351_ = 5u64;
    v___x_3352_ = lean_uint64_mix_hash(v___x_3351_, v___x_3350_);
    return v___x_3352_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7() -> u64 {
    let mut v___x_3353_: u64 = 0;
    let mut v___x_3354_: u64 = 0;
    let mut v___x_3355_: u64 = 0;
    v___x_3353_ = 11u64;
    v___x_3354_ = 5u64;
    v___x_3355_ = lean_uint64_mix_hash(v___x_3354_, v___x_3353_);
    return v___x_3355_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8() -> u64 {
    let mut v___x_3356_: u64 = 0;
    let mut v___x_3357_: u64 = 0;
    let mut v___x_3358_: u64 = 0;
    v___x_3356_ = 13u64;
    v___x_3357_ = 8u64;
    v___x_3358_ = lean_uint64_mix_hash(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9() -> u64 {
    let mut v___x_3359_: u64 = 0;
    let mut v___x_3360_: u64 = 0;
    let mut v___x_3361_: u64 = 0;
    v___x_3359_ = 11u64;
    v___x_3360_ = 8u64;
    v___x_3361_ = lean_uint64_mix_hash(v___x_3360_, v___x_3359_);
    return v___x_3361_;
}
pub unsafe fn l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(
    mut v_x_3362_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_x_3362_) {
        0 => {
            let mut v_gen_3363_: u8 = 0;
            v_gen_3363_ = leanh::lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3363_ == 0 {
                let mut v___x_3364_: u64 = 0;
                v___x_3364_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0,
                );
                return v___x_3364_;
            } else {
                let mut v___x_3365_: u64 = 0;
                v___x_3365_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1,
                );
                return v___x_3365_;
            }
        }
        1 => {
            let mut v_gen_3366_: u8 = 0;
            v_gen_3366_ = leanh::lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3366_ == 0 {
                let mut v___x_3367_: u64 = 0;
                v___x_3367_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2,
                );
                return v___x_3367_;
            } else {
                let mut v___x_3368_: u64 = 0;
                v___x_3368_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3,
                );
                return v___x_3368_;
            }
        }
        2 => {
            let mut v_gen_3369_: u8 = 0;
            v_gen_3369_ = leanh::lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3369_ == 0 {
                let mut v___x_3370_: u64 = 0;
                v___x_3370_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4,
                );
                return v___x_3370_;
            } else {
                let mut v___x_3371_: u64 = 0;
                v___x_3371_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5,
                );
                return v___x_3371_;
            }
        }
        3 => {
            let mut v___x_3372_: u64 = 0;
            v___x_3372_ = 3u64;
            return v___x_3372_;
        }
        4 => {
            let mut v___x_3373_: u64 = 0;
            v___x_3373_ = 4u64;
            return v___x_3373_;
        }
        5 => {
            let mut v_gen_3374_: u8 = 0;
            v_gen_3374_ = leanh::lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3374_ == 0 {
                let mut v___x_3375_: u64 = 0;
                v___x_3375_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6,
                );
                return v___x_3375_;
            } else {
                let mut v___x_3376_: u64 = 0;
                v___x_3376_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7,
                );
                return v___x_3376_;
            }
        }
        6 => {
            let mut v___x_3377_: u64 = 0;
            v___x_3377_ = 6u64;
            return v___x_3377_;
        }
        7 => {
            let mut v___x_3378_: u64 = 0;
            v___x_3378_ = 7u64;
            return v___x_3378_;
        }
        8 => {
            let mut v_gen_3379_: u8 = 0;
            v_gen_3379_ = leanh::lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3379_ == 0 {
                let mut v___x_3380_: u64 = 0;
                v___x_3380_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8,
                );
                return v___x_3380_;
            } else {
                let mut v___x_3381_: u64 = 0;
                v___x_3381_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once
                    ),
                    _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9,
                );
                return v___x_3381_;
            }
        }
        _ => {
            let mut v___x_3382_: u64 = 0;
            v___x_3382_ = 9u64;
            return v___x_3382_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(
    mut v_x_3383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3384_: u64 = 0;
    let mut v_r_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3384_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_3383_);
    leanh::lean_dec(v_x_3383_);
    v_r_3385_ = leanh::lean_box_uint64(v_res_3384_);
    return v_r_3385_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = leanh::lean_box(0);
    v___x_3394_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2;
    v___x_3395_ = l_Lean_Expr_const___override(v___x_3394_, v___x_3393_);
    return v___x_3395_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3396_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3,
    );
    v___x_3397_ = leanh::lean_unsigned_to_nat(0);
    v___x_3398_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0;
    v___x_3399_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3399_, 0, v___x_3398_);
    leanh::lean_ctor_set(v___x_3399_, 1, v___x_3397_);
    leanh::lean_ctor_set(v___x_3399_, 2, v___x_3396_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default()
-> *mut leanh::LeanObject {
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4,
    );
    return v___x_3400_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS() -> *mut leanh::LeanObject {
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
    return v___x_3401_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(
    mut v_xs_3402_: *mut leanh::LeanObject,
    mut v_ys_3403_: *mut leanh::LeanObject,
    mut v_x_3404_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3406_: u8 = 0;
    let mut v_one_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3405_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3406_ = lean_nat_dec_eq(v_x_3404_, v_zero_3405_);
                if v_isZero_3406_ == 1 {
                    leanh::lean_dec(v_x_3404_);
                    return v_isZero_3406_;
                } else {
                    v_one_3407_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3408_ = lean_nat_sub(v_x_3404_, v_one_3407_);
                    leanh::lean_dec(v_x_3404_);
                    v___x_3409_ = lean_array_fget_borrowed(v_xs_3402_, v_n_3408_);
                    v___x_3410_ = lean_array_fget_borrowed(v_ys_3403_, v_n_3408_);
                    v___x_3411_ = lean_name_eq(v___x_3409_, v___x_3410_);
                    if v___x_3411_ == 0 {
                        leanh::lean_dec(v_n_3408_);
                        return v___x_3411_;
                    } else {
                        v_x_3404_ = v_n_3408_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(
    mut v_xs_3413_: *mut leanh::LeanObject,
    mut v_ys_3414_: *mut leanh::LeanObject,
    mut v_x_3415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3416_: u8 = 0;
    let mut v_r_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(
        v_xs_3413_, v_ys_3414_, v_x_3415_,
    );
    leanh::lean_dec_ref(v_ys_3414_);
    leanh::lean_dec_ref(v_xs_3413_);
    v_r_3417_ = leanh::lean_box((v_res_3416_) as usize);
    return v_r_3417_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqCnstrRHS_beq(
    mut v_x_3418_: *mut leanh::LeanObject,
    mut v_x_3419_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_levelNames_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMVars_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMVars_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    v_levelNames_3420_ = leanh::lean_ctor_get(v_x_3418_, 0);
    v_numMVars_3421_ = leanh::lean_ctor_get(v_x_3418_, 1);
    v_expr_3422_ = leanh::lean_ctor_get(v_x_3418_, 2);
    v_levelNames_3423_ = leanh::lean_ctor_get(v_x_3419_, 0);
    v_numMVars_3424_ = leanh::lean_ctor_get(v_x_3419_, 1);
    v_expr_3425_ = leanh::lean_ctor_get(v_x_3419_, 2);
    v___x_3426_ = lean_array_get_size(v_levelNames_3420_);
    v___x_3427_ = lean_array_get_size(v_levelNames_3423_);
    v___x_3428_ = lean_nat_dec_eq(v___x_3426_, v___x_3427_);
    if v___x_3428_ == 0 {
        return v___x_3428_;
    } else {
        let mut v___x_3429_: u8 = 0;
        v___x_3429_ =
            l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(
                v_levelNames_3420_,
                v_levelNames_3423_,
                v___x_3426_,
            );
        if v___x_3429_ == 0 {
            return v___x_3429_;
        } else {
            let mut v___x_3430_: u8 = 0;
            v___x_3430_ = lean_nat_dec_eq(v_numMVars_3421_, v_numMVars_3424_);
            if v___x_3430_ == 0 {
                return v___x_3430_;
            } else {
                let mut v___x_3431_: u8 = 0;
                v___x_3431_ = lean_expr_eqv(v_expr_3422_, v_expr_3425_);
                return v___x_3431_;
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed(
    mut v_x_3432_: *mut leanh::LeanObject,
    mut v_x_3433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3434_: u8 = 0;
    let mut v_r_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3434_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_3432_, v_x_3433_);
    leanh::lean_dec_ref(v_x_3433_);
    leanh::lean_dec_ref(v_x_3432_);
    v_r_3435_ = leanh::lean_box((v_res_3434_) as usize);
    return v_r_3435_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(
    mut v_xs_3436_: *mut leanh::LeanObject,
    mut v_ys_3437_: *mut leanh::LeanObject,
    mut v_hsz_3438_: *mut leanh::LeanObject,
    mut v_x_3439_: *mut leanh::LeanObject,
    mut v_x_3440_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3441_: u8 = 0;
    v___x_3441_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(
        v_xs_3436_, v_ys_3437_, v_x_3439_,
    );
    return v___x_3441_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(
    mut v_xs_3442_: *mut leanh::LeanObject,
    mut v_ys_3443_: *mut leanh::LeanObject,
    mut v_hsz_3444_: *mut leanh::LeanObject,
    mut v_x_3445_: *mut leanh::LeanObject,
    mut v_x_3446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3447_: u8 = 0;
    let mut v_r_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3447_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(
        v_xs_3442_,
        v_ys_3443_,
        v_hsz_3444_,
        v_x_3445_,
        v_x_3446_,
    );
    leanh::lean_dec_ref(v_ys_3443_);
    leanh::lean_dec_ref(v_xs_3442_);
    v_r_3448_ = leanh::lean_box((v_res_3447_) as usize);
    return v_r_3448_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(
    mut v_a_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3452_ = lean_nat_to_int(v_a_3451_);
    return v___x_3452_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_3453_: *mut leanh::LeanObject,
    mut v_x_3454_: *mut leanh::LeanObject,
    mut v_x_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3455_) == 0 {
                    leanh::lean_dec(v_x_3453_);
                    return v_x_3454_;
                } else {
                    v_head_3456_ = leanh::lean_ctor_get(v_x_3455_, 0);
                    v_tail_3457_ = leanh::lean_ctor_get(v_x_3455_, 1);
                    v_isSharedCheck_3468_ = (!leanh::lean_is_exclusive(v_x_3455_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3459_ = v_x_3455_;
                        v_isShared_3460_ = v_isSharedCheck_3468_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3457_);
                        leanh::lean_inc(v_head_3456_);
                        leanh::lean_dec(v_x_3455_);
                        v___x_3459_ = leanh::lean_box(0);
                        v_isShared_3460_ = v_isSharedCheck_3468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_3453_);
                if v_isShared_3460_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3459_, 5);
                    leanh::lean_ctor_set(v___x_3459_, 1, v_x_3453_);
                    leanh::lean_ctor_set(v___x_3459_, 0, v_x_3454_);
                    v___x_3462_ = v___x_3459_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_x_3454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_x_3453_);
                    v___x_3462_ = v_reuseFailAlloc_3467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3463_ = leanh::lean_unsigned_to_nat(0);
                v___x_3464_ = l_Lean_Name_reprPrec(v_head_3456_, v___x_3463_);
                v___x_3465_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3465_, 0, v___x_3462_);
                leanh::lean_ctor_set(v___x_3465_, 1, v___x_3464_);
                v_x_3454_ = v___x_3465_;
                v_x_3455_ = v_tail_3457_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(
    mut v_x_3469_: *mut leanh::LeanObject,
    mut v_x_3470_: *mut leanh::LeanObject,
    mut v_x_3471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3471_) == 0 {
                    leanh::lean_dec(v_x_3469_);
                    return v_x_3470_;
                } else {
                    v_head_3472_ = leanh::lean_ctor_get(v_x_3471_, 0);
                    v_tail_3473_ = leanh::lean_ctor_get(v_x_3471_, 1);
                    v_isSharedCheck_3484_ = (!leanh::lean_is_exclusive(v_x_3471_)) as u8;
                    if v_isSharedCheck_3484_ == 0 {
                        v___x_3475_ = v_x_3471_;
                        v_isShared_3476_ = v_isSharedCheck_3484_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3473_);
                        leanh::lean_inc(v_head_3472_);
                        leanh::lean_dec(v_x_3471_);
                        v___x_3475_ = leanh::lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_3469_);
                if v_isShared_3476_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3475_, 5);
                    leanh::lean_ctor_set(v___x_3475_, 1, v_x_3469_);
                    leanh::lean_ctor_set(v___x_3475_, 0, v_x_3470_);
                    v___x_3478_ = v___x_3475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3483_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_x_3470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_x_3469_);
                    v___x_3478_ = v_reuseFailAlloc_3483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3479_ = leanh::lean_unsigned_to_nat(0);
                v___x_3480_ = l_Lean_Name_reprPrec(v_head_3472_, v___x_3479_);
                v___x_3481_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3481_, 0, v___x_3478_);
                leanh::lean_ctor_set(v___x_3481_, 1, v___x_3480_);
                v___x_3482_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_3469_, v___x_3481_, v_tail_3473_);
                return v___x_3482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(
    mut v___y_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = leanh::lean_unsigned_to_nat(0);
    v___x_3487_ = l_Lean_Name_reprPrec(v___y_3485_, v___x_3486_);
    return v___x_3487_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(
    mut v_x_3488_: *mut leanh::LeanObject,
    mut v_x_3489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3488_) == 0 {
        let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3489_);
        v___x_3490_ = leanh::lean_box(0);
        return v___x_3490_;
    } else {
        let mut v_tail_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_3491_ = leanh::lean_ctor_get(v_x_3488_, 1);
        if leanh::lean_obj_tag(v_tail_3491_) == 0 {
            let mut v_head_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_3489_);
            v_head_3492_ = leanh::lean_ctor_get(v_x_3488_, 0);
            leanh::lean_inc(v_head_3492_);
            leanh::lean_dec_ref_known(v_x_3488_, 2);
            v___x_3493_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_3492_);
            return v___x_3493_;
        } else {
            let mut v_head_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_3491_);
            v_head_3494_ = leanh::lean_ctor_get(v_x_3488_, 0);
            leanh::lean_inc(v_head_3494_);
            leanh::lean_dec_ref_known(v_x_3488_, 2);
            v___x_3495_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_3494_);
            v___x_3496_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_3489_, v___x_3495_, v_tail_3491_);
            return v___x_3496_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0;
    v___x_3506_ = lean_string_length(v___x_3505_);
    return v___x_3506_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3507_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once
        ),
        _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5,
    );
    v___x_3508_ = lean_nat_to_int(v___x_3507_);
    return v___x_3508_;
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(
    mut v_xs_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    v___x_3517_ = lean_array_get_size(v_xs_3516_);
    v___x_3518_ = leanh::lean_unsigned_to_nat(0);
    v___x_3519_ = lean_nat_dec_eq(v___x_3517_, v___x_3518_);
    if v___x_3519_ == 0 {
        let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3520_ = lean_array_to_list(v_xs_3516_);
        v___x_3521_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3;
        v___x_3522_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_3520_, v___x_3521_);
        v___x_3523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
        v___x_3524_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7;
        v___x_3525_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3525_, 0, v___x_3524_);
        leanh::lean_ctor_set(v___x_3525_, 1, v___x_3522_);
        v___x_3526_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8;
        v___x_3527_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3527_, 0, v___x_3525_);
        leanh::lean_ctor_set(v___x_3527_, 1, v___x_3526_);
        v___x_3528_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3528_, 0, v___x_3523_);
        leanh::lean_ctor_set(v___x_3528_, 1, v___x_3527_);
        v___x_3529_ = l_Std_Format_fill(v___x_3528_);
        return v___x_3529_;
    } else {
        let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_3516_);
        v___x_3530_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10;
        return v___x_3530_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3544_ = leanh::lean_unsigned_to_nat(14);
    v___x_3545_ = lean_nat_to_int(v___x_3544_);
    return v___x_3545_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3549_ = leanh::lean_unsigned_to_nat(12);
    v___x_3550_ = lean_nat_to_int(v___x_3549_);
    return v___x_3550_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3554_ = leanh::lean_unsigned_to_nat(8);
    v___x_3555_ = lean_nat_to_int(v___x_3554_);
    return v___x_3555_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3557_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0;
    v___x_3558_ = lean_string_length(v___x_3557_);
    return v___x_3558_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15,
    );
    v___x_3560_ = lean_nat_to_int(v___x_3559_);
    return v___x_3560_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(
    mut v_x_3565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levelNames_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMVars_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_levelNames_3566_ = leanh::lean_ctor_get(v_x_3565_, 0);
    leanh::lean_inc_ref(v_levelNames_3566_);
    v_numMVars_3567_ = leanh::lean_ctor_get(v_x_3565_, 1);
    leanh::lean_inc(v_numMVars_3567_);
    v_expr_3568_ = leanh::lean_ctor_get(v_x_3565_, 2);
    leanh::lean_inc_ref(v_expr_3568_);
    leanh::lean_dec_ref(v_x_3565_);
    v___x_3569_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5;
    v___x_3570_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6;
    v___x_3571_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7,
    );
    v___x_3572_ =
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_3566_);
    v___x_3573_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3573_, 0, v___x_3571_);
    leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
    v___x_3574_ = 0;
    v___x_3575_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3575_, 0, v___x_3573_);
    leanh::lean_ctor_set_uint8(
        v___x_3575_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    v___x_3576_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3576_, 0, v___x_3570_);
    leanh::lean_ctor_set(v___x_3576_, 1, v___x_3575_);
    v___x_3577_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2;
    v___x_3578_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3578_, 0, v___x_3576_);
    leanh::lean_ctor_set(v___x_3578_, 1, v___x_3577_);
    v___x_3579_ = leanh::lean_box(1);
    v___x_3580_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3580_, 0, v___x_3578_);
    leanh::lean_ctor_set(v___x_3580_, 1, v___x_3579_);
    v___x_3581_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9;
    v___x_3582_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3582_, 0, v___x_3580_);
    leanh::lean_ctor_set(v___x_3582_, 1, v___x_3581_);
    v___x_3583_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3583_, 0, v___x_3582_);
    leanh::lean_ctor_set(v___x_3583_, 1, v___x_3569_);
    v___x_3584_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10,
    );
    v___x_3585_ = l_Nat_reprFast(v_numMVars_3567_);
    v___x_3586_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3586_, 0, v___x_3585_);
    v___x_3587_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3587_, 0, v___x_3584_);
    leanh::lean_ctor_set(v___x_3587_, 1, v___x_3586_);
    v___x_3588_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3588_, 0, v___x_3587_);
    leanh::lean_ctor_set_uint8(
        v___x_3588_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    v___x_3589_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3589_, 0, v___x_3583_);
    leanh::lean_ctor_set(v___x_3589_, 1, v___x_3588_);
    v___x_3590_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3590_, 0, v___x_3589_);
    leanh::lean_ctor_set(v___x_3590_, 1, v___x_3577_);
    v___x_3591_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3591_, 0, v___x_3590_);
    leanh::lean_ctor_set(v___x_3591_, 1, v___x_3579_);
    v___x_3592_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12;
    v___x_3593_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3593_, 0, v___x_3591_);
    leanh::lean_ctor_set(v___x_3593_, 1, v___x_3592_);
    v___x_3594_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3594_, 0, v___x_3593_);
    leanh::lean_ctor_set(v___x_3594_, 1, v___x_3569_);
    v___x_3595_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13,
    );
    v___x_3596_ = leanh::lean_unsigned_to_nat(0);
    v___x_3597_ = l_Lean_instReprExpr_repr(v_expr_3568_, v___x_3596_);
    v___x_3598_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3598_, 0, v___x_3595_);
    leanh::lean_ctor_set(v___x_3598_, 1, v___x_3597_);
    v___x_3599_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3599_, 0, v___x_3598_);
    leanh::lean_ctor_set_uint8(
        v___x_3599_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    v___x_3600_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3600_, 0, v___x_3594_);
    leanh::lean_ctor_set(v___x_3600_, 1, v___x_3599_);
    v___x_3601_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16,
    );
    v___x_3602_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17;
    v___x_3603_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3603_, 0, v___x_3602_);
    leanh::lean_ctor_set(v___x_3603_, 1, v___x_3600_);
    v___x_3604_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18;
    v___x_3605_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3605_, 0, v___x_3603_);
    leanh::lean_ctor_set(v___x_3605_, 1, v___x_3604_);
    v___x_3606_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3606_, 0, v___x_3601_);
    leanh::lean_ctor_set(v___x_3606_, 1, v___x_3605_);
    v___x_3607_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3607_, 0, v___x_3606_);
    leanh::lean_ctor_set_uint8(
        v___x_3607_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    return v___x_3607_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprCnstrRHS_repr(
    mut v_x_3608_: *mut leanh::LeanObject,
    mut v_prec_3609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3610_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_3608_);
    return v___x_3610_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(
    mut v_x_3611_: *mut leanh::LeanObject,
    mut v_prec_3612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_3611_, v_prec_3612_);
    leanh::lean_dec(v_prec_3612_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(
    mut v_x_3616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3616_) {
        0 => {
            let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3617_ = leanh::lean_unsigned_to_nat(0);
            return v___x_3617_;
        }
        1 => {
            let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3618_ = leanh::lean_unsigned_to_nat(1);
            return v___x_3618_;
        }
        2 => {
            let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3619_ = leanh::lean_unsigned_to_nat(2);
            return v___x_3619_;
        }
        3 => {
            let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3620_ = leanh::lean_unsigned_to_nat(3);
            return v___x_3620_;
        }
        4 => {
            let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3621_ = leanh::lean_unsigned_to_nat(4);
            return v___x_3621_;
        }
        5 => {
            let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3622_ = leanh::lean_unsigned_to_nat(5);
            return v___x_3622_;
        }
        6 => {
            let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3623_ = leanh::lean_unsigned_to_nat(6);
            return v___x_3623_;
        }
        7 => {
            let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3624_ = leanh::lean_unsigned_to_nat(7);
            return v___x_3624_;
        }
        8 => {
            let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3625_ = leanh::lean_unsigned_to_nat(8);
            return v___x_3625_;
        }
        9 => {
            let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3626_ = leanh::lean_unsigned_to_nat(9);
            return v___x_3626_;
        }
        _ => {
            let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3627_ = leanh::lean_unsigned_to_nat(10);
            return v___x_3627_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(
    mut v_x_3628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3629_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_3628_);
    leanh::lean_dec_ref(v_x_3628_);
    return v_res_3629_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(
    mut v_t_3630_: *mut leanh::LeanObject,
    mut v_k_3631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_3630_) {
        0 => {
            let mut v_lhs_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_3632_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc(v_lhs_3632_);
            v_rhs_3633_ = leanh::lean_ctor_get(v_t_3630_, 1);
            leanh::lean_inc_ref(v_rhs_3633_);
            leanh::lean_dec_ref_known(v_t_3630_, 2);
            v___x_3634_ = leanh::lean_apply_2(v_k_3631_, v_lhs_3632_, v_rhs_3633_);
            return v___x_3634_;
        }
        1 => {
            let mut v_lhs_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_3635_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc(v_lhs_3635_);
            v_rhs_3636_ = leanh::lean_ctor_get(v_t_3630_, 1);
            leanh::lean_inc_ref(v_rhs_3636_);
            leanh::lean_dec_ref_known(v_t_3630_, 2);
            v___x_3637_ = leanh::lean_apply_2(v_k_3631_, v_lhs_3635_, v_rhs_3636_);
            return v___x_3637_;
        }
        2 => {
            let mut v_lhs_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_3638_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc(v_lhs_3638_);
            v_n_3639_ = leanh::lean_ctor_get(v_t_3630_, 1);
            leanh::lean_inc(v_n_3639_);
            leanh::lean_dec_ref_known(v_t_3630_, 2);
            v___x_3640_ = leanh::lean_apply_2(v_k_3631_, v_lhs_3638_, v_n_3639_);
            return v___x_3640_;
        }
        3 => {
            let mut v_lhs_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_3641_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc(v_lhs_3641_);
            v_n_3642_ = leanh::lean_ctor_get(v_t_3630_, 1);
            leanh::lean_inc(v_n_3642_);
            leanh::lean_dec_ref_known(v_t_3630_, 2);
            v___x_3643_ = leanh::lean_apply_2(v_k_3631_, v_lhs_3641_, v_n_3642_);
            return v___x_3643_;
        }
        6 => {
            let mut v_bvarIdx_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_strict_3645_: u8 = 0;
            let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_bvarIdx_3644_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc(v_bvarIdx_3644_);
            v_strict_3645_ = leanh::lean_ctor_get_uint8(
                v_t_3630_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            );
            leanh::lean_dec_ref_known(v_t_3630_, 1);
            v___x_3646_ = leanh::lean_box((v_strict_3645_) as usize);
            v___x_3647_ = leanh::lean_apply_2(v_k_3631_, v_bvarIdx_3644_, v___x_3646_);
            return v___x_3647_;
        }
        8 => {
            let mut v_e_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_3648_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc_ref(v_e_3648_);
            leanh::lean_dec_ref_known(v_t_3630_, 1);
            v___x_3649_ = leanh::lean_apply_1(v_k_3631_, v_e_3648_);
            return v___x_3649_;
        }
        9 => {
            let mut v_e_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_3650_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc_ref(v_e_3650_);
            leanh::lean_dec_ref_known(v_t_3630_, 1);
            v___x_3651_ = leanh::lean_apply_1(v_k_3631_, v_e_3650_);
            return v___x_3651_;
        }
        10 => {
            let mut v_bvarIdx_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_strict_3653_: u8 = 0;
            let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_bvarIdx_3652_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc(v_bvarIdx_3652_);
            v_strict_3653_ = leanh::lean_ctor_get_uint8(
                v_t_3630_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            );
            leanh::lean_dec_ref_known(v_t_3630_, 1);
            v___x_3654_ = leanh::lean_box((v_strict_3653_) as usize);
            v___x_3655_ = leanh::lean_apply_2(v_k_3631_, v_bvarIdx_3652_, v___x_3654_);
            return v___x_3655_;
        }
        _ => {
            let mut v_n_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_3656_ = leanh::lean_ctor_get(v_t_3630_, 0);
            leanh::lean_inc(v_n_3656_);
            leanh::lean_dec_ref(v_t_3630_);
            v___x_3657_ = leanh::lean_apply_1(v_k_3631_, v_n_3656_);
            return v___x_3657_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(
    mut v_motive_3658_: *mut leanh::LeanObject,
    mut v_ctorIdx_3659_: *mut leanh::LeanObject,
    mut v_t_3660_: *mut leanh::LeanObject,
    mut v_h_3661_: *mut leanh::LeanObject,
    mut v_k_3662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3660_, v_k_3662_);
    return v___x_3663_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(
    mut v_motive_3664_: *mut leanh::LeanObject,
    mut v_ctorIdx_3665_: *mut leanh::LeanObject,
    mut v_t_3666_: *mut leanh::LeanObject,
    mut v_h_3667_: *mut leanh::LeanObject,
    mut v_k_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3669_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(
        v_motive_3664_,
        v_ctorIdx_3665_,
        v_t_3666_,
        v_h_3667_,
        v_k_3668_,
    );
    leanh::lean_dec(v_ctorIdx_3665_);
    return v_res_3669_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(
    mut v_t_3670_: *mut leanh::LeanObject,
    mut v_notDefEq_3671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3670_, v_notDefEq_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(
    mut v_motive_3673_: *mut leanh::LeanObject,
    mut v_t_3674_: *mut leanh::LeanObject,
    mut v_h_3675_: *mut leanh::LeanObject,
    mut v_notDefEq_3676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3677_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3674_, v_notDefEq_3676_);
    return v___x_3677_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(
    mut v_t_3678_: *mut leanh::LeanObject,
    mut v_defEq_3679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3680_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3678_, v_defEq_3679_);
    return v___x_3680_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(
    mut v_motive_3681_: *mut leanh::LeanObject,
    mut v_t_3682_: *mut leanh::LeanObject,
    mut v_h_3683_: *mut leanh::LeanObject,
    mut v_defEq_3684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3685_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3682_, v_defEq_3684_);
    return v___x_3685_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(
    mut v_t_3686_: *mut leanh::LeanObject,
    mut v_sizeLt_3687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3688_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3686_, v_sizeLt_3687_);
    return v___x_3688_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(
    mut v_motive_3689_: *mut leanh::LeanObject,
    mut v_t_3690_: *mut leanh::LeanObject,
    mut v_h_3691_: *mut leanh::LeanObject,
    mut v_sizeLt_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3693_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3690_, v_sizeLt_3692_);
    return v___x_3693_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(
    mut v_t_3694_: *mut leanh::LeanObject,
    mut v_depthLt_3695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3696_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3694_, v_depthLt_3695_);
    return v___x_3696_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(
    mut v_motive_3697_: *mut leanh::LeanObject,
    mut v_t_3698_: *mut leanh::LeanObject,
    mut v_h_3699_: *mut leanh::LeanObject,
    mut v_depthLt_3700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3701_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3698_, v_depthLt_3700_);
    return v___x_3701_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(
    mut v_t_3702_: *mut leanh::LeanObject,
    mut v_genLt_3703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3704_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3702_, v_genLt_3703_);
    return v___x_3704_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(
    mut v_motive_3705_: *mut leanh::LeanObject,
    mut v_t_3706_: *mut leanh::LeanObject,
    mut v_h_3707_: *mut leanh::LeanObject,
    mut v_genLt_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3709_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3706_, v_genLt_3708_);
    return v___x_3709_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(
    mut v_t_3710_: *mut leanh::LeanObject,
    mut v_isGround_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3710_, v_isGround_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(
    mut v_motive_3713_: *mut leanh::LeanObject,
    mut v_t_3714_: *mut leanh::LeanObject,
    mut v_h_3715_: *mut leanh::LeanObject,
    mut v_isGround_3716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3714_, v_isGround_3716_);
    return v___x_3717_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(
    mut v_t_3718_: *mut leanh::LeanObject,
    mut v_isValue_3719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3718_, v_isValue_3719_);
    return v___x_3720_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(
    mut v_motive_3721_: *mut leanh::LeanObject,
    mut v_t_3722_: *mut leanh::LeanObject,
    mut v_h_3723_: *mut leanh::LeanObject,
    mut v_isValue_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3725_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3722_, v_isValue_3724_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(
    mut v_t_3726_: *mut leanh::LeanObject,
    mut v_maxInsts_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3726_, v_maxInsts_3727_);
    return v___x_3728_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(
    mut v_motive_3729_: *mut leanh::LeanObject,
    mut v_t_3730_: *mut leanh::LeanObject,
    mut v_h_3731_: *mut leanh::LeanObject,
    mut v_maxInsts_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3733_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3730_, v_maxInsts_3732_);
    return v___x_3733_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(
    mut v_t_3734_: *mut leanh::LeanObject,
    mut v_guard_3735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3736_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3734_, v_guard_3735_);
    return v___x_3736_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(
    mut v_motive_3737_: *mut leanh::LeanObject,
    mut v_t_3738_: *mut leanh::LeanObject,
    mut v_h_3739_: *mut leanh::LeanObject,
    mut v_guard_3740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3741_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3738_, v_guard_3740_);
    return v___x_3741_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(
    mut v_t_3742_: *mut leanh::LeanObject,
    mut v_check_3743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3744_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3742_, v_check_3743_);
    return v___x_3744_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(
    mut v_motive_3745_: *mut leanh::LeanObject,
    mut v_t_3746_: *mut leanh::LeanObject,
    mut v_h_3747_: *mut leanh::LeanObject,
    mut v_check_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3749_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3746_, v_check_3748_);
    return v___x_3749_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(
    mut v_t_3750_: *mut leanh::LeanObject,
    mut v_notValue_3751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3752_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3750_, v_notValue_3751_);
    return v___x_3752_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(
    mut v_motive_3753_: *mut leanh::LeanObject,
    mut v_t_3754_: *mut leanh::LeanObject,
    mut v_h_3755_: *mut leanh::LeanObject,
    mut v_notValue_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3754_, v_notValue_3756_);
    return v___x_3757_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
    v___x_3759_ = leanh::lean_unsigned_to_nat(0);
    v___x_3760_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3760_, 0, v___x_3759_);
    leanh::lean_ctor_set(v___x_3760_, 1, v___x_3758_);
    return v___x_3760_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default()
-> *mut leanh::LeanObject {
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3761_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0,
    );
    return v___x_3761_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint()
-> *mut leanh::LeanObject {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
    return v___x_3762_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(
    mut v_x_3829_: *mut leanh::LeanObject,
    mut v_prec_3830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___y_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3856_: u8 = 0;
    let mut v_lhs_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___y_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_lhs_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3887_: u8 = 0;
    let mut v___y_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: u8 = 0;
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut v_lhs_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___y_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_n_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___y_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: u8 = 0;
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3957_: u8 = 0;
    let mut v_bvarIdx_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3961_: u8 = 0;
    let mut v___y_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: u8 = 0;
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_bvarIdx_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3980_: u8 = 0;
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___y_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut v_n_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___y_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v_e_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvarIdx_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4057_: u8 = 0;
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___y_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_x_3829_) {
                    0 => {
                        v_lhs_3831_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_rhs_3832_ = leanh::lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3856_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3856_ == 0 {
                            v___x_3834_ = v_x_3829_;
                            v_isShared_3835_ = v_isSharedCheck_3856_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_rhs_3832_);
                            leanh::lean_inc(v_lhs_3831_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_3834_ = leanh::lean_box(0);
                            v_isShared_3835_ = v_isSharedCheck_3856_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_lhs_3857_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_rhs_3858_ = leanh::lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3882_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3882_ == 0 {
                            v___x_3860_ = v_x_3829_;
                            v_isShared_3861_ = v_isSharedCheck_3882_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_rhs_3858_);
                            leanh::lean_inc(v_lhs_3857_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_3860_ = leanh::lean_box(0);
                            v_isShared_3861_ = v_isSharedCheck_3882_;
                            state = 4;
                            continue;
                        }
                    }
                    2 => {
                        v_lhs_3883_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_n_3884_ = leanh::lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3909_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3909_ == 0 {
                            v___x_3886_ = v_x_3829_;
                            v_isShared_3887_ = v_isSharedCheck_3909_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_3884_);
                            leanh::lean_inc(v_lhs_3883_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_3886_ = leanh::lean_box(0);
                            v_isShared_3887_ = v_isSharedCheck_3909_;
                            state = 7;
                            continue;
                        }
                    }
                    3 => {
                        v_lhs_3910_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_n_3911_ = leanh::lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3936_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3936_ == 0 {
                            v___x_3913_ = v_x_3829_;
                            v_isShared_3914_ = v_isSharedCheck_3936_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_3911_);
                            leanh::lean_inc(v_lhs_3910_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_3913_ = leanh::lean_box(0);
                            v_isShared_3914_ = v_isSharedCheck_3936_;
                            state = 10;
                            continue;
                        }
                    }
                    4 => {
                        v_n_3937_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_isSharedCheck_3957_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3957_ == 0 {
                            v___x_3939_ = v_x_3829_;
                            v_isShared_3940_ = v_isSharedCheck_3957_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_3937_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_3939_ = leanh::lean_box(0);
                            v_isShared_3940_ = v_isSharedCheck_3957_;
                            state = 13;
                            continue;
                        }
                    }
                    5 => {
                        v_bvarIdx_3958_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_isSharedCheck_3978_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3978_ == 0 {
                            v___x_3960_ = v_x_3829_;
                            v_isShared_3961_ = v_isSharedCheck_3978_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_bvarIdx_3958_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_3960_ = leanh::lean_box(0);
                            v_isShared_3961_ = v_isSharedCheck_3978_;
                            state = 16;
                            continue;
                        }
                    }
                    6 => {
                        v_bvarIdx_3979_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_strict_3980_ = leanh::lean_ctor_get_uint8(
                            v_x_3829_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        v_isSharedCheck_4004_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_4004_ == 0 {
                            v___x_3982_ = v_x_3829_;
                            v_isShared_3983_ = v_isSharedCheck_4004_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_bvarIdx_3979_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_3982_ = leanh::lean_box(0);
                            v_isShared_3983_ = v_isSharedCheck_4004_;
                            state = 19;
                            continue;
                        }
                    }
                    7 => {
                        v_n_4005_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_isSharedCheck_4025_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_4025_ == 0 {
                            v___x_4007_ = v_x_3829_;
                            v_isShared_4008_ = v_isSharedCheck_4025_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_4005_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_4007_ = leanh::lean_box(0);
                            v_isShared_4008_ = v_isSharedCheck_4025_;
                            state = 22;
                            continue;
                        }
                    }
                    8 => {
                        v_e_4026_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        leanh::lean_inc_ref(v_e_4026_);
                        leanh::lean_dec_ref_known(v_x_3829_, 1);
                        v___x_4037_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_4038_ = lean_nat_dec_le(v___x_4037_, v_prec_3830_);
                        if v___x_4038_ == 0 {
                            v___x_4039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_4028_ = v___x_4039_;
                            state = 25;
                            continue;
                        } else {
                            v___x_4040_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_4028_ = v___x_4040_;
                            state = 25;
                            continue;
                        }
                    }
                    9 => {
                        v_e_4041_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        leanh::lean_inc_ref(v_e_4041_);
                        leanh::lean_dec_ref_known(v_x_3829_, 1);
                        v___x_4052_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_4053_ = lean_nat_dec_le(v___x_4052_, v_prec_3830_);
                        if v___x_4053_ == 0 {
                            v___x_4054_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_4043_ = v___x_4054_;
                            state = 26;
                            continue;
                        } else {
                            v___x_4055_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_4043_ = v___x_4055_;
                            state = 26;
                            continue;
                        }
                    }
                    _ => {
                        v_bvarIdx_4056_ = leanh::lean_ctor_get(v_x_3829_, 0);
                        v_strict_4057_ = leanh::lean_ctor_get_uint8(
                            v_x_3829_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        v_isSharedCheck_4081_ = (!leanh::lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_4081_ == 0 {
                            v___x_4059_ = v_x_3829_;
                            v_isShared_4060_ = v_isSharedCheck_4081_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_inc(v_bvarIdx_4056_);
                            leanh::lean_dec(v_x_3829_);
                            v___x_4059_ = leanh::lean_box(0);
                            v_isShared_4060_ = v_isSharedCheck_4081_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3852_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3853_ = lean_nat_dec_le(v___x_3852_, v_prec_3830_);
                if v___x_3853_ == 0 {
                    v___x_3854_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_3837_ = v___x_3854_;
                    state = 2;
                    continue;
                } else {
                    v___x_3855_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_3837_ = v___x_3855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3838_ = leanh::lean_box(1);
                v___x_3839_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2;
                v___x_3840_ = l_Nat_reprFast(v_lhs_3831_);
                v___x_3841_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3841_, 0, v___x_3840_);
                if v_isShared_3835_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3834_, 5);
                    leanh::lean_ctor_set(v___x_3834_, 1, v___x_3841_);
                    leanh::lean_ctor_set(v___x_3834_, 0, v___x_3839_);
                    v___x_3843_ = v___x_3834_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3841_);
                    v___x_3843_ = v_reuseFailAlloc_3851_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3844_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3844_, 0, v___x_3843_);
                leanh::lean_ctor_set(v___x_3844_, 1, v___x_3838_);
                v___x_3845_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_3832_);
                v___x_3846_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3846_, 0, v___x_3844_);
                leanh::lean_ctor_set(v___x_3846_, 1, v___x_3845_);
                leanh::lean_inc(v___y_3837_);
                v___x_3847_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3847_, 0, v___y_3837_);
                leanh::lean_ctor_set(v___x_3847_, 1, v___x_3846_);
                v___x_3848_ = 0;
                v___x_3849_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3849_, 0, v___x_3847_);
                leanh::lean_ctor_set_uint8(
                    v___x_3849_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3848_,
                );
                v___x_3850_ = l_Repr_addAppParen(v___x_3849_, v_prec_3830_);
                return v___x_3850_;
            }
            4 => {
                v___x_3878_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3879_ = lean_nat_dec_le(v___x_3878_, v_prec_3830_);
                if v___x_3879_ == 0 {
                    v___x_3880_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_3863_ = v___x_3880_;
                    state = 5;
                    continue;
                } else {
                    v___x_3881_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_3863_ = v___x_3881_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3864_ = leanh::lean_box(1);
                v___x_3865_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5;
                v___x_3866_ = l_Nat_reprFast(v_lhs_3857_);
                v___x_3867_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3867_, 0, v___x_3866_);
                if v_isShared_3861_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3860_, 5);
                    leanh::lean_ctor_set(v___x_3860_, 1, v___x_3867_);
                    leanh::lean_ctor_set(v___x_3860_, 0, v___x_3865_);
                    v___x_3869_ = v___x_3860_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3877_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3867_);
                    v___x_3869_ = v_reuseFailAlloc_3877_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3870_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3870_, 0, v___x_3869_);
                leanh::lean_ctor_set(v___x_3870_, 1, v___x_3864_);
                v___x_3871_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_3858_);
                v___x_3872_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3872_, 0, v___x_3870_);
                leanh::lean_ctor_set(v___x_3872_, 1, v___x_3871_);
                leanh::lean_inc(v___y_3863_);
                v___x_3873_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3873_, 0, v___y_3863_);
                leanh::lean_ctor_set(v___x_3873_, 1, v___x_3872_);
                v___x_3874_ = 0;
                v___x_3875_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3875_, 0, v___x_3873_);
                leanh::lean_ctor_set_uint8(
                    v___x_3875_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3874_,
                );
                v___x_3876_ = l_Repr_addAppParen(v___x_3875_, v_prec_3830_);
                return v___x_3876_;
            }
            7 => {
                v___x_3905_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3906_ = lean_nat_dec_le(v___x_3905_, v_prec_3830_);
                if v___x_3906_ == 0 {
                    v___x_3907_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_3889_ = v___x_3907_;
                    state = 8;
                    continue;
                } else {
                    v___x_3908_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_3889_ = v___x_3908_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3890_ = leanh::lean_box(1);
                v___x_3891_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8;
                v___x_3892_ = l_Nat_reprFast(v_lhs_3883_);
                v___x_3893_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3893_, 0, v___x_3892_);
                if v_isShared_3887_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3886_, 5);
                    leanh::lean_ctor_set(v___x_3886_, 1, v___x_3893_);
                    leanh::lean_ctor_set(v___x_3886_, 0, v___x_3891_);
                    v___x_3895_ = v___x_3886_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3893_);
                    v___x_3895_ = v_reuseFailAlloc_3904_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3896_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3896_, 0, v___x_3895_);
                leanh::lean_ctor_set(v___x_3896_, 1, v___x_3890_);
                v___x_3897_ = l_Nat_reprFast(v_n_3884_);
                v___x_3898_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                v___x_3899_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3899_, 0, v___x_3896_);
                leanh::lean_ctor_set(v___x_3899_, 1, v___x_3898_);
                leanh::lean_inc(v___y_3889_);
                v___x_3900_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3900_, 0, v___y_3889_);
                leanh::lean_ctor_set(v___x_3900_, 1, v___x_3899_);
                v___x_3901_ = 0;
                v___x_3902_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3902_, 0, v___x_3900_);
                leanh::lean_ctor_set_uint8(
                    v___x_3902_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3901_,
                );
                v___x_3903_ = l_Repr_addAppParen(v___x_3902_, v_prec_3830_);
                return v___x_3903_;
            }
            10 => {
                v___x_3932_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3933_ = lean_nat_dec_le(v___x_3932_, v_prec_3830_);
                if v___x_3933_ == 0 {
                    v___x_3934_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_3916_ = v___x_3934_;
                    state = 11;
                    continue;
                } else {
                    v___x_3935_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_3916_ = v___x_3935_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3917_ = leanh::lean_box(1);
                v___x_3918_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11;
                v___x_3919_ = l_Nat_reprFast(v_lhs_3910_);
                v___x_3920_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3920_, 0, v___x_3919_);
                if v_isShared_3914_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3913_, 5);
                    leanh::lean_ctor_set(v___x_3913_, 1, v___x_3920_);
                    leanh::lean_ctor_set(v___x_3913_, 0, v___x_3918_);
                    v___x_3922_ = v___x_3913_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3920_);
                    v___x_3922_ = v_reuseFailAlloc_3931_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3923_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3923_, 0, v___x_3922_);
                leanh::lean_ctor_set(v___x_3923_, 1, v___x_3917_);
                v___x_3924_ = l_Nat_reprFast(v_n_3911_);
                v___x_3925_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3925_, 0, v___x_3924_);
                v___x_3926_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3926_, 0, v___x_3923_);
                leanh::lean_ctor_set(v___x_3926_, 1, v___x_3925_);
                leanh::lean_inc(v___y_3916_);
                v___x_3927_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3927_, 0, v___y_3916_);
                leanh::lean_ctor_set(v___x_3927_, 1, v___x_3926_);
                v___x_3928_ = 0;
                v___x_3929_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3929_, 0, v___x_3927_);
                leanh::lean_ctor_set_uint8(
                    v___x_3929_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3928_,
                );
                v___x_3930_ = l_Repr_addAppParen(v___x_3929_, v_prec_3830_);
                return v___x_3930_;
            }
            13 => {
                v___x_3953_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3954_ = lean_nat_dec_le(v___x_3953_, v_prec_3830_);
                if v___x_3954_ == 0 {
                    v___x_3955_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_3942_ = v___x_3955_;
                    state = 14;
                    continue;
                } else {
                    v___x_3956_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_3942_ = v___x_3956_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3943_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14;
                v___x_3944_ = l_Nat_reprFast(v_n_3937_);
                if v_isShared_3940_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3939_, 3);
                    leanh::lean_ctor_set(v___x_3939_, 0, v___x_3944_);
                    v___x_3946_ = v___x_3939_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3952_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3944_);
                    v___x_3946_ = v_reuseFailAlloc_3952_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3947_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3947_, 0, v___x_3943_);
                leanh::lean_ctor_set(v___x_3947_, 1, v___x_3946_);
                leanh::lean_inc(v___y_3942_);
                v___x_3948_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3948_, 0, v___y_3942_);
                leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = 0;
                v___x_3950_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                leanh::lean_ctor_set_uint8(
                    v___x_3950_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3949_,
                );
                v___x_3951_ = l_Repr_addAppParen(v___x_3950_, v_prec_3830_);
                return v___x_3951_;
            }
            16 => {
                v___x_3974_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3975_ = lean_nat_dec_le(v___x_3974_, v_prec_3830_);
                if v___x_3975_ == 0 {
                    v___x_3976_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_3963_ = v___x_3976_;
                    state = 17;
                    continue;
                } else {
                    v___x_3977_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_3963_ = v___x_3977_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3964_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17;
                v___x_3965_ = l_Nat_reprFast(v_bvarIdx_3958_);
                if v_isShared_3961_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3960_, 3);
                    leanh::lean_ctor_set(v___x_3960_, 0, v___x_3965_);
                    v___x_3967_ = v___x_3960_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3973_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3965_);
                    v___x_3967_ = v_reuseFailAlloc_3973_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3968_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3968_, 0, v___x_3964_);
                leanh::lean_ctor_set(v___x_3968_, 1, v___x_3967_);
                leanh::lean_inc(v___y_3963_);
                v___x_3969_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3969_, 0, v___y_3963_);
                leanh::lean_ctor_set(v___x_3969_, 1, v___x_3968_);
                v___x_3970_ = 0;
                v___x_3971_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3971_, 0, v___x_3969_);
                leanh::lean_ctor_set_uint8(
                    v___x_3971_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3970_,
                );
                v___x_3972_ = l_Repr_addAppParen(v___x_3971_, v_prec_3830_);
                return v___x_3972_;
            }
            19 => {
                v___x_4000_ = leanh::lean_unsigned_to_nat(1024);
                v___x_4001_ = lean_nat_dec_le(v___x_4000_, v_prec_3830_);
                if v___x_4001_ == 0 {
                    v___x_4002_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_3985_ = v___x_4002_;
                    state = 20;
                    continue;
                } else {
                    v___x_4003_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_3985_ = v___x_4003_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3986_ = leanh::lean_box(1);
                v___x_3987_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20;
                v___x_3988_ = l_Nat_reprFast(v_bvarIdx_3979_);
                v___x_3989_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3989_, 0, v___x_3988_);
                v___x_3990_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3990_, 0, v___x_3987_);
                leanh::lean_ctor_set(v___x_3990_, 1, v___x_3989_);
                v___x_3991_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3991_, 0, v___x_3990_);
                leanh::lean_ctor_set(v___x_3991_, 1, v___x_3986_);
                v___x_3992_ = l_Bool_repr___redArg(v_strict_3980_);
                v___x_3993_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3993_, 0, v___x_3991_);
                leanh::lean_ctor_set(v___x_3993_, 1, v___x_3992_);
                leanh::lean_inc(v___y_3985_);
                v___x_3994_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3994_, 0, v___y_3985_);
                leanh::lean_ctor_set(v___x_3994_, 1, v___x_3993_);
                v___x_3995_ = 0;
                if v_isShared_3983_ == 0 {
                    leanh::lean_ctor_set(v___x_3982_, 0, v___x_3994_);
                    v___x_3997_ = v___x_3982_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3994_);
                    v___x_3997_ = v_reuseFailAlloc_3999_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3997_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3995_,
                );
                v___x_3998_ = l_Repr_addAppParen(v___x_3997_, v_prec_3830_);
                return v___x_3998_;
            }
            22 => {
                v___x_4021_ = leanh::lean_unsigned_to_nat(1024);
                v___x_4022_ = lean_nat_dec_le(v___x_4021_, v_prec_3830_);
                if v___x_4022_ == 0 {
                    v___x_4023_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_4010_ = v___x_4023_;
                    state = 23;
                    continue;
                } else {
                    v___x_4024_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_4010_ = v___x_4024_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_4011_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23;
                v___x_4012_ = l_Nat_reprFast(v_n_4005_);
                if v_isShared_4008_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4007_, 3);
                    leanh::lean_ctor_set(v___x_4007_, 0, v___x_4012_);
                    v___x_4014_ = v___x_4007_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4020_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4012_);
                    v___x_4014_ = v_reuseFailAlloc_4020_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_4015_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4015_, 0, v___x_4011_);
                leanh::lean_ctor_set(v___x_4015_, 1, v___x_4014_);
                leanh::lean_inc(v___y_4010_);
                v___x_4016_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4016_, 0, v___y_4010_);
                leanh::lean_ctor_set(v___x_4016_, 1, v___x_4015_);
                v___x_4017_ = 0;
                v___x_4018_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4018_, 0, v___x_4016_);
                leanh::lean_ctor_set_uint8(
                    v___x_4018_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4017_,
                );
                v___x_4019_ = l_Repr_addAppParen(v___x_4018_, v_prec_3830_);
                return v___x_4019_;
            }
            25 => {
                v___x_4029_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26;
                v___x_4030_ = leanh::lean_unsigned_to_nat(1024);
                v___x_4031_ = l_Lean_instReprExpr_repr(v_e_4026_, v___x_4030_);
                v___x_4032_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4032_, 0, v___x_4029_);
                leanh::lean_ctor_set(v___x_4032_, 1, v___x_4031_);
                leanh::lean_inc(v___y_4028_);
                v___x_4033_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4033_, 0, v___y_4028_);
                leanh::lean_ctor_set(v___x_4033_, 1, v___x_4032_);
                v___x_4034_ = 0;
                v___x_4035_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4035_, 0, v___x_4033_);
                leanh::lean_ctor_set_uint8(
                    v___x_4035_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4034_,
                );
                v___x_4036_ = l_Repr_addAppParen(v___x_4035_, v_prec_3830_);
                return v___x_4036_;
            }
            26 => {
                v___x_4044_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29;
                v___x_4045_ = leanh::lean_unsigned_to_nat(1024);
                v___x_4046_ = l_Lean_instReprExpr_repr(v_e_4041_, v___x_4045_);
                v___x_4047_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4047_, 0, v___x_4044_);
                leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                leanh::lean_inc(v___y_4043_);
                v___x_4048_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4048_, 0, v___y_4043_);
                leanh::lean_ctor_set(v___x_4048_, 1, v___x_4047_);
                v___x_4049_ = 0;
                v___x_4050_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4050_, 0, v___x_4048_);
                leanh::lean_ctor_set_uint8(
                    v___x_4050_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4049_,
                );
                v___x_4051_ = l_Repr_addAppParen(v___x_4050_, v_prec_3830_);
                return v___x_4051_;
            }
            27 => {
                v___x_4077_ = leanh::lean_unsigned_to_nat(1024);
                v___x_4078_ = lean_nat_dec_le(v___x_4077_, v_prec_3830_);
                if v___x_4078_ == 0 {
                    v___x_4079_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13,
                    );
                    v___y_4062_ = v___x_4079_;
                    state = 28;
                    continue;
                } else {
                    v___x_4080_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14,
                    );
                    v___y_4062_ = v___x_4080_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4063_ = leanh::lean_box(1);
                v___x_4064_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32;
                v___x_4065_ = l_Nat_reprFast(v_bvarIdx_4056_);
                v___x_4066_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4066_, 0, v___x_4065_);
                v___x_4067_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4067_, 0, v___x_4064_);
                leanh::lean_ctor_set(v___x_4067_, 1, v___x_4066_);
                v___x_4068_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4068_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4068_, 1, v___x_4063_);
                v___x_4069_ = l_Bool_repr___redArg(v_strict_4057_);
                v___x_4070_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4070_, 0, v___x_4068_);
                leanh::lean_ctor_set(v___x_4070_, 1, v___x_4069_);
                leanh::lean_inc(v___y_4062_);
                v___x_4071_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4071_, 0, v___y_4062_);
                leanh::lean_ctor_set(v___x_4071_, 1, v___x_4070_);
                v___x_4072_ = 0;
                if v_isShared_4060_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4059_, 6);
                    leanh::lean_ctor_set(v___x_4059_, 0, v___x_4071_);
                    v___x_4074_ = v___x_4059_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4071_);
                    v___x_4074_ = v_reuseFailAlloc_4076_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4074_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4072_,
                );
                v___x_4075_ = l_Repr_addAppParen(v___x_4074_, v_prec_3830_);
                return v___x_4075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(
    mut v_x_4082_: *mut leanh::LeanObject,
    mut v_prec_4083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4084_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_4082_, v_prec_4083_);
    leanh::lean_dec(v_prec_4083_);
    return v_res_4084_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(
    mut v_x_4087_: *mut leanh::LeanObject,
    mut v_x_4088_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lhs_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_x27_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_x27_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: u8 = 0;
    let mut v_lhs_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_x27_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_x27_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: u8 = 0;
    let mut v___x_4102_: u8 = 0;
    let mut v_bvarIdx_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4105_: u8 = 0;
    let mut v_bvarIdx_x27_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_x27_4107_: u8 = 0;
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: u8 = 0;
    let mut v_lhs_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvarIdx_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4129_: u8 = 0;
    let mut v_bvarIdx_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4131_: u8 = 0;
    let mut v_e_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v_e_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    let mut v_bvarIdx_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4139_: u8 = 0;
    let mut v_bvarIdx_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4141_: u8 = 0;
    let mut v_n_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4109_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_4087_);
                v___x_4110_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_4088_);
                v___x_4111_ = lean_nat_dec_eq(v___x_4109_, v___x_4110_);
                leanh::lean_dec(v___x_4110_);
                leanh::lean_dec(v___x_4109_);
                if v___x_4111_ == 0 {
                    return v___x_4111_;
                } else {
                    match leanh::lean_obj_tag(v_x_4087_) {
                        0 => {
                            v_lhs_4112_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_rhs_4113_ = leanh::lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4114_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v_rhs_4115_ = leanh::lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4090_ = v_lhs_4112_;
                            v_rhs_4091_ = v_rhs_4113_;
                            v_lhs_x27_4092_ = v_lhs_4114_;
                            v_rhs_x27_4093_ = v_rhs_4115_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_lhs_4116_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_rhs_4117_ = leanh::lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4118_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v_rhs_4119_ = leanh::lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4090_ = v_lhs_4116_;
                            v_rhs_4091_ = v_rhs_4117_;
                            v_lhs_x27_4092_ = v_lhs_4118_;
                            v_rhs_x27_4093_ = v_rhs_4119_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_lhs_4120_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_n_4121_ = leanh::lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4122_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v_n_4123_ = leanh::lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4097_ = v_lhs_4120_;
                            v_n_4098_ = v_n_4121_;
                            v_lhs_x27_4099_ = v_lhs_4122_;
                            v_n_x27_4100_ = v_n_4123_;
                            state = 2;
                            continue;
                        }
                        3 => {
                            v_lhs_4124_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_n_4125_ = leanh::lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4126_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v_n_4127_ = leanh::lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4097_ = v_lhs_4124_;
                            v_n_4098_ = v_n_4125_;
                            v_lhs_x27_4099_ = v_lhs_4126_;
                            v_n_x27_4100_ = v_n_4127_;
                            state = 2;
                            continue;
                        }
                        6 => {
                            v_bvarIdx_4128_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_strict_4129_ = leanh::lean_ctor_get_uint8(
                                v_x_4087_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4130_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v_strict_4131_ = leanh::lean_ctor_get_uint8(
                                v_x_4088_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4104_ = v_bvarIdx_4128_;
                            v_strict_4105_ = v_strict_4129_;
                            v_bvarIdx_x27_4106_ = v_bvarIdx_4130_;
                            v_strict_x27_4107_ = v_strict_4131_;
                            state = 3;
                            continue;
                        }
                        8 => {
                            v_e_4132_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_e_4133_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v___x_4134_ = lean_expr_eqv(v_e_4132_, v_e_4133_);
                            return v___x_4134_;
                        }
                        9 => {
                            v_e_4135_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_e_4136_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v___x_4137_ = lean_expr_eqv(v_e_4135_, v_e_4136_);
                            return v___x_4137_;
                        }
                        10 => {
                            v_bvarIdx_4138_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_strict_4139_ = leanh::lean_ctor_get_uint8(
                                v_x_4087_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4140_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v_strict_4141_ = leanh::lean_ctor_get_uint8(
                                v_x_4088_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4104_ = v_bvarIdx_4138_;
                            v_strict_4105_ = v_strict_4139_;
                            v_bvarIdx_x27_4106_ = v_bvarIdx_4140_;
                            v_strict_x27_4107_ = v_strict_4141_;
                            state = 3;
                            continue;
                        }
                        _ => {
                            v_n_4142_ = leanh::lean_ctor_get(v_x_4087_, 0);
                            v_n_4143_ = leanh::lean_ctor_get(v_x_4088_, 0);
                            v___x_4144_ = lean_nat_dec_eq(v_n_4142_, v_n_4143_);
                            return v___x_4144_;
                        }
                    }
                }
            }
            1 => {
                v___x_4094_ = lean_nat_dec_eq(v_lhs_4090_, v_lhs_x27_4092_);
                if v___x_4094_ == 0 {
                    return v___x_4094_;
                } else {
                    v___x_4095_ =
                        l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_rhs_4091_, v_rhs_x27_4093_);
                    return v___x_4095_;
                }
            }
            2 => {
                v___x_4101_ = lean_nat_dec_eq(v_lhs_4097_, v_lhs_x27_4099_);
                if v___x_4101_ == 0 {
                    return v___x_4101_;
                } else {
                    v___x_4102_ = lean_nat_dec_eq(v_n_4098_, v_n_x27_4100_);
                    return v___x_4102_;
                }
            }
            3 => {
                v___x_4108_ = lean_nat_dec_eq(v_bvarIdx_4104_, v_bvarIdx_x27_4106_);
                if v___x_4108_ == 0 {
                    return v___x_4108_;
                } else {
                    if v_strict_4105_ == 0 {
                        if v_strict_x27_4107_ == 0 {
                            return v___x_4108_;
                        } else {
                            return v_strict_4105_;
                        }
                    } else {
                        return v_strict_x27_4107_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(
    mut v_x_4145_: *mut leanh::LeanObject,
    mut v_x_4146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4147_: u8 = 0;
    let mut v_r_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_4145_, v_x_4146_);
    leanh::lean_dec_ref(v_x_4146_);
    leanh::lean_dec_ref(v_x_4145_);
    v_r_4148_ = leanh::lean_box((v_res_4147_) as usize);
    return v_r_4148_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4151_: u8 = 0;
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4151_ = 0;
    v___x_4152_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default;
    v___x_4153_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
    v___x_4154_ = leanh::lean_box(0);
    v___x_4155_ = leanh::lean_unsigned_to_nat(0);
    v___x_4156_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3,
    );
    v___x_4157_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0;
    v___x_4158_ = leanh::lean_alloc_ctor(0, 8, (1) as u32);
    leanh::lean_ctor_set(v___x_4158_, 0, v___x_4157_);
    leanh::lean_ctor_set(v___x_4158_, 1, v___x_4156_);
    leanh::lean_ctor_set(v___x_4158_, 2, v___x_4155_);
    leanh::lean_ctor_set(v___x_4158_, 3, v___x_4154_);
    leanh::lean_ctor_set(v___x_4158_, 4, v___x_4154_);
    leanh::lean_ctor_set(v___x_4158_, 5, v___x_4153_);
    leanh::lean_ctor_set(v___x_4158_, 6, v___x_4152_);
    leanh::lean_ctor_set(v___x_4158_, 7, v___x_4154_);
    leanh::lean_ctor_set_uint8(
        v___x_4158_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
        v___x_4151_,
    );
    return v___x_4158_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default()
-> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0,
    );
    return v___x_4159_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem() -> *mut leanh::LeanObject
{
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
    return v___x_4160_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(
    mut v_thm_4161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_symbols_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_symbols_4162_ = leanh::lean_ctor_get(v_thm_4161_, 4);
    leanh::lean_inc(v_symbols_4162_);
    return v_symbols_4162_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(
    mut v_thm_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4164_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_4163_);
    leanh::lean_dec_ref(v_thm_4163_);
    return v_res_4164_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(
    mut v_thm_4165_: *mut leanh::LeanObject,
    mut v_symbols_4166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levelParams_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minIndexable_4173_: u8 = 0;
    let mut v_cnstrs_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_unused_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_levelParams_4167_ = leanh::lean_ctor_get(v_thm_4165_, 0);
                v_proof_4168_ = leanh::lean_ctor_get(v_thm_4165_, 1);
                v_numParams_4169_ = leanh::lean_ctor_get(v_thm_4165_, 2);
                v_patterns_4170_ = leanh::lean_ctor_get(v_thm_4165_, 3);
                v_origin_4171_ = leanh::lean_ctor_get(v_thm_4165_, 5);
                v_kind_4172_ = leanh::lean_ctor_get(v_thm_4165_, 6);
                v_minIndexable_4173_ = leanh::lean_ctor_get_uint8(
                    v_thm_4165_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                v_cnstrs_4174_ = leanh::lean_ctor_get(v_thm_4165_, 7);
                v_isSharedCheck_4181_ = (!leanh::lean_is_exclusive(v_thm_4165_)) as u8;
                if v_isSharedCheck_4181_ == 0 {
                    v_unused_4182_ = leanh::lean_ctor_get(v_thm_4165_, 4);
                    leanh::lean_dec(v_unused_4182_);
                    v___x_4176_ = v_thm_4165_;
                    v_isShared_4177_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cnstrs_4174_);
                    leanh::lean_inc(v_kind_4172_);
                    leanh::lean_inc(v_origin_4171_);
                    leanh::lean_inc(v_patterns_4170_);
                    leanh::lean_inc(v_numParams_4169_);
                    leanh::lean_inc(v_proof_4168_);
                    leanh::lean_inc(v_levelParams_4167_);
                    leanh::lean_dec(v_thm_4165_);
                    v___x_4176_ = leanh::lean_box(0);
                    v_isShared_4177_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4177_ == 0 {
                    leanh::lean_ctor_set(v___x_4176_, 4, v_symbols_4166_);
                    v___x_4179_ = v___x_4176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = leanh::lean_alloc_ctor(0, 8, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_levelParams_4167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_proof_4168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_numParams_4169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_patterns_4170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_symbols_4166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 5, v_origin_4171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 6, v_kind_4172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 7, v_cnstrs_4174_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4180_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                        v_minIndexable_4173_,
                    );
                    v___x_4179_ = v_reuseFailAlloc_4180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(
    mut v_thm_4183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_origin_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_origin_4184_ = leanh::lean_ctor_get(v_thm_4183_, 5);
    leanh::lean_inc_ref(v_origin_4184_);
    return v_origin_4184_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(
    mut v_thm_4185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4186_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_4185_);
    leanh::lean_dec_ref(v_thm_4185_);
    return v_res_4186_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(
    mut v_thm_4187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_proof_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_proof_4188_ = leanh::lean_ctor_get(v_thm_4187_, 1);
    leanh::lean_inc_ref(v_proof_4188_);
    return v_proof_4188_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(
    mut v_thm_4189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4190_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_4189_);
    leanh::lean_dec_ref(v_thm_4189_);
    return v_res_4190_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(
    mut v_thm_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levelParams_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_levelParams_4192_ = leanh::lean_ctor_get(v_thm_4191_, 0);
    leanh::lean_inc_ref(v_levelParams_4192_);
    return v_levelParams_4192_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(
    mut v_thm_4193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4194_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_4193_);
    leanh::lean_dec_ref(v_thm_4193_);
    return v_res_4194_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
    v___x_4208_ = leanh::lean_box(0);
    v___x_4209_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3,
    );
    v___x_4210_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0;
    v___x_4211_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4211_, 0, v___x_4210_);
    leanh::lean_ctor_set(v___x_4211_, 1, v___x_4209_);
    leanh::lean_ctor_set(v___x_4211_, 2, v___x_4208_);
    leanh::lean_ctor_set(v___x_4211_, 3, v___x_4207_);
    return v___x_4211_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default()
-> *mut leanh::LeanObject {
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4212_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0,
    );
    return v___x_4212_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem()
-> *mut leanh::LeanObject {
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4213_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
    return v___x_4213_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(
    mut v_thm_4214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_symbols_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_symbols_4215_ = leanh::lean_ctor_get(v_thm_4214_, 2);
    leanh::lean_inc(v_symbols_4215_);
    return v_symbols_4215_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(
    mut v_thm_4216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4217_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_4216_);
    leanh::lean_dec_ref(v_thm_4216_);
    return v_res_4217_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(
    mut v_thm_4218_: *mut leanh::LeanObject,
    mut v_symbols_4219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levelParams_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_unused_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_levelParams_4220_ = leanh::lean_ctor_get(v_thm_4218_, 0);
                v_proof_4221_ = leanh::lean_ctor_get(v_thm_4218_, 1);
                v_origin_4222_ = leanh::lean_ctor_get(v_thm_4218_, 3);
                v_isSharedCheck_4229_ = (!leanh::lean_is_exclusive(v_thm_4218_)) as u8;
                if v_isSharedCheck_4229_ == 0 {
                    v_unused_4230_ = leanh::lean_ctor_get(v_thm_4218_, 2);
                    leanh::lean_dec(v_unused_4230_);
                    v___x_4224_ = v_thm_4218_;
                    v_isShared_4225_ = v_isSharedCheck_4229_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_origin_4222_);
                    leanh::lean_inc(v_proof_4221_);
                    leanh::lean_inc(v_levelParams_4220_);
                    leanh::lean_dec(v_thm_4218_);
                    v___x_4224_ = leanh::lean_box(0);
                    v_isShared_4225_ = v_isSharedCheck_4229_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4225_ == 0 {
                    leanh::lean_ctor_set(v___x_4224_, 2, v_symbols_4219_);
                    v___x_4227_ = v___x_4224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_levelParams_4220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 1, v_proof_4221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 2, v_symbols_4219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 3, v_origin_4222_);
                    v___x_4227_ = v_reuseFailAlloc_4228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(
    mut v_thm_4231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_origin_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_origin_4232_ = leanh::lean_ctor_get(v_thm_4231_, 3);
    leanh::lean_inc_ref(v_origin_4232_);
    return v_origin_4232_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(
    mut v_thm_4233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4234_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_4233_);
    leanh::lean_dec_ref(v_thm_4233_);
    return v_res_4234_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(
    mut v_thm_4235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_proof_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_proof_4236_ = leanh::lean_ctor_get(v_thm_4235_, 1);
    leanh::lean_inc_ref(v_proof_4236_);
    return v_proof_4236_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(
    mut v_thm_4237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4238_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_4237_);
    leanh::lean_dec_ref(v_thm_4237_);
    return v_res_4238_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(
    mut v_thm_4239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levelParams_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_levelParams_4240_ = leanh::lean_ctor_get(v_thm_4239_, 0);
    leanh::lean_inc_ref(v_levelParams_4240_);
    return v_levelParams_4240_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(
    mut v_thm_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4242_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_4241_);
    leanh::lean_dec_ref(v_thm_4241_);
    return v_res_4242_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorIdx(
    mut v_x_4255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_4255_) {
        0 => {
            let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4256_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4256_;
        }
        1 => {
            let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4257_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4257_;
        }
        2 => {
            let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4258_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4258_;
        }
        3 => {
            let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4259_ = leanh::lean_unsigned_to_nat(3);
            return v___x_4259_;
        }
        _ => {
            let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4260_ = leanh::lean_unsigned_to_nat(4);
            return v___x_4260_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorIdx___boxed(
    mut v_x_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4262_ = l_Lean_Meta_Grind_Entry_ctorIdx(v_x_4261_);
    leanh::lean_dec_ref(v_x_4261_);
    return v_res_4262_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorElim___redArg(
    mut v_t_4263_: *mut leanh::LeanObject,
    mut v_k_4264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_4263_) {
        2 => {
            let mut v_declName_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_eager_4266_: u8 = 0;
            let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_declName_4265_ = leanh::lean_ctor_get(v_t_4263_, 0);
            leanh::lean_inc(v_declName_4265_);
            v_eager_4266_ = leanh::lean_ctor_get_uint8(
                v_t_4263_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            );
            leanh::lean_dec_ref_known(v_t_4263_, 1);
            v___x_4267_ = leanh::lean_box((v_eager_4266_) as usize);
            v___x_4268_ = leanh::lean_apply_2(v_k_4264_, v_declName_4265_, v___x_4267_);
            return v___x_4268_;
        }
        3 => {
            let mut v_thm_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_thm_4269_ = leanh::lean_ctor_get(v_t_4263_, 0);
            leanh::lean_inc_ref(v_thm_4269_);
            leanh::lean_dec_ref_known(v_t_4263_, 1);
            v___x_4270_ = leanh::lean_apply_1(v_k_4264_, v_thm_4269_);
            return v___x_4270_;
        }
        4 => {
            let mut v_thm_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_thm_4271_ = leanh::lean_ctor_get(v_t_4263_, 0);
            leanh::lean_inc_ref(v_thm_4271_);
            leanh::lean_dec_ref_known(v_t_4263_, 1);
            v___x_4272_ = leanh::lean_apply_1(v_k_4264_, v_thm_4271_);
            return v___x_4272_;
        }
        _ => {
            let mut v_declName_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_declName_4273_ = leanh::lean_ctor_get(v_t_4263_, 0);
            leanh::lean_inc(v_declName_4273_);
            leanh::lean_dec_ref(v_t_4263_);
            v___x_4274_ = leanh::lean_apply_1(v_k_4264_, v_declName_4273_);
            return v___x_4274_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorElim(
    mut v_motive_4275_: *mut leanh::LeanObject,
    mut v_ctorIdx_4276_: *mut leanh::LeanObject,
    mut v_t_4277_: *mut leanh::LeanObject,
    mut v_h_4278_: *mut leanh::LeanObject,
    mut v_k_4279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4280_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4277_, v_k_4279_);
    return v___x_4280_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorElim___boxed(
    mut v_motive_4281_: *mut leanh::LeanObject,
    mut v_ctorIdx_4282_: *mut leanh::LeanObject,
    mut v_t_4283_: *mut leanh::LeanObject,
    mut v_h_4284_: *mut leanh::LeanObject,
    mut v_k_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_Meta_Grind_Entry_ctorElim(
        v_motive_4281_,
        v_ctorIdx_4282_,
        v_t_4283_,
        v_h_4284_,
        v_k_4285_,
    );
    leanh::lean_dec(v_ctorIdx_4282_);
    return v_res_4286_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ext_elim___redArg(
    mut v_t_4287_: *mut leanh::LeanObject,
    mut v_ext_4288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4289_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4287_, v_ext_4288_);
    return v___x_4289_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ext_elim(
    mut v_motive_4290_: *mut leanh::LeanObject,
    mut v_t_4291_: *mut leanh::LeanObject,
    mut v_h_4292_: *mut leanh::LeanObject,
    mut v_ext_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4291_, v_ext_4293_);
    return v___x_4294_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_funCC_elim___redArg(
    mut v_t_4295_: *mut leanh::LeanObject,
    mut v_funCC_4296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4295_, v_funCC_4296_);
    return v___x_4297_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_funCC_elim(
    mut v_motive_4298_: *mut leanh::LeanObject,
    mut v_t_4299_: *mut leanh::LeanObject,
    mut v_h_4300_: *mut leanh::LeanObject,
    mut v_funCC_4301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4302_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4299_, v_funCC_4301_);
    return v___x_4302_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_cases_elim___redArg(
    mut v_t_4303_: *mut leanh::LeanObject,
    mut v_cases_4304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4305_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4303_, v_cases_4304_);
    return v___x_4305_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_cases_elim(
    mut v_motive_4306_: *mut leanh::LeanObject,
    mut v_t_4307_: *mut leanh::LeanObject,
    mut v_h_4308_: *mut leanh::LeanObject,
    mut v_cases_4309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4310_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4307_, v_cases_4309_);
    return v___x_4310_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ematch_elim___redArg(
    mut v_t_4311_: *mut leanh::LeanObject,
    mut v_ematch_4312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4313_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4311_, v_ematch_4312_);
    return v___x_4313_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ematch_elim(
    mut v_motive_4314_: *mut leanh::LeanObject,
    mut v_t_4315_: *mut leanh::LeanObject,
    mut v_h_4316_: *mut leanh::LeanObject,
    mut v_ematch_4317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4315_, v_ematch_4317_);
    return v___x_4318_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_inj_elim___redArg(
    mut v_t_4319_: *mut leanh::LeanObject,
    mut v_inj_4320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4321_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4319_, v_inj_4320_);
    return v___x_4321_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_inj_elim(
    mut v_motive_4322_: *mut leanh::LeanObject,
    mut v_t_4323_: *mut leanh::LeanObject,
    mut v_h_4324_: *mut leanh::LeanObject,
    mut v_inj_4325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4326_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4323_, v_inj_4325_);
    return v___x_4326_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4331_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4332_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
    v___x_4333_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4333_, 0, v___x_4332_);
    return v___x_4333_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(
    mut v_00_u03b2_4334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4335_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1);
    return v___x_4335_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4336_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(leanh::lean_box(0));
    return v___x_4336_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4337_ = l_Lean_Meta_Grind_Theorems_mkEmpty(leanh::lean_box(0));
    return v___x_4337_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4338_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1,
    );
    v___x_4339_ = l_Lean_NameSet_empty;
    v___x_4340_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0,
    );
    v___x_4341_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once),
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1,
    );
    v___x_4342_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4342_, 0, v___x_4341_);
    leanh::lean_ctor_set(v___x_4342_, 1, v___x_4340_);
    leanh::lean_ctor_set(v___x_4342_, 2, v___x_4339_);
    leanh::lean_ctor_set(v___x_4342_, 3, v___x_4338_);
    leanh::lean_ctor_set(v___x_4342_, 4, v___x_4338_);
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default()
-> *mut leanh::LeanObject {
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2,
    );
    return v___x_4343_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState() -> *mut leanh::LeanObject
{
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4344_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
    return v___x_4344_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(
    mut v_x_4345_: *mut leanh::LeanObject,
    mut v_x_4346_: *mut leanh::LeanObject,
    mut v_x_4347_: *mut leanh::LeanObject,
    mut v_x_4348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4353_: u8 = 0;
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4349_ = leanh::lean_ctor_get(v_x_4345_, 0);
                v_vs_4350_ = leanh::lean_ctor_get(v_x_4345_, 1);
                v_isSharedCheck_4376_ = (!leanh::lean_is_exclusive(v_x_4345_)) as u8;
                if v_isSharedCheck_4376_ == 0 {
                    v___x_4352_ = v_x_4345_;
                    v_isShared_4353_ = v_isSharedCheck_4376_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4350_);
                    leanh::lean_inc(v_ks_4349_);
                    leanh::lean_dec(v_x_4345_);
                    v___x_4352_ = leanh::lean_box(0);
                    v_isShared_4353_ = v_isSharedCheck_4376_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4354_ = lean_array_get_size(v_ks_4349_);
                v___x_4355_ = lean_nat_dec_lt(v_x_4346_, v___x_4354_);
                if v___x_4355_ == 0 {
                    leanh::lean_dec(v_x_4346_);
                    v___x_4356_ = lean_array_push(v_ks_4349_, v_x_4347_);
                    v___x_4357_ = lean_array_push(v_vs_4350_, v_x_4348_);
                    if v_isShared_4353_ == 0 {
                        leanh::lean_ctor_set(v___x_4352_, 1, v___x_4357_);
                        leanh::lean_ctor_set(v___x_4352_, 0, v___x_4356_);
                        v___x_4359_ = v___x_4352_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4360_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4356_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4360_, 1, v___x_4357_);
                        v___x_4359_ = v_reuseFailAlloc_4360_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4361_ = lean_array_fget_borrowed(v_ks_4349_, v_x_4346_);
                    v___x_4362_ = l_Lean_Meta_Grind_Origin_key(v_x_4347_);
                    v___x_4363_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_4361_);
                    v___x_4364_ = lean_name_eq(v___x_4362_, v___x_4363_);
                    leanh::lean_dec(v___x_4363_);
                    leanh::lean_dec(v___x_4362_);
                    if v___x_4364_ == 0 {
                        if v_isShared_4353_ == 0 {
                            v___x_4366_ = v___x_4352_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4370_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_ks_4349_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_vs_4350_);
                            v___x_4366_ = v_reuseFailAlloc_4370_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4371_ = lean_array_fset(v_ks_4349_, v_x_4346_, v_x_4347_);
                        v___x_4372_ = lean_array_fset(v_vs_4350_, v_x_4346_, v_x_4348_);
                        leanh::lean_dec(v_x_4346_);
                        if v_isShared_4353_ == 0 {
                            leanh::lean_ctor_set(v___x_4352_, 1, v___x_4372_);
                            leanh::lean_ctor_set(v___x_4352_, 0, v___x_4371_);
                            v___x_4374_ = v___x_4352_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4375_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4371_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 1, v___x_4372_);
                            v___x_4374_ = v_reuseFailAlloc_4375_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4359_;
            }
            3 => {
                v___x_4367_ = leanh::lean_unsigned_to_nat(1);
                v___x_4368_ = lean_nat_add(v_x_4346_, v___x_4367_);
                leanh::lean_dec(v_x_4346_);
                v_x_4345_ = v___x_4366_;
                v_x_4346_ = v___x_4368_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_n_4377_: *mut leanh::LeanObject,
    mut v_k_4378_: *mut leanh::LeanObject,
    mut v_v_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = leanh::lean_unsigned_to_nat(0);
    v___x_4381_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_n_4377_, v___x_4380_, v_k_4378_, v_v_4379_);
    return v___x_4381_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4382_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(
    mut v_x_4383_: *mut leanh::LeanObject,
    mut v_x_4384_: usize,
    mut v_x_4385_: usize,
    mut v_x_4386_: *mut leanh::LeanObject,
    mut v_x_4387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: usize = 0;
    let mut v___x_4390_: usize = 0;
    let mut v___x_4391_: usize = 0;
    let mut v___x_4392_: usize = 0;
    let mut v_j_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v_v_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: u8 = 0;
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v_node_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4425_: u8 = 0;
    let mut v___x_4426_: usize = 0;
    let mut v___x_4427_: usize = 0;
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4432_: u8 = 0;
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4434_: u8 = 0;
    let mut v_unused_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4440_: u8 = 0;
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4445_: u8 = 0;
    let mut v_ks_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: usize = 0;
    let mut v___x_4452_: u8 = 0;
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v_reuseFailAlloc_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4383_) == 0 {
                    v_es_4388_ = leanh::lean_ctor_get(v_x_4383_, 0);
                    v___x_4389_ = 5usize;
                    v___x_4390_ = 1usize;
                    v___x_4391_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4392_ = lean_usize_land(v_x_4384_, v___x_4391_);
                    v_j_4393_ = lean_usize_to_nat(v___x_4392_);
                    v___x_4394_ = lean_array_get_size(v_es_4388_);
                    v___x_4395_ = lean_nat_dec_lt(v_j_4393_, v___x_4394_);
                    if v___x_4395_ == 0 {
                        leanh::lean_dec(v_j_4393_);
                        leanh::lean_dec(v_x_4387_);
                        leanh::lean_dec_ref(v_x_4386_);
                        return v_x_4383_;
                    } else {
                        leanh::lean_inc_ref(v_es_4388_);
                        v_isSharedCheck_4434_ = (!leanh::lean_is_exclusive(v_x_4383_)) as u8;
                        if v_isSharedCheck_4434_ == 0 {
                            v_unused_4435_ = leanh::lean_ctor_get(v_x_4383_, 0);
                            leanh::lean_dec(v_unused_4435_);
                            v___x_4397_ = v_x_4383_;
                            v_isShared_4398_ = v_isSharedCheck_4434_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4383_);
                            v___x_4397_ = leanh::lean_box(0);
                            v_isShared_4398_ = v_isSharedCheck_4434_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4436_ = leanh::lean_ctor_get(v_x_4383_, 0);
                    v_vs_4437_ = leanh::lean_ctor_get(v_x_4383_, 1);
                    v_isSharedCheck_4457_ = (!leanh::lean_is_exclusive(v_x_4383_)) as u8;
                    if v_isSharedCheck_4457_ == 0 {
                        v___x_4439_ = v_x_4383_;
                        v_isShared_4440_ = v_isSharedCheck_4457_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4437_);
                        leanh::lean_inc(v_ks_4436_);
                        leanh::lean_dec(v_x_4383_);
                        v___x_4439_ = leanh::lean_box(0);
                        v_isShared_4440_ = v_isSharedCheck_4457_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4399_ = lean_array_fget(v_es_4388_, v_j_4393_);
                v___x_4400_ = leanh::lean_box(0);
                v_xs_x27_4401_ = lean_array_fset(v_es_4388_, v_j_4393_, v___x_4400_);
                match leanh::lean_obj_tag(v_v_4399_) {
                    0 => {
                        v_key_4408_ = leanh::lean_ctor_get(v_v_4399_, 0);
                        v_val_4409_ = leanh::lean_ctor_get(v_v_4399_, 1);
                        v_isSharedCheck_4421_ = (!leanh::lean_is_exclusive(v_v_4399_)) as u8;
                        if v_isSharedCheck_4421_ == 0 {
                            v___x_4411_ = v_v_4399_;
                            v_isShared_4412_ = v_isSharedCheck_4421_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4409_);
                            leanh::lean_inc(v_key_4408_);
                            leanh::lean_dec(v_v_4399_);
                            v___x_4411_ = leanh::lean_box(0);
                            v_isShared_4412_ = v_isSharedCheck_4421_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4422_ = leanh::lean_ctor_get(v_v_4399_, 0);
                        v_isSharedCheck_4432_ = (!leanh::lean_is_exclusive(v_v_4399_)) as u8;
                        if v_isSharedCheck_4432_ == 0 {
                            v___x_4424_ = v_v_4399_;
                            v_isShared_4425_ = v_isSharedCheck_4432_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4422_);
                            leanh::lean_dec(v_v_4399_);
                            v___x_4424_ = leanh::lean_box(0);
                            v_isShared_4425_ = v_isSharedCheck_4432_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4433_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4433_, 0, v_x_4386_);
                        leanh::lean_ctor_set(v___x_4433_, 1, v_x_4387_);
                        v___y_4403_ = v___x_4433_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4404_ = lean_array_fset(v_xs_x27_4401_, v_j_4393_, v___y_4403_);
                leanh::lean_dec(v_j_4393_);
                if v_isShared_4398_ == 0 {
                    leanh::lean_ctor_set(v___x_4397_, 0, v___x_4404_);
                    v___x_4406_ = v___x_4397_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4407_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4404_);
                    v___x_4406_ = v_reuseFailAlloc_4407_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4406_;
            }
            4 => {
                v___x_4413_ = l_Lean_Meta_Grind_Origin_key(v_x_4386_);
                v___x_4414_ = l_Lean_Meta_Grind_Origin_key(v_key_4408_);
                v___x_4415_ = lean_name_eq(v___x_4413_, v___x_4414_);
                leanh::lean_dec(v___x_4414_);
                leanh::lean_dec(v___x_4413_);
                if v___x_4415_ == 0 {
                    leanh::lean_del_object(v___x_4411_);
                    v___x_4416_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4408_,
                        v_val_4409_,
                        v_x_4386_,
                        v_x_4387_,
                    );
                    v___x_4417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4417_, 0, v___x_4416_);
                    v___y_4403_ = v___x_4417_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4409_);
                    leanh::lean_dec(v_key_4408_);
                    if v_isShared_4412_ == 0 {
                        leanh::lean_ctor_set(v___x_4411_, 1, v_x_4387_);
                        leanh::lean_ctor_set(v___x_4411_, 0, v_x_4386_);
                        v___x_4419_ = v___x_4411_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4420_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_x_4386_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_x_4387_);
                        v___x_4419_ = v_reuseFailAlloc_4420_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4403_ = v___x_4419_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4426_ = lean_usize_shift_right(v_x_4384_, v___x_4389_);
                v___x_4427_ = lean_usize_add(v_x_4385_, v___x_4390_);
                v___x_4428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_node_4422_, v___x_4426_, v___x_4427_, v_x_4386_, v_x_4387_);
                if v_isShared_4425_ == 0 {
                    leanh::lean_ctor_set(v___x_4424_, 0, v___x_4428_);
                    v___x_4430_ = v___x_4424_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
                    v___x_4430_ = v_reuseFailAlloc_4431_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4403_ = v___x_4430_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4440_ == 0 {
                    v___x_4442_ = v___x_4439_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_ks_4436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_vs_4437_);
                    v___x_4442_ = v_reuseFailAlloc_4456_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4443_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v___x_4442_, v_x_4386_, v_x_4387_);
                v___x_4451_ = 7usize;
                v___x_4452_ = lean_usize_dec_le(v___x_4451_, v_x_4385_);
                if v___x_4452_ == 0 {
                    v___x_4453_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4443_);
                    v___x_4454_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4455_ = lean_nat_dec_lt(v___x_4453_, v___x_4454_);
                    leanh::lean_dec(v___x_4453_);
                    v___y_4445_ = v___x_4455_;
                    state = 10;
                    continue;
                } else {
                    v___y_4445_ = v___x_4452_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4445_ == 0 {
                    v_ks_4446_ = leanh::lean_ctor_get(v_newNode_4443_, 0);
                    leanh::lean_inc_ref(v_ks_4446_);
                    v_vs_4447_ = leanh::lean_ctor_get(v_newNode_4443_, 1);
                    leanh::lean_inc_ref(v_vs_4447_);
                    leanh::lean_dec_ref(v_newNode_4443_);
                    v___x_4448_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4449_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0);
                    v___x_4450_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_4385_, v_ks_4446_, v_vs_4447_, v___x_4448_, v___x_4449_);
                    leanh::lean_dec_ref(v_vs_4447_);
                    leanh::lean_dec_ref(v_ks_4446_);
                    return v___x_4450_;
                } else {
                    return v_newNode_4443_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(
    mut v_depth_4458_: usize,
    mut v_keys_4459_: *mut leanh::LeanObject,
    mut v_vals_4460_: *mut leanh::LeanObject,
    mut v_i_4461_: *mut leanh::LeanObject,
    mut v_entries_4462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: u8 = 0;
    let mut v_k_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4468_: u64 = 0;
    let mut v_h_4469_: usize = 0;
    let mut v___x_4470_: usize = 0;
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: usize = 0;
    let mut v___x_4473_: usize = 0;
    let mut v___x_4474_: usize = 0;
    let mut v_h_4475_: usize = 0;
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: u64 = 0;
    let mut v_hash_4481_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4463_ = lean_array_get_size(v_keys_4459_);
                v___x_4464_ = lean_nat_dec_lt(v_i_4461_, v___x_4463_);
                if v___x_4464_ == 0 {
                    leanh::lean_dec(v_i_4461_);
                    return v_entries_4462_;
                } else {
                    v_k_4465_ = lean_array_fget_borrowed(v_keys_4459_, v_i_4461_);
                    v_v_4466_ = lean_array_fget_borrowed(v_vals_4460_, v_i_4461_);
                    v___x_4479_ = l_Lean_Meta_Grind_Origin_key(v_k_4465_);
                    if leanh::lean_obj_tag(v___x_4479_) == 0 {
                        v___x_4480_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_4468_ = v___x_4480_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4481_ = leanh::lean_ctor_get_uint64(
                            v___x_4479_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        leanh::lean_dec(v___x_4479_);
                        v___y_4468_ = v_hash_4481_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4469_ = lean_uint64_to_usize(v___y_4468_);
                v___x_4470_ = 5usize;
                v___x_4471_ = leanh::lean_unsigned_to_nat(1);
                v___x_4472_ = 1usize;
                v___x_4473_ = lean_usize_sub(v_depth_4458_, v___x_4472_);
                v___x_4474_ = lean_usize_mul(v___x_4470_, v___x_4473_);
                v_h_4475_ = lean_usize_shift_right(v_h_4469_, v___x_4474_);
                v___x_4476_ = lean_nat_add(v_i_4461_, v___x_4471_);
                leanh::lean_dec(v_i_4461_);
                leanh::lean_inc(v_v_4466_);
                leanh::lean_inc(v_k_4465_);
                v___x_4477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_entries_4462_, v_h_4475_, v_depth_4458_, v_k_4465_, v_v_4466_);
                v_i_4461_ = v___x_4476_;
                v_entries_4462_ = v___x_4477_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_depth_4482_: *mut leanh::LeanObject,
    mut v_keys_4483_: *mut leanh::LeanObject,
    mut v_vals_4484_: *mut leanh::LeanObject,
    mut v_i_4485_: *mut leanh::LeanObject,
    mut v_entries_4486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4487_: usize = 0;
    let mut v_res_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4487_ = leanh::lean_unbox_usize(v_depth_4482_);
    leanh::lean_dec(v_depth_4482_);
    v_res_4488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_4487_, v_keys_4483_, v_vals_4484_, v_i_4485_, v_entries_4486_);
    leanh::lean_dec_ref(v_vals_4484_);
    leanh::lean_dec_ref(v_keys_4483_);
    return v_res_4488_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_4489_: *mut leanh::LeanObject,
    mut v_x_4490_: *mut leanh::LeanObject,
    mut v_x_4491_: *mut leanh::LeanObject,
    mut v_x_4492_: *mut leanh::LeanObject,
    mut v_x_4493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1264__boxed_4494_: usize = 0;
    let mut v_x_1265__boxed_4495_: usize = 0;
    let mut v_res_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1264__boxed_4494_ = leanh::lean_unbox_usize(v_x_4490_);
    leanh::lean_dec(v_x_4490_);
    v_x_1265__boxed_4495_ = leanh::lean_unbox_usize(v_x_4491_);
    leanh::lean_dec(v_x_4491_);
    v_res_4496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_4489_, v_x_1264__boxed_4494_, v_x_1265__boxed_4495_, v_x_4492_, v_x_4493_);
    return v_res_4496_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(
    mut v_x_4497_: *mut leanh::LeanObject,
    mut v_x_4498_: *mut leanh::LeanObject,
    mut v_x_4499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4501_: u64 = 0;
    let mut v___x_4502_: usize = 0;
    let mut v___x_4503_: usize = 0;
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: u64 = 0;
    let mut v_hash_4507_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4505_ = l_Lean_Meta_Grind_Origin_key(v_x_4498_);
                if leanh::lean_obj_tag(v___x_4505_) == 0 {
                    v___x_4506_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4501_ = v___x_4506_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4507_ = leanh::lean_ctor_get_uint64(
                        v___x_4505_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___x_4505_);
                    v___y_4501_ = v_hash_4507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4502_ = lean_uint64_to_usize(v___y_4501_);
                v___x_4503_ = 1usize;
                v___x_4504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_4497_, v___x_4502_, v___x_4503_, v_x_4498_, v_x_4499_);
                return v___x_4504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(
    mut v_keys_4508_: *mut leanh::LeanObject,
    mut v_vals_4509_: *mut leanh::LeanObject,
    mut v_i_4510_: *mut leanh::LeanObject,
    mut v_k_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4512_ = lean_array_get_size(v_keys_4508_);
                v___x_4513_ = lean_nat_dec_lt(v_i_4510_, v___x_4512_);
                if v___x_4513_ == 0 {
                    leanh::lean_dec(v_i_4510_);
                    v___x_4514_ = leanh::lean_box(0);
                    return v___x_4514_;
                } else {
                    v_k_x27_4515_ = lean_array_fget_borrowed(v_keys_4508_, v_i_4510_);
                    v___x_4516_ = l_Lean_Meta_Grind_Origin_key(v_k_4511_);
                    v___x_4517_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_4515_);
                    v___x_4518_ = lean_name_eq(v___x_4516_, v___x_4517_);
                    leanh::lean_dec(v___x_4517_);
                    leanh::lean_dec(v___x_4516_);
                    if v___x_4518_ == 0 {
                        v___x_4519_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4520_ = lean_nat_add(v_i_4510_, v___x_4519_);
                        leanh::lean_dec(v_i_4510_);
                        v_i_4510_ = v___x_4520_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4522_ = lean_array_fget_borrowed(v_vals_4509_, v_i_4510_);
                        leanh::lean_dec(v_i_4510_);
                        leanh::lean_inc(v___x_4522_);
                        v___x_4523_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4523_, 0, v___x_4522_);
                        return v___x_4523_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(
    mut v_keys_4524_: *mut leanh::LeanObject,
    mut v_vals_4525_: *mut leanh::LeanObject,
    mut v_i_4526_: *mut leanh::LeanObject,
    mut v_k_4527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4528_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_4524_, v_vals_4525_, v_i_4526_, v_k_4527_);
    leanh::lean_dec_ref(v_k_4527_);
    leanh::lean_dec_ref(v_vals_4525_);
    leanh::lean_dec_ref(v_keys_4524_);
    return v_res_4528_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(
    mut v_x_4529_: *mut leanh::LeanObject,
    mut v_x_4530_: usize,
    mut v_x_4531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: usize = 0;
    let mut v_j_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: u8 = 0;
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: usize = 0;
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4529_) == 0 {
                    v_es_4532_ = leanh::lean_ctor_get(v_x_4529_, 0);
                    v___x_4533_ = leanh::lean_box(2);
                    v___x_4534_ = 5usize;
                    v___x_4535_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4536_ = lean_usize_land(v_x_4530_, v___x_4535_);
                    v_j_4537_ = lean_usize_to_nat(v___x_4536_);
                    v___x_4538_ = lean_array_get_borrowed(v___x_4533_, v_es_4532_, v_j_4537_);
                    leanh::lean_dec(v_j_4537_);
                    match leanh::lean_obj_tag(v___x_4538_) {
                        0 => {
                            v_key_4539_ = leanh::lean_ctor_get(v___x_4538_, 0);
                            v_val_4540_ = leanh::lean_ctor_get(v___x_4538_, 1);
                            v___x_4541_ = l_Lean_Meta_Grind_Origin_key(v_x_4531_);
                            v___x_4542_ = l_Lean_Meta_Grind_Origin_key(v_key_4539_);
                            v___x_4543_ = lean_name_eq(v___x_4541_, v___x_4542_);
                            leanh::lean_dec(v___x_4542_);
                            leanh::lean_dec(v___x_4541_);
                            if v___x_4543_ == 0 {
                                v___x_4544_ = leanh::lean_box(0);
                                return v___x_4544_;
                            } else {
                                leanh::lean_inc(v_val_4540_);
                                v___x_4545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4545_, 0, v_val_4540_);
                                return v___x_4545_;
                            }
                        }
                        1 => {
                            v_node_4546_ = leanh::lean_ctor_get(v___x_4538_, 0);
                            v___x_4547_ = lean_usize_shift_right(v_x_4530_, v___x_4534_);
                            v_x_4529_ = v_node_4546_;
                            v_x_4530_ = v___x_4547_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4549_ = leanh::lean_box(0);
                            return v___x_4549_;
                        }
                    }
                } else {
                    v_ks_4550_ = leanh::lean_ctor_get(v_x_4529_, 0);
                    v_vs_4551_ = leanh::lean_ctor_get(v_x_4529_, 1);
                    v___x_4552_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4553_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_4550_, v_vs_4551_, v___x_4552_, v_x_4531_);
                    return v___x_4553_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(
    mut v_x_4554_: *mut leanh::LeanObject,
    mut v_x_4555_: *mut leanh::LeanObject,
    mut v_x_4556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1478__boxed_4557_: usize = 0;
    let mut v_res_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1478__boxed_4557_ = leanh::lean_unbox_usize(v_x_4555_);
    leanh::lean_dec(v_x_4555_);
    v_res_4558_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_4554_, v_x_1478__boxed_4557_, v_x_4556_);
    leanh::lean_dec_ref(v_x_4556_);
    leanh::lean_dec_ref(v_x_4554_);
    return v_res_4558_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(
    mut v_x_4559_: *mut leanh::LeanObject,
    mut v_x_4560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4562_: u64 = 0;
    let mut v___x_4563_: usize = 0;
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u64 = 0;
    let mut v_hash_4567_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4565_ = l_Lean_Meta_Grind_Origin_key(v_x_4560_);
                if leanh::lean_obj_tag(v___x_4565_) == 0 {
                    v___x_4566_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4562_ = v___x_4566_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4567_ = leanh::lean_ctor_get_uint64(
                        v___x_4565_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___x_4565_);
                    v___y_4562_ = v_hash_4567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4563_ = lean_uint64_to_usize(v___y_4562_);
                v___x_4564_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_4559_, v___x_4563_, v_x_4560_);
                return v___x_4564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(
    mut v_x_4568_: *mut leanh::LeanObject,
    mut v_x_4569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4570_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_4568_, v_x_4569_);
    leanh::lean_dec_ref(v_x_4569_);
    leanh::lean_dec_ref(v_x_4568_);
    return v_res_4570_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(
    mut v_keys_4571_: *mut leanh::LeanObject,
    mut v_vals_4572_: *mut leanh::LeanObject,
    mut v_i_4573_: *mut leanh::LeanObject,
    mut v_k_4574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4575_ = lean_array_get_size(v_keys_4571_);
                v___x_4576_ = lean_nat_dec_lt(v_i_4573_, v___x_4575_);
                if v___x_4576_ == 0 {
                    leanh::lean_dec(v_i_4573_);
                    v___x_4577_ = leanh::lean_box(0);
                    return v___x_4577_;
                } else {
                    v_k_x27_4578_ = lean_array_fget_borrowed(v_keys_4571_, v_i_4573_);
                    v___x_4579_ = lean_name_eq(v_k_4574_, v_k_x27_4578_);
                    if v___x_4579_ == 0 {
                        v___x_4580_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4581_ = lean_nat_add(v_i_4573_, v___x_4580_);
                        leanh::lean_dec(v_i_4573_);
                        v_i_4573_ = v___x_4581_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4583_ = lean_array_fget_borrowed(v_vals_4572_, v_i_4573_);
                        leanh::lean_dec(v_i_4573_);
                        leanh::lean_inc(v___x_4583_);
                        v___x_4584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4584_, 0, v___x_4583_);
                        return v___x_4584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(
    mut v_keys_4585_: *mut leanh::LeanObject,
    mut v_vals_4586_: *mut leanh::LeanObject,
    mut v_i_4587_: *mut leanh::LeanObject,
    mut v_k_4588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4589_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_4585_, v_vals_4586_, v_i_4587_, v_k_4588_);
    leanh::lean_dec(v_k_4588_);
    leanh::lean_dec_ref(v_vals_4586_);
    leanh::lean_dec_ref(v_keys_4585_);
    return v_res_4589_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(
    mut v_x_4590_: *mut leanh::LeanObject,
    mut v_x_4591_: usize,
    mut v_x_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: usize = 0;
    let mut v___x_4596_: usize = 0;
    let mut v___x_4597_: usize = 0;
    let mut v_j_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: u8 = 0;
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: usize = 0;
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4590_) == 0 {
                    v_es_4593_ = leanh::lean_ctor_get(v_x_4590_, 0);
                    v___x_4594_ = leanh::lean_box(2);
                    v___x_4595_ = 5usize;
                    v___x_4596_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4597_ = lean_usize_land(v_x_4591_, v___x_4596_);
                    v_j_4598_ = lean_usize_to_nat(v___x_4597_);
                    v___x_4599_ = lean_array_get_borrowed(v___x_4594_, v_es_4593_, v_j_4598_);
                    leanh::lean_dec(v_j_4598_);
                    match leanh::lean_obj_tag(v___x_4599_) {
                        0 => {
                            v_key_4600_ = leanh::lean_ctor_get(v___x_4599_, 0);
                            v_val_4601_ = leanh::lean_ctor_get(v___x_4599_, 1);
                            v___x_4602_ = lean_name_eq(v_x_4592_, v_key_4600_);
                            if v___x_4602_ == 0 {
                                v___x_4603_ = leanh::lean_box(0);
                                return v___x_4603_;
                            } else {
                                leanh::lean_inc(v_val_4601_);
                                v___x_4604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4604_, 0, v_val_4601_);
                                return v___x_4604_;
                            }
                        }
                        1 => {
                            v_node_4605_ = leanh::lean_ctor_get(v___x_4599_, 0);
                            v___x_4606_ = lean_usize_shift_right(v_x_4591_, v___x_4595_);
                            v_x_4590_ = v_node_4605_;
                            v_x_4591_ = v___x_4606_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4608_ = leanh::lean_box(0);
                            return v___x_4608_;
                        }
                    }
                } else {
                    v_ks_4609_ = leanh::lean_ctor_get(v_x_4590_, 0);
                    v_vs_4610_ = leanh::lean_ctor_get(v_x_4590_, 1);
                    v___x_4611_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4612_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_4609_, v_vs_4610_, v___x_4611_, v_x_4592_);
                    return v___x_4612_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(
    mut v_x_4613_: *mut leanh::LeanObject,
    mut v_x_4614_: *mut leanh::LeanObject,
    mut v_x_4615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1576__boxed_4616_: usize = 0;
    let mut v_res_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1576__boxed_4616_ = leanh::lean_unbox_usize(v_x_4614_);
    leanh::lean_dec(v_x_4614_);
    v_res_4617_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_4613_, v_x_1576__boxed_4616_, v_x_4615_);
    leanh::lean_dec(v_x_4615_);
    leanh::lean_dec_ref(v_x_4613_);
    return v_res_4617_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(
    mut v_x_4618_: *mut leanh::LeanObject,
    mut v_x_4619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4621_: u64 = 0;
    let mut v___x_4622_: usize = 0;
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: u64 = 0;
    let mut v_hash_4625_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4619_) == 0 {
                    v___x_4624_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4621_ = v___x_4624_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4625_ = leanh::lean_ctor_get_uint64(
                        v_x_4619_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4621_ = v_hash_4625_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4622_ = lean_uint64_to_usize(v___y_4621_);
                v___x_4623_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_4618_, v___x_4622_, v_x_4619_);
                return v___x_4623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(
    mut v_x_4626_: *mut leanh::LeanObject,
    mut v_x_4627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4628_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_4626_, v_x_4627_);
    leanh::lean_dec(v_x_4627_);
    leanh::lean_dec_ref(v_x_4626_);
    return v_res_4628_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l_Lean_Meta_Grind_instInhabitedTheorems_default(leanh::lean_box(0));
    return v___x_4636_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(
    mut v_msg_4637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4638_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0;
    v___f_4639_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1;
    v___f_4640_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2;
    v___f_4641_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3;
    v___f_4642_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4;
    v___f_4643_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5;
    v___f_4644_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6;
    v___x_4645_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4645_, 0, v___f_4638_);
    leanh::lean_ctor_set(v___x_4645_, 1, v___f_4639_);
    v___x_4646_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4646_, 0, v___x_4645_);
    leanh::lean_ctor_set(v___x_4646_, 1, v___f_4640_);
    leanh::lean_ctor_set(v___x_4646_, 2, v___f_4641_);
    leanh::lean_ctor_set(v___x_4646_, 3, v___f_4642_);
    leanh::lean_ctor_set(v___x_4646_, 4, v___f_4643_);
    v___x_4647_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4647_, 0, v___x_4646_);
    leanh::lean_ctor_set(v___x_4647_, 1, v___f_4644_);
    v___x_4648_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once), _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
    v___x_4649_ = l_instInhabitedOfMonad___redArg(v___x_4647_, v___x_4648_);
    v___x_4650_ = lean_panic_fn_borrowed(v___x_4649_, v_msg_4637_);
    leanh::lean_dec(v___x_4649_);
    return v___x_4650_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(
    mut v_xs_4651_: *mut leanh::LeanObject,
    mut v_v_4652_: *mut leanh::LeanObject,
    mut v_i_4653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: u8 = 0;
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4654_ = lean_array_get_size(v_xs_4651_);
                v___x_4655_ = lean_nat_dec_lt(v_i_4653_, v___x_4654_);
                if v___x_4655_ == 0 {
                    leanh::lean_dec(v_i_4653_);
                    v___x_4656_ = leanh::lean_box(0);
                    return v___x_4656_;
                } else {
                    v___x_4657_ = lean_array_fget_borrowed(v_xs_4651_, v_i_4653_);
                    v___x_4658_ = l_Lean_Meta_Grind_Origin_key(v___x_4657_);
                    v___x_4659_ = l_Lean_Meta_Grind_Origin_key(v_v_4652_);
                    v___x_4660_ = lean_name_eq(v___x_4658_, v___x_4659_);
                    leanh::lean_dec(v___x_4659_);
                    leanh::lean_dec(v___x_4658_);
                    if v___x_4660_ == 0 {
                        v___x_4661_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4662_ = lean_nat_add(v_i_4653_, v___x_4661_);
                        leanh::lean_dec(v_i_4653_);
                        v_i_4653_ = v___x_4662_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4664_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4664_, 0, v_i_4653_);
                        return v___x_4664_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(
    mut v_xs_4665_: *mut leanh::LeanObject,
    mut v_v_4666_: *mut leanh::LeanObject,
    mut v_i_4667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_4665_, v_v_4666_, v_i_4667_);
    leanh::lean_dec_ref(v_v_4666_);
    leanh::lean_dec_ref(v_xs_4665_);
    return v_res_4668_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(
    mut v_xs_4669_: *mut leanh::LeanObject,
    mut v_v_4670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4671_ = leanh::lean_unsigned_to_nat(0);
    v___x_4672_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_4669_, v_v_4670_, v___x_4671_);
    return v___x_4672_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(
    mut v_xs_4673_: *mut leanh::LeanObject,
    mut v_v_4674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4675_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_4673_, v_v_4674_);
    leanh::lean_dec_ref(v_v_4674_);
    leanh::lean_dec_ref(v_xs_4673_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(
    mut v_x_4676_: *mut leanh::LeanObject,
    mut v_x_4677_: usize,
    mut v_x_4678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: usize = 0;
    let mut v___x_4682_: usize = 0;
    let mut v___x_4683_: usize = 0;
    let mut v_j_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: u8 = 0;
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4692_: u8 = 0;
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v_unused_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v_node_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4705_: u8 = 0;
    let mut v_entries_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: usize = 0;
    let mut v_newNode_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4722_: u8 = 0;
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4730_: u8 = 0;
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut v_unused_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4676_) == 0 {
                    v_es_4679_ = leanh::lean_ctor_get(v_x_4676_, 0);
                    v___x_4680_ = leanh::lean_box(2);
                    v___x_4681_ = 5usize;
                    v___x_4682_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4683_ = lean_usize_land(v_x_4677_, v___x_4682_);
                    v_j_4684_ = lean_usize_to_nat(v___x_4683_);
                    v_entry_4685_ = lean_array_get(v___x_4680_, v_es_4679_, v_j_4684_);
                    match leanh::lean_obj_tag(v_entry_4685_) {
                        0 => {
                            v_key_4686_ = leanh::lean_ctor_get(v_entry_4685_, 0);
                            leanh::lean_inc(v_key_4686_);
                            leanh::lean_dec_ref_known(v_entry_4685_, 2);
                            v___x_4687_ = l_Lean_Meta_Grind_Origin_key(v_x_4678_);
                            v___x_4688_ = l_Lean_Meta_Grind_Origin_key(v_key_4686_);
                            leanh::lean_dec(v_key_4686_);
                            v___x_4689_ = lean_name_eq(v___x_4687_, v___x_4688_);
                            leanh::lean_dec(v___x_4688_);
                            leanh::lean_dec(v___x_4687_);
                            if v___x_4689_ == 0 {
                                leanh::lean_dec(v_j_4684_);
                                return v_x_4676_;
                            } else {
                                leanh::lean_inc_ref(v_es_4679_);
                                v_isSharedCheck_4697_ =
                                    (!leanh::lean_is_exclusive(v_x_4676_)) as u8;
                                if v_isSharedCheck_4697_ == 0 {
                                    v_unused_4698_ = leanh::lean_ctor_get(v_x_4676_, 0);
                                    leanh::lean_dec(v_unused_4698_);
                                    v___x_4691_ = v_x_4676_;
                                    v_isShared_4692_ = v_isSharedCheck_4697_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_4676_);
                                    v___x_4691_ = leanh::lean_box(0);
                                    v_isShared_4692_ = v_isSharedCheck_4697_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            leanh::lean_inc_ref(v_es_4679_);
                            v_isSharedCheck_4732_ =
                                (!leanh::lean_is_exclusive(v_x_4676_)) as u8;
                            if v_isSharedCheck_4732_ == 0 {
                                v_unused_4733_ = leanh::lean_ctor_get(v_x_4676_, 0);
                                leanh::lean_dec(v_unused_4733_);
                                v___x_4700_ = v_x_4676_;
                                v_isShared_4701_ = v_isSharedCheck_4732_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_4676_);
                                v___x_4700_ = leanh::lean_box(0);
                                v_isShared_4701_ = v_isSharedCheck_4732_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_j_4684_);
                            return v_x_4676_;
                        }
                    }
                } else {
                    v_ks_4734_ = leanh::lean_ctor_get(v_x_4676_, 0);
                    v_vs_4735_ = leanh::lean_ctor_get(v_x_4676_, 1);
                    v_isSharedCheck_4749_ = (!leanh::lean_is_exclusive(v_x_4676_)) as u8;
                    if v_isSharedCheck_4749_ == 0 {
                        v___x_4737_ = v_x_4676_;
                        v_isShared_4738_ = v_isSharedCheck_4749_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4735_);
                        leanh::lean_inc(v_ks_4734_);
                        leanh::lean_dec(v_x_4676_);
                        v___x_4737_ = leanh::lean_box(0);
                        v_isShared_4738_ = v_isSharedCheck_4749_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4693_ = lean_array_set(v_es_4679_, v_j_4684_, v___x_4680_);
                leanh::lean_dec(v_j_4684_);
                if v_isShared_4692_ == 0 {
                    leanh::lean_ctor_set(v___x_4691_, 0, v___x_4693_);
                    v___x_4695_ = v___x_4691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
                    v___x_4695_ = v_reuseFailAlloc_4696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4695_;
            }
            3 => {
                v_node_4702_ = leanh::lean_ctor_get(v_entry_4685_, 0);
                v_isSharedCheck_4731_ = (!leanh::lean_is_exclusive(v_entry_4685_)) as u8;
                if v_isSharedCheck_4731_ == 0 {
                    v___x_4704_ = v_entry_4685_;
                    v_isShared_4705_ = v_isSharedCheck_4731_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_node_4702_);
                    leanh::lean_dec(v_entry_4685_);
                    v___x_4704_ = leanh::lean_box(0);
                    v_isShared_4705_ = v_isSharedCheck_4731_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_4706_ = lean_array_set(v_es_4679_, v_j_4684_, v___x_4680_);
                v___x_4707_ = lean_usize_shift_right(v_x_4677_, v___x_4681_);
                v_newNode_4708_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_4702_, v___x_4707_, v_x_4678_);
                leanh::lean_inc_ref(v_newNode_4708_);
                v___x_4709_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_4708_);
                if leanh::lean_obj_tag(v___x_4709_) == 0 {
                    if v_isShared_4705_ == 0 {
                        leanh::lean_ctor_set(v___x_4704_, 0, v_newNode_4708_);
                        v___x_4711_ = v___x_4704_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_newNode_4708_);
                        v___x_4711_ = v_reuseFailAlloc_4716_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_newNode_4708_);
                    leanh::lean_del_object(v___x_4704_);
                    v_val_4717_ = leanh::lean_ctor_get(v___x_4709_, 0);
                    leanh::lean_inc(v_val_4717_);
                    leanh::lean_dec_ref_known(v___x_4709_, 1);
                    v_fst_4718_ = leanh::lean_ctor_get(v_val_4717_, 0);
                    v_snd_4719_ = leanh::lean_ctor_get(v_val_4717_, 1);
                    v_isSharedCheck_4730_ = (!leanh::lean_is_exclusive(v_val_4717_)) as u8;
                    if v_isSharedCheck_4730_ == 0 {
                        v___x_4721_ = v_val_4717_;
                        v_isShared_4722_ = v_isSharedCheck_4730_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4719_);
                        leanh::lean_inc(v_fst_4718_);
                        leanh::lean_dec(v_val_4717_);
                        v___x_4721_ = leanh::lean_box(0);
                        v_isShared_4722_ = v_isSharedCheck_4730_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4712_ = lean_array_set(v_entries_4706_, v_j_4684_, v___x_4711_);
                leanh::lean_dec(v_j_4684_);
                if v_isShared_4701_ == 0 {
                    leanh::lean_ctor_set(v___x_4700_, 0, v___x_4712_);
                    v___x_4714_ = v___x_4700_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4712_);
                    v___x_4714_ = v_reuseFailAlloc_4715_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4714_;
            }
            7 => {
                if v_isShared_4722_ == 0 {
                    v___x_4724_ = v___x_4721_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4729_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_fst_4718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_snd_4719_);
                    v___x_4724_ = v_reuseFailAlloc_4729_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4725_ = lean_array_set(v_entries_4706_, v_j_4684_, v___x_4724_);
                leanh::lean_dec(v_j_4684_);
                if v_isShared_4701_ == 0 {
                    leanh::lean_ctor_set(v___x_4700_, 0, v___x_4725_);
                    v___x_4727_ = v___x_4700_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4725_);
                    v___x_4727_ = v_reuseFailAlloc_4728_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4727_;
            }
            10 => {
                v___x_4739_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_ks_4734_, v_x_4678_);
                if leanh::lean_obj_tag(v___x_4739_) == 0 {
                    if v_isShared_4738_ == 0 {
                        v___x_4741_ = v___x_4737_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4742_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_ks_4734_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_vs_4735_);
                        v___x_4741_ = v_reuseFailAlloc_4742_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_4743_ = leanh::lean_ctor_get(v___x_4739_, 0);
                    leanh::lean_inc_n(v_val_4743_, 2);
                    leanh::lean_dec_ref_known(v___x_4739_, 1);
                    v_keys_x27_4744_ = l_Array_eraseIdx___redArg(v_ks_4734_, v_val_4743_);
                    v_vals_x27_4745_ = l_Array_eraseIdx___redArg(v_vs_4735_, v_val_4743_);
                    if v_isShared_4738_ == 0 {
                        leanh::lean_ctor_set(v___x_4737_, 1, v_vals_x27_4745_);
                        leanh::lean_ctor_set(v___x_4737_, 0, v_keys_x27_4744_);
                        v___x_4747_ = v___x_4737_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4748_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_keys_x27_4744_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_vals_x27_4745_);
                        v___x_4747_ = v_reuseFailAlloc_4748_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_4741_;
            }
            12 => {
                return v___x_4747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_x_4750_: *mut leanh::LeanObject,
    mut v_x_4751_: *mut leanh::LeanObject,
    mut v_x_4752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1726__boxed_4753_: usize = 0;
    let mut v_res_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1726__boxed_4753_ = leanh::lean_unbox_usize(v_x_4751_);
    leanh::lean_dec(v_x_4751_);
    v_res_4754_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_4750_, v_x_1726__boxed_4753_, v_x_4752_);
    leanh::lean_dec_ref(v_x_4752_);
    return v_res_4754_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(
    mut v_x_4755_: *mut leanh::LeanObject,
    mut v_x_4756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4758_: u64 = 0;
    let mut v_h_4759_: usize = 0;
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u64 = 0;
    let mut v_hash_4763_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4761_ = l_Lean_Meta_Grind_Origin_key(v_x_4756_);
                if leanh::lean_obj_tag(v___x_4761_) == 0 {
                    v___x_4762_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4758_ = v___x_4762_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4763_ = leanh::lean_ctor_get_uint64(
                        v___x_4761_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___x_4761_);
                    v___y_4758_ = v_hash_4763_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_h_4759_ = lean_uint64_to_usize(v___y_4758_);
                v___x_4760_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_4755_, v_h_4759_, v_x_4756_);
                return v___x_4760_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(
    mut v_x_4764_: *mut leanh::LeanObject,
    mut v_x_4765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4766_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_4764_, v_x_4765_);
    leanh::lean_dec_ref(v_x_4765_);
    return v_res_4766_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4770_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2;
    v___x_4771_ = leanh::lean_unsigned_to_nat(6);
    v___x_4772_ = leanh::lean_unsigned_to_nat(82);
    v___x_4773_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1;
    v___x_4774_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0;
    v___x_4775_ = l_mkPanicMessageWithDecl(
        v___x_4774_,
        v___x_4773_,
        v___x_4772_,
        v___x_4771_,
        v___x_4770_,
    );
    return v___x_4775_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(
    mut v_s_4776_: *mut leanh::LeanObject,
    mut v_thm_4777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_symbols_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minIndexable_4789_: u8 = 0;
    let mut v_cnstrs_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4793_: u8 = 0;
    let mut v_tail_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4797_: u8 = 0;
    let mut v_constName_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_smap_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_omap_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v_thm_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut v_unused_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4841_: u8 = 0;
    let mut v_unused_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_symbols_4781_ = leanh::lean_ctor_get(v_thm_4777_, 4);
                leanh::lean_inc(v_symbols_4781_);
                if leanh::lean_obj_tag(v_symbols_4781_) == 1 {
                    v_head_4782_ = leanh::lean_ctor_get(v_symbols_4781_, 0);
                    leanh::lean_inc(v_head_4782_);
                    if leanh::lean_obj_tag(v_head_4782_) == 2 {
                        v_levelParams_4783_ = leanh::lean_ctor_get(v_thm_4777_, 0);
                        v_proof_4784_ = leanh::lean_ctor_get(v_thm_4777_, 1);
                        v_numParams_4785_ = leanh::lean_ctor_get(v_thm_4777_, 2);
                        v_patterns_4786_ = leanh::lean_ctor_get(v_thm_4777_, 3);
                        v_origin_4787_ = leanh::lean_ctor_get(v_thm_4777_, 5);
                        v_kind_4788_ = leanh::lean_ctor_get(v_thm_4777_, 6);
                        v_minIndexable_4789_ = leanh::lean_ctor_get_uint8(
                            v_thm_4777_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                        );
                        v_cnstrs_4790_ = leanh::lean_ctor_get(v_thm_4777_, 7);
                        v_isSharedCheck_4841_ =
                            (!leanh::lean_is_exclusive(v_thm_4777_)) as u8;
                        if v_isSharedCheck_4841_ == 0 {
                            v_unused_4842_ = leanh::lean_ctor_get(v_thm_4777_, 4);
                            leanh::lean_dec(v_unused_4842_);
                            v___x_4792_ = v_thm_4777_;
                            v_isShared_4793_ = v_isSharedCheck_4841_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_cnstrs_4790_);
                            leanh::lean_inc(v_kind_4788_);
                            leanh::lean_inc(v_origin_4787_);
                            leanh::lean_inc(v_patterns_4786_);
                            leanh::lean_inc(v_numParams_4785_);
                            leanh::lean_inc(v_proof_4784_);
                            leanh::lean_inc(v_levelParams_4783_);
                            leanh::lean_dec(v_thm_4777_);
                            v___x_4792_ = leanh::lean_box(0);
                            v_isShared_4793_ = v_isSharedCheck_4841_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_head_4782_);
                        leanh::lean_dec_ref_known(v_symbols_4781_, 2);
                        leanh::lean_dec_ref(v_thm_4777_);
                        leanh::lean_dec_ref(v_s_4776_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_symbols_4781_);
                    leanh::lean_dec_ref(v_thm_4777_);
                    leanh::lean_dec_ref(v_s_4776_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4779_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once), _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
                v___x_4780_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_4779_);
                return v___x_4780_;
            }
            2 => {
                v_tail_4794_ = leanh::lean_ctor_get(v_symbols_4781_, 1);
                v_isSharedCheck_4839_ = (!leanh::lean_is_exclusive(v_symbols_4781_)) as u8;
                if v_isSharedCheck_4839_ == 0 {
                    v_unused_4840_ = leanh::lean_ctor_get(v_symbols_4781_, 0);
                    leanh::lean_dec(v_unused_4840_);
                    v___x_4796_ = v_symbols_4781_;
                    v_isShared_4797_ = v_isSharedCheck_4839_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_tail_4794_);
                    leanh::lean_dec(v_symbols_4781_);
                    v___x_4796_ = leanh::lean_box(0);
                    v_isShared_4797_ = v_isSharedCheck_4839_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_constName_4798_ = leanh::lean_ctor_get(v_head_4782_, 0);
                leanh::lean_inc(v_constName_4798_);
                leanh::lean_dec_ref_known(v_head_4782_, 1);
                v_smap_4799_ = leanh::lean_ctor_get(v_s_4776_, 0);
                v_origins_4800_ = leanh::lean_ctor_get(v_s_4776_, 1);
                v_erased_4801_ = leanh::lean_ctor_get(v_s_4776_, 2);
                v_omap_4802_ = leanh::lean_ctor_get(v_s_4776_, 3);
                v_isSharedCheck_4838_ = (!leanh::lean_is_exclusive(v_s_4776_)) as u8;
                if v_isSharedCheck_4838_ == 0 {
                    v___x_4804_ = v_s_4776_;
                    v_isShared_4805_ = v_isSharedCheck_4838_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_omap_4802_);
                    leanh::lean_inc(v_erased_4801_);
                    leanh::lean_inc(v_origins_4800_);
                    leanh::lean_inc(v_smap_4799_);
                    leanh::lean_dec(v_s_4776_);
                    v___x_4804_ = leanh::lean_box(0);
                    v_isShared_4805_ = v_isSharedCheck_4838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v_origin_4787_);
                if v_isShared_4793_ == 0 {
                    leanh::lean_ctor_set(v___x_4792_, 4, v_tail_4794_);
                    v_thm_4807_ = v___x_4792_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = leanh::lean_alloc_ctor(0, 8, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_levelParams_4783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_proof_4784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 2, v_numParams_4785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 3, v_patterns_4786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 4, v_tail_4794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 5, v_origin_4787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 6, v_kind_4788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 7, v_cnstrs_4790_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4837_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                        v_minIndexable_4789_,
                    );
                    v_thm_4807_ = v_reuseFailAlloc_4837_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4808_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_origin_4787_);
                v_origins_4809_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_4800_, v_origin_4787_, v___x_4808_);
                v_erased_4810_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_4801_, v_origin_4787_);
                v___x_4830_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_4799_, v_constName_4798_);
                if leanh::lean_obj_tag(v___x_4830_) == 1 {
                    v_val_4831_ = leanh::lean_ctor_get(v___x_4830_, 0);
                    leanh::lean_inc(v_val_4831_);
                    leanh::lean_dec_ref_known(v___x_4830_, 1);
                    leanh::lean_inc_ref(v_thm_4807_);
                    v___x_4832_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4832_, 0, v_thm_4807_);
                    leanh::lean_ctor_set(v___x_4832_, 1, v_val_4831_);
                    v___x_4833_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4799_, v_constName_4798_, v___x_4832_);
                    v___y_4812_ = v___x_4833_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4830_);
                    v___x_4834_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_thm_4807_);
                    v___x_4835_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4835_, 0, v_thm_4807_);
                    leanh::lean_ctor_set(v___x_4835_, 1, v___x_4834_);
                    v___x_4836_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4799_, v_constName_4798_, v___x_4835_);
                    v___y_4812_ = v___x_4836_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4813_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_4802_, v_origin_4787_);
                if leanh::lean_obj_tag(v___x_4813_) == 1 {
                    v_val_4814_ = leanh::lean_ctor_get(v___x_4813_, 0);
                    leanh::lean_inc(v_val_4814_);
                    leanh::lean_dec_ref_known(v___x_4813_, 1);
                    if v_isShared_4797_ == 0 {
                        leanh::lean_ctor_set(v___x_4796_, 1, v_val_4814_);
                        leanh::lean_ctor_set(v___x_4796_, 0, v_thm_4807_);
                        v___x_4816_ = v___x_4796_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4821_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_thm_4807_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 1, v_val_4814_);
                        v___x_4816_ = v_reuseFailAlloc_4821_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4813_);
                    v___x_4822_ = leanh::lean_box(0);
                    if v_isShared_4797_ == 0 {
                        leanh::lean_ctor_set(v___x_4796_, 1, v___x_4822_);
                        leanh::lean_ctor_set(v___x_4796_, 0, v_thm_4807_);
                        v___x_4824_ = v___x_4796_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4829_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_thm_4807_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4829_, 1, v___x_4822_);
                        v___x_4824_ = v_reuseFailAlloc_4829_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4817_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_4802_, v_origin_4787_, v___x_4816_);
                if v_isShared_4805_ == 0 {
                    leanh::lean_ctor_set(v___x_4804_, 3, v___x_4817_);
                    leanh::lean_ctor_set(v___x_4804_, 2, v_erased_4810_);
                    leanh::lean_ctor_set(v___x_4804_, 1, v_origins_4809_);
                    leanh::lean_ctor_set(v___x_4804_, 0, v___y_4812_);
                    v___x_4819_ = v___x_4804_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4820_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___y_4812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_origins_4809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_erased_4810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 3, v___x_4817_);
                    v___x_4819_ = v_reuseFailAlloc_4820_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4819_;
            }
            9 => {
                v___x_4825_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_4802_, v_origin_4787_, v___x_4824_);
                if v_isShared_4805_ == 0 {
                    leanh::lean_ctor_set(v___x_4804_, 3, v___x_4825_);
                    leanh::lean_ctor_set(v___x_4804_, 2, v_erased_4810_);
                    leanh::lean_ctor_set(v___x_4804_, 1, v_origins_4809_);
                    leanh::lean_ctor_set(v___x_4804_, 0, v___y_4812_);
                    v___x_4827_ = v___x_4804_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4828_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___y_4812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 1, v_origins_4809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 2, v_erased_4810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 3, v___x_4825_);
                    v___x_4827_ = v_reuseFailAlloc_4828_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(
    mut v_msg_4843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4844_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0;
    v___f_4845_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1;
    v___f_4846_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2;
    v___f_4847_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3;
    v___f_4848_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4;
    v___f_4849_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5;
    v___f_4850_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6;
    v___x_4851_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4851_, 0, v___f_4844_);
    leanh::lean_ctor_set(v___x_4851_, 1, v___f_4845_);
    v___x_4852_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4852_, 0, v___x_4851_);
    leanh::lean_ctor_set(v___x_4852_, 1, v___f_4846_);
    leanh::lean_ctor_set(v___x_4852_, 2, v___f_4847_);
    leanh::lean_ctor_set(v___x_4852_, 3, v___f_4848_);
    leanh::lean_ctor_set(v___x_4852_, 4, v___f_4849_);
    v___x_4853_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4853_, 0, v___x_4852_);
    leanh::lean_ctor_set(v___x_4853_, 1, v___f_4850_);
    v___x_4854_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once), _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
    v___x_4855_ = l_instInhabitedOfMonad___redArg(v___x_4853_, v___x_4854_);
    v___x_4856_ = lean_panic_fn_borrowed(v___x_4855_, v_msg_4843_);
    leanh::lean_dec(v___x_4855_);
    return v___x_4856_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(
    mut v_s_4857_: *mut leanh::LeanObject,
    mut v_thm_4858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_symbols_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v_tail_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4873_: u8 = 0;
    let mut v_constName_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_smap_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_omap_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v_thm_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v_unused_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4917_: u8 = 0;
    let mut v_unused_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_symbols_4862_ = leanh::lean_ctor_get(v_thm_4858_, 2);
                leanh::lean_inc(v_symbols_4862_);
                if leanh::lean_obj_tag(v_symbols_4862_) == 1 {
                    v_head_4863_ = leanh::lean_ctor_get(v_symbols_4862_, 0);
                    leanh::lean_inc(v_head_4863_);
                    if leanh::lean_obj_tag(v_head_4863_) == 2 {
                        v_levelParams_4864_ = leanh::lean_ctor_get(v_thm_4858_, 0);
                        v_proof_4865_ = leanh::lean_ctor_get(v_thm_4858_, 1);
                        v_origin_4866_ = leanh::lean_ctor_get(v_thm_4858_, 3);
                        v_isSharedCheck_4917_ =
                            (!leanh::lean_is_exclusive(v_thm_4858_)) as u8;
                        if v_isSharedCheck_4917_ == 0 {
                            v_unused_4918_ = leanh::lean_ctor_get(v_thm_4858_, 2);
                            leanh::lean_dec(v_unused_4918_);
                            v___x_4868_ = v_thm_4858_;
                            v_isShared_4869_ = v_isSharedCheck_4917_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_origin_4866_);
                            leanh::lean_inc(v_proof_4865_);
                            leanh::lean_inc(v_levelParams_4864_);
                            leanh::lean_dec(v_thm_4858_);
                            v___x_4868_ = leanh::lean_box(0);
                            v_isShared_4869_ = v_isSharedCheck_4917_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_symbols_4862_, 2);
                        leanh::lean_dec(v_head_4863_);
                        leanh::lean_dec_ref(v_thm_4858_);
                        leanh::lean_dec_ref(v_s_4857_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_symbols_4862_);
                    leanh::lean_dec_ref(v_thm_4858_);
                    leanh::lean_dec_ref(v_s_4857_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once), _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
                v___x_4861_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_4860_);
                return v___x_4861_;
            }
            2 => {
                v_tail_4870_ = leanh::lean_ctor_get(v_symbols_4862_, 1);
                v_isSharedCheck_4915_ = (!leanh::lean_is_exclusive(v_symbols_4862_)) as u8;
                if v_isSharedCheck_4915_ == 0 {
                    v_unused_4916_ = leanh::lean_ctor_get(v_symbols_4862_, 0);
                    leanh::lean_dec(v_unused_4916_);
                    v___x_4872_ = v_symbols_4862_;
                    v_isShared_4873_ = v_isSharedCheck_4915_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_tail_4870_);
                    leanh::lean_dec(v_symbols_4862_);
                    v___x_4872_ = leanh::lean_box(0);
                    v_isShared_4873_ = v_isSharedCheck_4915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_constName_4874_ = leanh::lean_ctor_get(v_head_4863_, 0);
                leanh::lean_inc(v_constName_4874_);
                leanh::lean_dec_ref_known(v_head_4863_, 1);
                v_smap_4875_ = leanh::lean_ctor_get(v_s_4857_, 0);
                v_origins_4876_ = leanh::lean_ctor_get(v_s_4857_, 1);
                v_erased_4877_ = leanh::lean_ctor_get(v_s_4857_, 2);
                v_omap_4878_ = leanh::lean_ctor_get(v_s_4857_, 3);
                v_isSharedCheck_4914_ = (!leanh::lean_is_exclusive(v_s_4857_)) as u8;
                if v_isSharedCheck_4914_ == 0 {
                    v___x_4880_ = v_s_4857_;
                    v_isShared_4881_ = v_isSharedCheck_4914_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_omap_4878_);
                    leanh::lean_inc(v_erased_4877_);
                    leanh::lean_inc(v_origins_4876_);
                    leanh::lean_inc(v_smap_4875_);
                    leanh::lean_dec(v_s_4857_);
                    v___x_4880_ = leanh::lean_box(0);
                    v_isShared_4881_ = v_isSharedCheck_4914_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v_origin_4866_);
                if v_isShared_4869_ == 0 {
                    leanh::lean_ctor_set(v___x_4868_, 2, v_tail_4870_);
                    v_thm_4883_ = v___x_4868_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4913_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_levelParams_4864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_proof_4865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 2, v_tail_4870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 3, v_origin_4866_);
                    v_thm_4883_ = v_reuseFailAlloc_4913_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4884_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_origin_4866_);
                v_origins_4885_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_4876_, v_origin_4866_, v___x_4884_);
                v_erased_4886_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_4877_, v_origin_4866_);
                v___x_4906_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_4875_, v_constName_4874_);
                if leanh::lean_obj_tag(v___x_4906_) == 1 {
                    v_val_4907_ = leanh::lean_ctor_get(v___x_4906_, 0);
                    leanh::lean_inc(v_val_4907_);
                    leanh::lean_dec_ref_known(v___x_4906_, 1);
                    leanh::lean_inc_ref(v_thm_4883_);
                    v___x_4908_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4908_, 0, v_thm_4883_);
                    leanh::lean_ctor_set(v___x_4908_, 1, v_val_4907_);
                    v___x_4909_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4875_, v_constName_4874_, v___x_4908_);
                    v___y_4888_ = v___x_4909_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4906_);
                    v___x_4910_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_thm_4883_);
                    v___x_4911_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4911_, 0, v_thm_4883_);
                    leanh::lean_ctor_set(v___x_4911_, 1, v___x_4910_);
                    v___x_4912_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4875_, v_constName_4874_, v___x_4911_);
                    v___y_4888_ = v___x_4912_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4889_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_4878_, v_origin_4866_);
                if leanh::lean_obj_tag(v___x_4889_) == 1 {
                    v_val_4890_ = leanh::lean_ctor_get(v___x_4889_, 0);
                    leanh::lean_inc(v_val_4890_);
                    leanh::lean_dec_ref_known(v___x_4889_, 1);
                    if v_isShared_4873_ == 0 {
                        leanh::lean_ctor_set(v___x_4872_, 1, v_val_4890_);
                        leanh::lean_ctor_set(v___x_4872_, 0, v_thm_4883_);
                        v___x_4892_ = v___x_4872_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4897_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_thm_4883_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4897_, 1, v_val_4890_);
                        v___x_4892_ = v_reuseFailAlloc_4897_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4889_);
                    v___x_4898_ = leanh::lean_box(0);
                    if v_isShared_4873_ == 0 {
                        leanh::lean_ctor_set(v___x_4872_, 1, v___x_4898_);
                        leanh::lean_ctor_set(v___x_4872_, 0, v_thm_4883_);
                        v___x_4900_ = v___x_4872_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4905_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_thm_4883_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4905_, 1, v___x_4898_);
                        v___x_4900_ = v_reuseFailAlloc_4905_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4893_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_4878_, v_origin_4866_, v___x_4892_);
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 3, v___x_4893_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v_erased_4886_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v_origins_4885_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___y_4888_);
                    v___x_4895_ = v___x_4880_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4896_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___y_4888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_origins_4885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_erased_4886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 3, v___x_4893_);
                    v___x_4895_ = v_reuseFailAlloc_4896_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4895_;
            }
            9 => {
                v___x_4901_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_4878_, v_origin_4866_, v___x_4900_);
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 3, v___x_4901_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v_erased_4886_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v_origins_4885_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___y_4888_);
                    v___x_4903_ = v___x_4880_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4904_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___y_4888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_origins_4885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 2, v_erased_4886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 3, v___x_4901_);
                    v___x_4903_ = v_reuseFailAlloc_4904_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_ExtensionState_addEntry(
    mut v_s_4919_: *mut leanh::LeanObject,
    mut v_e_4920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funCC_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4929_: u8 = 0;
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4935_: u8 = 0;
    let mut v_declName_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funCC_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_declName_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eager_4951_: u8 = 0;
    let mut v_casesTypes_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funCC_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_thm_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funCC_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4974_: u8 = 0;
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4979_: u8 = 0;
    let mut v_thm_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funCC_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_4920_) {
                0 => {
                    v_declName_4921_ = leanh::lean_ctor_get(v_e_4920_, 0);
                    leanh::lean_inc(v_declName_4921_);
                    leanh::lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4922_ = leanh::lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4923_ = leanh::lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4924_ = leanh::lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4925_ = leanh::lean_ctor_get(v_s_4919_, 3);
                    v_inj_4926_ = leanh::lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4935_ = (!leanh::lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4935_ == 0 {
                        v___x_4928_ = v_s_4919_;
                        v_isShared_4929_ = v_isSharedCheck_4935_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_inj_4926_);
                        leanh::lean_inc(v_ematch_4925_);
                        leanh::lean_inc(v_funCC_4924_);
                        leanh::lean_inc(v_extThms_4923_);
                        leanh::lean_inc(v_casesTypes_4922_);
                        leanh::lean_dec(v_s_4919_);
                        v___x_4928_ = leanh::lean_box(0);
                        v_isShared_4929_ = v_isSharedCheck_4935_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_declName_4936_ = leanh::lean_ctor_get(v_e_4920_, 0);
                    leanh::lean_inc(v_declName_4936_);
                    leanh::lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4937_ = leanh::lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4938_ = leanh::lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4939_ = leanh::lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4940_ = leanh::lean_ctor_get(v_s_4919_, 3);
                    v_inj_4941_ = leanh::lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4949_ = (!leanh::lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4943_ = v_s_4919_;
                        v_isShared_4944_ = v_isSharedCheck_4949_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_inj_4941_);
                        leanh::lean_inc(v_ematch_4940_);
                        leanh::lean_inc(v_funCC_4939_);
                        leanh::lean_inc(v_extThms_4938_);
                        leanh::lean_inc(v_casesTypes_4937_);
                        leanh::lean_dec(v_s_4919_);
                        v___x_4943_ = leanh::lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4949_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_declName_4950_ = leanh::lean_ctor_get(v_e_4920_, 0);
                    leanh::lean_inc(v_declName_4950_);
                    v_eager_4951_ = leanh::lean_ctor_get_uint8(
                        v_e_4920_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4952_ = leanh::lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4953_ = leanh::lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4954_ = leanh::lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4955_ = leanh::lean_ctor_get(v_s_4919_, 3);
                    v_inj_4956_ = leanh::lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4965_ = (!leanh::lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4965_ == 0 {
                        v___x_4958_ = v_s_4919_;
                        v_isShared_4959_ = v_isSharedCheck_4965_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_inj_4956_);
                        leanh::lean_inc(v_ematch_4955_);
                        leanh::lean_inc(v_funCC_4954_);
                        leanh::lean_inc(v_extThms_4953_);
                        leanh::lean_inc(v_casesTypes_4952_);
                        leanh::lean_dec(v_s_4919_);
                        v___x_4958_ = leanh::lean_box(0);
                        v_isShared_4959_ = v_isSharedCheck_4965_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_thm_4966_ = leanh::lean_ctor_get(v_e_4920_, 0);
                    leanh::lean_inc_ref(v_thm_4966_);
                    leanh::lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4967_ = leanh::lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4968_ = leanh::lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4969_ = leanh::lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4970_ = leanh::lean_ctor_get(v_s_4919_, 3);
                    v_inj_4971_ = leanh::lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4979_ = (!leanh::lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4979_ == 0 {
                        v___x_4973_ = v_s_4919_;
                        v_isShared_4974_ = v_isSharedCheck_4979_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_inj_4971_);
                        leanh::lean_inc(v_ematch_4970_);
                        leanh::lean_inc(v_funCC_4969_);
                        leanh::lean_inc(v_extThms_4968_);
                        leanh::lean_inc(v_casesTypes_4967_);
                        leanh::lean_dec(v_s_4919_);
                        v___x_4973_ = leanh::lean_box(0);
                        v_isShared_4974_ = v_isSharedCheck_4979_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    v_thm_4980_ = leanh::lean_ctor_get(v_e_4920_, 0);
                    leanh::lean_inc_ref(v_thm_4980_);
                    leanh::lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4981_ = leanh::lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4982_ = leanh::lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4983_ = leanh::lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4984_ = leanh::lean_ctor_get(v_s_4919_, 3);
                    v_inj_4985_ = leanh::lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4993_ = (!leanh::lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4993_ == 0 {
                        v___x_4987_ = v_s_4919_;
                        v_isShared_4988_ = v_isSharedCheck_4993_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_inj_4985_);
                        leanh::lean_inc(v_ematch_4984_);
                        leanh::lean_inc(v_funCC_4983_);
                        leanh::lean_inc(v_extThms_4982_);
                        leanh::lean_inc(v_casesTypes_4981_);
                        leanh::lean_dec(v_s_4919_);
                        v___x_4987_ = leanh::lean_box(0);
                        v_isShared_4988_ = v_isSharedCheck_4993_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4930_ = leanh::lean_box(0);
                v___x_4931_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_4923_, v_declName_4921_, v___x_4930_);
                if v_isShared_4929_ == 0 {
                    leanh::lean_ctor_set(v___x_4928_, 1, v___x_4931_);
                    v___x_4933_ = v___x_4928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4934_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_casesTypes_4922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___x_4931_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_funCC_4924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_ematch_4925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 4, v_inj_4926_);
                    v___x_4933_ = v_reuseFailAlloc_4934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4933_;
            }
            3 => {
                v___x_4945_ = l_Lean_NameSet_insert(v_funCC_4939_, v_declName_4936_);
                if v_isShared_4944_ == 0 {
                    leanh::lean_ctor_set(v___x_4943_, 2, v___x_4945_);
                    v___x_4947_ = v___x_4943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_casesTypes_4937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 1, v_extThms_4938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 2, v___x_4945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 3, v_ematch_4940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 4, v_inj_4941_);
                    v___x_4947_ = v_reuseFailAlloc_4948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4947_;
            }
            5 => {
                v___x_4960_ = leanh::lean_box((v_eager_4951_) as usize);
                v___x_4961_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_4952_, v_declName_4950_, v___x_4960_);
                if v_isShared_4959_ == 0 {
                    leanh::lean_ctor_set(v___x_4958_, 0, v___x_4961_);
                    v___x_4963_ = v___x_4958_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4964_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 0, v___x_4961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 1, v_extThms_4953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 2, v_funCC_4954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 3, v_ematch_4955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 4, v_inj_4956_);
                    v___x_4963_ = v_reuseFailAlloc_4964_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4963_;
            }
            7 => {
                v___x_4975_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(v_ematch_4970_, v_thm_4966_);
                if v_isShared_4974_ == 0 {
                    leanh::lean_ctor_set(v___x_4973_, 3, v___x_4975_);
                    v___x_4977_ = v___x_4973_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_casesTypes_4967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 1, v_extThms_4968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 2, v_funCC_4969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 3, v___x_4975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 4, v_inj_4971_);
                    v___x_4977_ = v_reuseFailAlloc_4978_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4977_;
            }
            9 => {
                v___x_4989_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(v_inj_4985_, v_thm_4980_);
                if v_isShared_4988_ == 0 {
                    leanh::lean_ctor_set(v___x_4987_, 4, v___x_4989_);
                    v___x_4991_ = v___x_4987_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4992_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_casesTypes_4981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_extThms_4982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_funCC_4983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 3, v_ematch_4984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 4, v___x_4989_);
                    v___x_4991_ = v_reuseFailAlloc_4992_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(
    mut v_00_u03b2_4994_: *mut leanh::LeanObject,
    mut v_x_4995_: *mut leanh::LeanObject,
    mut v_x_4996_: *mut leanh::LeanObject,
    mut v_x_4997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4998_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_4995_, v_x_4996_, v_x_4997_);
    return v___x_4998_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(
    mut v_00_u03b2_4999_: *mut leanh::LeanObject,
    mut v_x_5000_: *mut leanh::LeanObject,
    mut v_x_5001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5002_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_5000_, v_x_5001_);
    return v___x_5002_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(
    mut v_00_u03b2_5003_: *mut leanh::LeanObject,
    mut v_x_5004_: *mut leanh::LeanObject,
    mut v_x_5005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5006_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_5003_, v_x_5004_, v_x_5005_);
    leanh::lean_dec_ref(v_x_5005_);
    return v_res_5006_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(
    mut v_00_u03b2_5007_: *mut leanh::LeanObject,
    mut v_x_5008_: *mut leanh::LeanObject,
    mut v_x_5009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5010_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_5008_, v_x_5009_);
    return v___x_5010_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(
    mut v_00_u03b2_5011_: *mut leanh::LeanObject,
    mut v_x_5012_: *mut leanh::LeanObject,
    mut v_x_5013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5014_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_5011_, v_x_5012_, v_x_5013_);
    leanh::lean_dec_ref(v_x_5013_);
    leanh::lean_dec_ref(v_x_5012_);
    return v_res_5014_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(
    mut v_00_u03b2_5015_: *mut leanh::LeanObject,
    mut v_x_5016_: *mut leanh::LeanObject,
    mut v_x_5017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5018_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_5016_, v_x_5017_);
    return v___x_5018_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(
    mut v_00_u03b2_5019_: *mut leanh::LeanObject,
    mut v_x_5020_: *mut leanh::LeanObject,
    mut v_x_5021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5022_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_5019_, v_x_5020_, v_x_5021_);
    leanh::lean_dec(v_x_5021_);
    leanh::lean_dec_ref(v_x_5020_);
    return v_res_5022_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5023_: *mut leanh::LeanObject,
    mut v_x_5024_: *mut leanh::LeanObject,
    mut v_x_5025_: usize,
    mut v_x_5026_: usize,
    mut v_x_5027_: *mut leanh::LeanObject,
    mut v_x_5028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5029_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_5024_, v_x_5025_, v_x_5026_, v_x_5027_, v_x_5028_);
    return v___x_5029_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_5030_: *mut leanh::LeanObject,
    mut v_x_5031_: *mut leanh::LeanObject,
    mut v_x_5032_: *mut leanh::LeanObject,
    mut v_x_5033_: *mut leanh::LeanObject,
    mut v_x_5034_: *mut leanh::LeanObject,
    mut v_x_5035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2302__boxed_5036_: usize = 0;
    let mut v_x_2303__boxed_5037_: usize = 0;
    let mut v_res_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2302__boxed_5036_ = leanh::lean_unbox_usize(v_x_5032_);
    leanh::lean_dec(v_x_5032_);
    v_x_2303__boxed_5037_ = leanh::lean_unbox_usize(v_x_5033_);
    leanh::lean_dec(v_x_5033_);
    v_res_5038_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_5030_, v_x_5031_, v_x_2302__boxed_5036_, v_x_2303__boxed_5037_, v_x_5034_, v_x_5035_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(
    mut v_00_u03b2_5039_: *mut leanh::LeanObject,
    mut v_x_5040_: *mut leanh::LeanObject,
    mut v_x_5041_: usize,
    mut v_x_5042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5043_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_5040_, v_x_5041_, v_x_5042_);
    return v___x_5043_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_5044_: *mut leanh::LeanObject,
    mut v_x_5045_: *mut leanh::LeanObject,
    mut v_x_5046_: *mut leanh::LeanObject,
    mut v_x_5047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2319__boxed_5048_: usize = 0;
    let mut v_res_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2319__boxed_5048_ = leanh::lean_unbox_usize(v_x_5046_);
    leanh::lean_dec(v_x_5046_);
    v_res_5049_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_5044_, v_x_5045_, v_x_2319__boxed_5048_, v_x_5047_);
    leanh::lean_dec_ref(v_x_5047_);
    return v_res_5049_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(
    mut v_00_u03b2_5050_: *mut leanh::LeanObject,
    mut v_x_5051_: *mut leanh::LeanObject,
    mut v_x_5052_: usize,
    mut v_x_5053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_5051_, v_x_5052_, v_x_5053_);
    return v___x_5054_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(
    mut v_00_u03b2_5055_: *mut leanh::LeanObject,
    mut v_x_5056_: *mut leanh::LeanObject,
    mut v_x_5057_: *mut leanh::LeanObject,
    mut v_x_5058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2330__boxed_5059_: usize = 0;
    let mut v_res_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2330__boxed_5059_ = leanh::lean_unbox_usize(v_x_5057_);
    leanh::lean_dec(v_x_5057_);
    v_res_5060_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_5055_, v_x_5056_, v_x_2330__boxed_5059_, v_x_5058_);
    leanh::lean_dec_ref(v_x_5058_);
    leanh::lean_dec_ref(v_x_5056_);
    return v_res_5060_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(
    mut v_00_u03b2_5061_: *mut leanh::LeanObject,
    mut v_x_5062_: *mut leanh::LeanObject,
    mut v_x_5063_: usize,
    mut v_x_5064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_5062_, v_x_5063_, v_x_5064_);
    return v___x_5065_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(
    mut v_00_u03b2_5066_: *mut leanh::LeanObject,
    mut v_x_5067_: *mut leanh::LeanObject,
    mut v_x_5068_: *mut leanh::LeanObject,
    mut v_x_5069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2341__boxed_5070_: usize = 0;
    let mut v_res_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2341__boxed_5070_ = leanh::lean_unbox_usize(v_x_5068_);
    leanh::lean_dec(v_x_5068_);
    v_res_5071_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_5066_, v_x_5067_, v_x_2341__boxed_5070_, v_x_5069_);
    leanh::lean_dec(v_x_5069_);
    leanh::lean_dec_ref(v_x_5067_);
    return v_res_5071_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_5072_: *mut leanh::LeanObject,
    mut v_n_5073_: *mut leanh::LeanObject,
    mut v_k_5074_: *mut leanh::LeanObject,
    mut v_v_5075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5076_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_5073_, v_k_5074_, v_v_5075_);
    return v___x_5076_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(
    mut v_00_u03b2_5077_: *mut leanh::LeanObject,
    mut v_depth_5078_: usize,
    mut v_keys_5079_: *mut leanh::LeanObject,
    mut v_vals_5080_: *mut leanh::LeanObject,
    mut v_heq_5081_: *mut leanh::LeanObject,
    mut v_i_5082_: *mut leanh::LeanObject,
    mut v_entries_5083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_5078_, v_keys_5079_, v_vals_5080_, v_i_5082_, v_entries_5083_);
    return v___x_5084_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_5085_: *mut leanh::LeanObject,
    mut v_depth_5086_: *mut leanh::LeanObject,
    mut v_keys_5087_: *mut leanh::LeanObject,
    mut v_vals_5088_: *mut leanh::LeanObject,
    mut v_heq_5089_: *mut leanh::LeanObject,
    mut v_i_5090_: *mut leanh::LeanObject,
    mut v_entries_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5092_: usize = 0;
    let mut v_res_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5092_ = leanh::lean_unbox_usize(v_depth_5086_);
    leanh::lean_dec(v_depth_5086_);
    v_res_5093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_5085_, v_depth_boxed_5092_, v_keys_5087_, v_vals_5088_, v_heq_5089_, v_i_5090_, v_entries_5091_);
    leanh::lean_dec_ref(v_vals_5088_);
    leanh::lean_dec_ref(v_keys_5087_);
    return v_res_5093_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(
    mut v_00_u03b2_5094_: *mut leanh::LeanObject,
    mut v_keys_5095_: *mut leanh::LeanObject,
    mut v_vals_5096_: *mut leanh::LeanObject,
    mut v_heq_5097_: *mut leanh::LeanObject,
    mut v_i_5098_: *mut leanh::LeanObject,
    mut v_k_5099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5100_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_5095_, v_vals_5096_, v_i_5098_, v_k_5099_);
    return v___x_5100_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(
    mut v_00_u03b2_5101_: *mut leanh::LeanObject,
    mut v_keys_5102_: *mut leanh::LeanObject,
    mut v_vals_5103_: *mut leanh::LeanObject,
    mut v_heq_5104_: *mut leanh::LeanObject,
    mut v_i_5105_: *mut leanh::LeanObject,
    mut v_k_5106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5107_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_5101_, v_keys_5102_, v_vals_5103_, v_heq_5104_, v_i_5105_, v_k_5106_);
    leanh::lean_dec_ref(v_k_5106_);
    leanh::lean_dec_ref(v_vals_5103_);
    leanh::lean_dec_ref(v_keys_5102_);
    return v_res_5107_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(
    mut v_00_u03b2_5108_: *mut leanh::LeanObject,
    mut v_keys_5109_: *mut leanh::LeanObject,
    mut v_vals_5110_: *mut leanh::LeanObject,
    mut v_heq_5111_: *mut leanh::LeanObject,
    mut v_i_5112_: *mut leanh::LeanObject,
    mut v_k_5113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_5109_, v_vals_5110_, v_i_5112_, v_k_5113_);
    return v___x_5114_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(
    mut v_00_u03b2_5115_: *mut leanh::LeanObject,
    mut v_keys_5116_: *mut leanh::LeanObject,
    mut v_vals_5117_: *mut leanh::LeanObject,
    mut v_heq_5118_: *mut leanh::LeanObject,
    mut v_i_5119_: *mut leanh::LeanObject,
    mut v_k_5120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5121_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_5115_, v_keys_5116_, v_vals_5117_, v_heq_5118_, v_i_5119_, v_k_5120_);
    leanh::lean_dec(v_k_5120_);
    leanh::lean_dec_ref(v_vals_5117_);
    leanh::lean_dec_ref(v_keys_5116_);
    return v_res_5121_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(
    mut v_00_u03b2_5122_: *mut leanh::LeanObject,
    mut v_x_5123_: *mut leanh::LeanObject,
    mut v_x_5124_: *mut leanh::LeanObject,
    mut v_x_5125_: *mut leanh::LeanObject,
    mut v_x_5126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5127_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_5123_, v_x_5124_, v_x_5125_, v_x_5126_);
    return v___x_5127_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5154_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__10;
    v___x_5155_ = l_Lean_mkAtom(v___x_5154_);
    return v___x_5155_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5156_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12,
    );
    v___x_5157_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5158_ = lean_array_push(v___x_5157_, v___x_5156_);
    return v___x_5158_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5167_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__17;
    v___x_5168_ = l_Lean_mkAtom(v___x_5167_);
    return v___x_5168_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5169_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18,
    );
    v___x_5170_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5171_ = lean_array_push(v___x_5170_, v___x_5169_);
    return v___x_5171_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5172_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19,
    );
    v___x_5173_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__16;
    v___x_5174_ = leanh::lean_box(2);
    v___x_5175_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5175_, 0, v___x_5174_);
    leanh::lean_ctor_set(v___x_5175_, 1, v___x_5173_);
    leanh::lean_ctor_set(v___x_5175_, 2, v___x_5172_);
    return v___x_5175_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5176_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20,
    );
    v___x_5177_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13,
    );
    v___x_5178_ = lean_array_push(v___x_5177_, v___x_5176_);
    return v___x_5178_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5179_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21,
    );
    v___x_5180_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__11;
    v___x_5181_ = leanh::lean_box(2);
    v___x_5182_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5182_, 0, v___x_5181_);
    leanh::lean_ctor_set(v___x_5182_, 1, v___x_5180_);
    leanh::lean_ctor_set(v___x_5182_, 2, v___x_5179_);
    return v___x_5182_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5183_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22,
    );
    v___x_5184_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5185_ = lean_array_push(v___x_5184_, v___x_5183_);
    return v___x_5185_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5186_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23,
    );
    v___x_5187_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__9;
    v___x_5188_ = leanh::lean_box(2);
    v___x_5189_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5189_, 0, v___x_5188_);
    leanh::lean_ctor_set(v___x_5189_, 1, v___x_5187_);
    leanh::lean_ctor_set(v___x_5189_, 2, v___x_5186_);
    return v___x_5189_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5190_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24,
    );
    v___x_5191_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5192_ = lean_array_push(v___x_5191_, v___x_5190_);
    return v___x_5192_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5193_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25,
    );
    v___x_5194_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__7;
    v___x_5195_ = leanh::lean_box(2);
    v___x_5196_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5196_, 0, v___x_5195_);
    leanh::lean_ctor_set(v___x_5196_, 1, v___x_5194_);
    leanh::lean_ctor_set(v___x_5196_, 2, v___x_5193_);
    return v___x_5196_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5197_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26,
    );
    v___x_5198_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5199_ = lean_array_push(v___x_5198_, v___x_5197_);
    return v___x_5199_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5200_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27,
    );
    v___x_5201_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__4;
    v___x_5202_ = leanh::lean_box(2);
    v___x_5203_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5203_, 0, v___x_5202_);
    leanh::lean_ctor_set(v___x_5203_, 1, v___x_5201_);
    leanh::lean_ctor_set(v___x_5203_, 2, v___x_5200_);
    return v___x_5203_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5204_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28,
    );
    return v___x_5204_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(
    mut v_msg_5205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = leanh::lean_box(0);
    v___x_5207_ = lean_panic_fn_borrowed(v___x_5206_, v_msg_5205_);
    return v___x_5207_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5210_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2;
    v___x_5211_ = leanh::lean_unsigned_to_nat(17);
    v___x_5212_ = leanh::lean_unsigned_to_nat(203);
    v___x_5213_ = l_Lean_Meta_Grind_mkExtension___lam__0___closed__1;
    v___x_5214_ = l_Lean_Meta_Grind_mkExtension___lam__0___closed__0;
    v___x_5215_ = l_mkPanicMessageWithDecl(
        v___x_5214_,
        v___x_5213_,
        v___x_5212_,
        v___x_5211_,
        v___x_5210_,
    );
    return v___x_5215_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___lam__0(
    mut v_x_5216_: *mut leanh::LeanObject,
    mut v_e_5217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: u8 = 0;
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_5217_) {
                3 => {
                    v_thm_5226_ = leanh::lean_ctor_get(v_e_5217_, 0);
                    v_origin_5227_ = leanh::lean_ctor_get(v_thm_5226_, 5);
                    if leanh::lean_obj_tag(v_origin_5227_) == 0 {
                        v_declName_5228_ = leanh::lean_ctor_get(v_origin_5227_, 0);
                        leanh::lean_inc(v_declName_5228_);
                        v___y_5219_ = v_declName_5228_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5229_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_mkExtension___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2,
                        );
                        v___x_5230_ =
                            l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_5229_);
                        v___y_5219_ = v___x_5230_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_thm_5231_ = leanh::lean_ctor_get(v_e_5217_, 0);
                    v_origin_5232_ = leanh::lean_ctor_get(v_thm_5231_, 3);
                    if leanh::lean_obj_tag(v_origin_5232_) == 0 {
                        v_declName_5233_ = leanh::lean_ctor_get(v_origin_5232_, 0);
                        leanh::lean_inc(v_declName_5233_);
                        v___y_5219_ = v_declName_5233_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5234_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_mkExtension___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2,
                        );
                        v___x_5235_ =
                            l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_5234_);
                        v___y_5219_ = v___x_5235_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_declName_5236_ = leanh::lean_ctor_get(v_e_5217_, 0);
                    leanh::lean_inc(v_declName_5236_);
                    v___y_5219_ = v_declName_5236_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_5220_ = l_Lean_isPrivateName(v___y_5219_);
                leanh::lean_dec(v___y_5219_);
                if v___x_5220_ == 0 {
                    v___x_5221_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5221_, 0, v_e_5217_);
                    leanh::lean_inc_ref_n(v___x_5221_, 2);
                    v___x_5222_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5222_, 0, v___x_5221_);
                    leanh::lean_ctor_set(v___x_5222_, 1, v___x_5221_);
                    leanh::lean_ctor_set(v___x_5222_, 2, v___x_5221_);
                    return v___x_5222_;
                } else {
                    v___x_5223_ = leanh::lean_box(0);
                    v___x_5224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5224_, 0, v_e_5217_);
                    v___x_5225_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5225_, 0, v___x_5223_);
                    leanh::lean_ctor_set(v___x_5225_, 1, v___x_5223_);
                    leanh::lean_ctor_set(v___x_5225_, 2, v___x_5224_);
                    return v___x_5225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___lam__0___boxed(
    mut v_x_5237_: *mut leanh::LeanObject,
    mut v_e_5238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5239_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_x_5237_, v_e_5238_);
    leanh::lean_dec_ref(v_x_5237_);
    return v_res_5239_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___lam__1(
    mut v___y_5240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_5240_);
    return v___y_5240_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___lam__1___boxed(
    mut v___y_5241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5242_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_5241_);
    leanh::lean_dec_ref(v___y_5241_);
    return v_res_5242_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension(
    mut v_name_5246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5248_ = l_Lean_Meta_Grind_mkExtension___closed__0;
    v___f_5249_ = l_Lean_Meta_Grind_mkExtension___closed__1;
    v___x_5250_ = l_Lean_Meta_Grind_mkExtension___closed__2;
    v___x_5251_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2,
    );
    v___x_5252_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_5252_, 0, v_name_5246_);
    leanh::lean_ctor_set(v___x_5252_, 1, v___x_5250_);
    leanh::lean_ctor_set(v___x_5252_, 2, v___x_5251_);
    leanh::lean_ctor_set(v___x_5252_, 3, v___f_5249_);
    leanh::lean_ctor_set(v___x_5252_, 4, v___f_5248_);
    v___x_5253_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_5252_);
    return v___x_5253_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___boxed(
    mut v_name_5254_: *mut leanh::LeanObject,
    mut v_a_5255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Lean_Meta_Grind_mkExtension(v_name_5254_);
    return v_res_5256_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5257_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5258_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
    v___x_5259_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5259_, 0, v___x_5258_);
    return v___x_5259_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5260_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
    v___x_5261_ = leanh::lean_unsigned_to_nat(0);
    v___x_5262_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_5262_, 0, v___x_5261_);
    leanh::lean_ctor_set(v___x_5262_, 1, v___x_5261_);
    leanh::lean_ctor_set(v___x_5262_, 2, v___x_5261_);
    leanh::lean_ctor_set(v___x_5262_, 3, v___x_5261_);
    leanh::lean_ctor_set(v___x_5262_, 4, v___x_5260_);
    leanh::lean_ctor_set(v___x_5262_, 5, v___x_5260_);
    leanh::lean_ctor_set(v___x_5262_, 6, v___x_5260_);
    leanh::lean_ctor_set(v___x_5262_, 7, v___x_5260_);
    leanh::lean_ctor_set(v___x_5262_, 8, v___x_5260_);
    leanh::lean_ctor_set(v___x_5262_, 9, v___x_5260_);
    return v___x_5262_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5263_ = leanh::lean_unsigned_to_nat(32);
    v___x_5264_ = lean_mk_empty_array_with_capacity(v___x_5263_);
    v___x_5265_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5265_, 0, v___x_5264_);
    return v___x_5265_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5266_: usize = 0;
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5266_ = 5usize;
    v___x_5267_ = leanh::lean_unsigned_to_nat(0);
    v___x_5268_ = leanh::lean_unsigned_to_nat(32);
    v___x_5269_ = lean_mk_empty_array_with_capacity(v___x_5268_);
    v___x_5270_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
    v___x_5271_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5271_, 0, v___x_5270_);
    leanh::lean_ctor_set(v___x_5271_, 1, v___x_5269_);
    leanh::lean_ctor_set(v___x_5271_, 2, v___x_5267_);
    leanh::lean_ctor_set(v___x_5271_, 3, v___x_5267_);
    leanh::lean_ctor_set_usize(v___x_5271_, 4, v___x_5266_);
    return v___x_5271_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5272_ = leanh::lean_box(1);
    v___x_5273_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
    v___x_5274_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
    v___x_5275_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5275_, 0, v___x_5274_);
    leanh::lean_ctor_set(v___x_5275_, 1, v___x_5273_);
    leanh::lean_ctor_set(v___x_5275_, 2, v___x_5272_);
    return v___x_5275_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(
    mut v_msgData_5276_: *mut leanh::LeanObject,
    mut v___y_5277_: *mut leanh::LeanObject,
    mut v___y_5278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5280_ = lean_st_ref_get(v___y_5278_);
    v_env_5281_ = leanh::lean_ctor_get(v___x_5280_, 0);
    leanh::lean_inc_ref(v_env_5281_);
    leanh::lean_dec(v___x_5280_);
    v_options_5282_ = leanh::lean_ctor_get(v___y_5277_, 2);
    v___x_5283_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
    v___x_5284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_5282_);
    v___x_5285_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5285_, 0, v_env_5281_);
    leanh::lean_ctor_set(v___x_5285_, 1, v___x_5283_);
    leanh::lean_ctor_set(v___x_5285_, 2, v___x_5284_);
    leanh::lean_ctor_set(v___x_5285_, 3, v_options_5282_);
    v___x_5286_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5286_, 0, v___x_5285_);
    leanh::lean_ctor_set(v___x_5286_, 1, v_msgData_5276_);
    v___x_5287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5287_, 0, v___x_5286_);
    return v___x_5287_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(
    mut v_msgData_5288_: *mut leanh::LeanObject,
    mut v___y_5289_: *mut leanh::LeanObject,
    mut v___y_5290_: *mut leanh::LeanObject,
    mut v___y_5291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_5288_, v___y_5289_, v___y_5290_);
    leanh::lean_dec(v___y_5290_);
    leanh::lean_dec_ref(v___y_5289_);
    return v_res_5292_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(
    mut v_msg_5293_: *mut leanh::LeanObject,
    mut v___y_5294_: *mut leanh::LeanObject,
    mut v___y_5295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5297_ = leanh::lean_ctor_get(v___y_5294_, 5);
                v___x_5298_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_5293_, v___y_5294_, v___y_5295_);
                v_a_5299_ = leanh::lean_ctor_get(v___x_5298_, 0);
                v_isSharedCheck_5307_ = (!leanh::lean_is_exclusive(v___x_5298_)) as u8;
                if v_isSharedCheck_5307_ == 0 {
                    v___x_5301_ = v___x_5298_;
                    v_isShared_5302_ = v_isSharedCheck_5307_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5299_);
                    leanh::lean_dec(v___x_5298_);
                    v___x_5301_ = leanh::lean_box(0);
                    v_isShared_5302_ = v_isSharedCheck_5307_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_5297_);
                v___x_5303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5303_, 0, v_ref_5297_);
                leanh::lean_ctor_set(v___x_5303_, 1, v_a_5299_);
                if v_isShared_5302_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5301_, 1);
                    leanh::lean_ctor_set(v___x_5301_, 0, v___x_5303_);
                    v___x_5305_ = v___x_5301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5306_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5303_);
                    v___x_5305_ = v_reuseFailAlloc_5306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(
    mut v_msg_5308_: *mut leanh::LeanObject,
    mut v___y_5309_: *mut leanh::LeanObject,
    mut v___y_5310_: *mut leanh::LeanObject,
    mut v___y_5311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_5308_, v___y_5309_, v___y_5310_);
    leanh::lean_dec(v___y_5310_);
    leanh::lean_dec_ref(v___y_5309_);
    return v_res_5312_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5314_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0;
    v___x_5315_ = l_Lean_stringToMessageData(v___x_5314_);
    return v___x_5315_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5317_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2;
    v___x_5318_ = l_Lean_stringToMessageData(v___x_5317_);
    return v___x_5318_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(
    mut v_declName_5319_: *mut leanh::LeanObject,
    mut v_a_5320_: *mut leanh::LeanObject,
    mut v_a_5321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: u8 = 0;
    let mut v___x_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5323_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1,
    );
    v___x_5324_ = 0;
    v___x_5325_ = l_Lean_MessageData_ofConstName(v_declName_5319_, v___x_5324_);
    v___x_5326_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5326_, 0, v___x_5323_);
    leanh::lean_ctor_set(v___x_5326_, 1, v___x_5325_);
    v___x_5327_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3,
    );
    v___x_5328_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5328_, 0, v___x_5326_);
    leanh::lean_ctor_set(v___x_5328_, 1, v___x_5327_);
    v___x_5329_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_5328_, v_a_5320_, v_a_5321_);
    return v___x_5329_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(
    mut v_declName_5330_: *mut leanh::LeanObject,
    mut v_a_5331_: *mut leanh::LeanObject,
    mut v_a_5332_: *mut leanh::LeanObject,
    mut v_a_5333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(
        v_declName_5330_,
        v_a_5331_,
        v_a_5332_,
    );
    leanh::lean_dec(v_a_5332_);
    leanh::lean_dec_ref(v_a_5331_);
    return v_res_5334_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(
    mut v_00_u03b1_5335_: *mut leanh::LeanObject,
    mut v_declName_5336_: *mut leanh::LeanObject,
    mut v_a_5337_: *mut leanh::LeanObject,
    mut v_a_5338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5340_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(
        v_declName_5336_,
        v_a_5337_,
        v_a_5338_,
    );
    return v___x_5340_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(
    mut v_00_u03b1_5341_: *mut leanh::LeanObject,
    mut v_declName_5342_: *mut leanh::LeanObject,
    mut v_a_5343_: *mut leanh::LeanObject,
    mut v_a_5344_: *mut leanh::LeanObject,
    mut v_a_5345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5346_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(
        v_00_u03b1_5341_,
        v_declName_5342_,
        v_a_5343_,
        v_a_5344_,
    );
    leanh::lean_dec(v_a_5344_);
    leanh::lean_dec_ref(v_a_5343_);
    return v_res_5346_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(
    mut v_00_u03b1_5347_: *mut leanh::LeanObject,
    mut v_msg_5348_: *mut leanh::LeanObject,
    mut v___y_5349_: *mut leanh::LeanObject,
    mut v___y_5350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5352_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_5348_, v___y_5349_, v___y_5350_);
    return v___x_5352_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(
    mut v_00_u03b1_5353_: *mut leanh::LeanObject,
    mut v_msg_5354_: *mut leanh::LeanObject,
    mut v___y_5355_: *mut leanh::LeanObject,
    mut v___y_5356_: *mut leanh::LeanObject,
    mut v___y_5357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5358_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(
            v_00_u03b1_5353_,
            v_msg_5354_,
            v___y_5355_,
            v___y_5356_,
        );
    leanh::lean_dec(v___y_5356_);
    leanh::lean_dec_ref(v___y_5355_);
    return v_res_5358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Extension(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_instInhabitedCasesTypes_default =
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCasesTypes_default);
    l_Lean_Meta_Grind_instInhabitedCasesTypes = _init_l_Lean_Meta_Grind_instInhabitedCasesTypes();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCasesTypes);
    l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default =
        _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default);
    l_Lean_Meta_Grind_instInhabitedSymbolPriorities =
        _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSymbolPriorities);
    l_Lean_Meta_Grind_instInhabitedCnstrRHS_default =
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default);
    l_Lean_Meta_Grind_instInhabitedCnstrRHS = _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCnstrRHS);
    l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default,
    );
    l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint);
    l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default);
    l_Lean_Meta_Grind_instInhabitedEMatchTheorem =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorem);
    l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default =
        _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default);
    l_Lean_Meta_Grind_instInhabitedInjectiveTheorem =
        _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedInjectiveTheorem);
    l_Lean_Meta_Grind_instInhabitedExtensionState_default =
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedExtensionState_default);
    l_Lean_Meta_Grind_instInhabitedExtensionState =
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedExtensionState);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Extension(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Meta_Grind_mkExtension___auto__1 = _init_l_Lean_Meta_Grind_mkExtension___auto__1();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_mkExtension___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Extension(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
}
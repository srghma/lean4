// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Extension
// Imports: Lean.Meta.Tactic.Grind.Theorems
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_eraseIdx___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom, l_instInhabitedOfMonad___redArg,
};
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
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_box_uint64, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCasesTypes_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCasesTypes: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedSymbolPriorities: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqEMatchTheoremKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value: LeanStringObject<
    44,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value: LeanStringObject<
    44,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value: LeanStringObject<
    40,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value: LeanStringObject<
    38,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value: LeanStringObject<
    39,
> = LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 69, 77, 97, 116,
        99, 104, 84, 104, 101, 111, 114, 101, 109, 75, 105, 110, 100, 46, 117, 115, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value: LeanStringObject<
    40,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value: LeanStringObject<
    40,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value: LeanStringObject<
    41,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value: LeanStringObject<
    38,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value: LeanStringObject<
    42,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instReprEMatchTheoremKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8: u64 = 0;
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9: u64 = 0;
pub static l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instHashableEMatchTheoremKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109,
            121, 0,
        ],
    };
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value)
                as *mut LeanObject,
            17542774118954891045 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedCnstrRHS: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqCnstrRHS: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value
) as *mut LeanObject;
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instReprCnstrRHS___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instReprCnstrRHS: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value:
    LeanStringObject<49> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value:
    LeanStringObject<47> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value:
    LeanStringObject<48> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value:
    LeanStringObject<49> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value:
    LeanStringObject<48> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value:
    LeanStringObject<49> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value:
    LeanStringObject<49> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instReprEMatchTheoremConstraint: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedEMatchTheorem: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedInjectiveTheorem: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEntry_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedExtensionState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedExtensionState: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 84, 104, 101, 111, 114, 101, 109, 115, 46, 105, 110, 115, 101, 114, 116, 0]};
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___auto__1___closed__17_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_mkExtension___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___lam__0___closed__0_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___lam__0___closed__1_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 69,
            120, 116, 101, 110, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkExtension___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkExtension___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_mkExtension___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_mkExtension___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_mkExtension___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_mkExtension___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkExtension___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_ExtensionState_addEntry as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_mkExtension___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkExtension___closed__2_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2_value:
    LeanStringObject<45> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    v___x_2680_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2680_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1()
-> *mut LeanObject {
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    v___x_2681_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once),
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0,
    );
    v___x_2682_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2682_, 0, v___x_2681_);
    return v___x_2682_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default() -> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v___x_2683_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once),
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1,
    );
    return v___x_2683_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCasesTypes() -> *mut LeanObject {
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    v___x_2684_ = l_Lean_Meta_Grind_instInhabitedCasesTypes_default;
    return v___x_2684_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2685_: *mut LeanObject,
    mut v_x_2686_: *mut LeanObject,
    mut v_x_2687_: *mut LeanObject,
    mut v_x_2688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: u8 = 0;
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2689_ = lean_ctor_get(v_x_2685_, 0);
                v_vs_2690_ = lean_ctor_get(v_x_2685_, 1);
                v_isSharedCheck_2714_ = (!lean_is_exclusive(v_x_2685_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v___x_2692_ = v_x_2685_;
                    v_isShared_2693_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2690_);
                    lean_inc(v_ks_2689_);
                    lean_dec(v_x_2685_);
                    v___x_2692_ = lean_box(0);
                    v_isShared_2693_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2694_ = lean_array_get_size(v_ks_2689_);
                v___x_2695_ = lean_nat_dec_lt(v_x_2686_, v___x_2694_);
                if v___x_2695_ == 0 {
                    lean_dec(v_x_2686_);
                    v___x_2696_ = lean_array_push(v_ks_2689_, v_x_2687_);
                    v___x_2697_ = lean_array_push(v_vs_2690_, v_x_2688_);
                    if v_isShared_2693_ == 0 {
                        lean_ctor_set(v___x_2692_, 1, v___x_2697_);
                        lean_ctor_set(v___x_2692_, 0, v___x_2696_);
                        v___x_2699_ = v___x_2692_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
                        lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2697_);
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
                            v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_ks_2689_);
                            lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_vs_2690_);
                            v___x_2704_ = v_reuseFailAlloc_2708_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2709_ = lean_array_fset(v_ks_2689_, v_x_2686_, v_x_2687_);
                        v___x_2710_ = lean_array_fset(v_vs_2690_, v_x_2686_, v_x_2688_);
                        lean_dec(v_x_2686_);
                        if v_isShared_2693_ == 0 {
                            lean_ctor_set(v___x_2692_, 1, v___x_2710_);
                            lean_ctor_set(v___x_2692_, 0, v___x_2709_);
                            v___x_2712_ = v___x_2692_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2709_);
                            lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2710_);
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
                v___x_2705_ = lean_unsigned_to_nat(1);
                v___x_2706_ = lean_nat_add(v_x_2686_, v___x_2705_);
                lean_dec(v_x_2686_);
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
    mut v_n_2715_: *mut LeanObject,
    mut v_k_2716_: *mut LeanObject,
    mut v_v_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    v___x_2718_ = lean_unsigned_to_nat(0);
    v___x_2719_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2715_, v___x_2718_, v_k_2716_, v_v_2717_);
    return v___x_2719_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: u64 = 0;
    v___x_2720_ = lean_unsigned_to_nat(1723);
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
    v___x_2726_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
    v___x_2727_ = lean_usize_sub(v___x_2726_, v___x_2725_);
    return v___x_2727_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2728_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(
    mut v_x_2729_: *mut LeanObject,
    mut v_x_2730_: usize,
    mut v_x_2731_: usize,
    mut v_x_2732_: *mut LeanObject,
    mut v_x_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: usize = 0;
    let mut v___x_2736_: usize = 0;
    let mut v___x_2737_: usize = 0;
    let mut v___x_2738_: usize = 0;
    let mut v_j_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v_v_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2765_: u8 = 0;
    let mut v_node_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2769_: u8 = 0;
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2778_: u8 = 0;
    let mut v_unused_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: u8 = 0;
    let mut v_ks_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: usize = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: u8 = 0;
    let mut v_reuseFailAlloc_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2729_) == 0 {
                    v_es_2734_ = lean_ctor_get(v_x_2729_, 0);
                    v___x_2735_ = 5usize;
                    v___x_2736_ = 1usize;
                    v___x_2737_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_2738_ = lean_usize_land(v_x_2730_, v___x_2737_);
                    v_j_2739_ = lean_usize_to_nat(v___x_2738_);
                    v___x_2740_ = lean_array_get_size(v_es_2734_);
                    v___x_2741_ = lean_nat_dec_lt(v_j_2739_, v___x_2740_);
                    if v___x_2741_ == 0 {
                        lean_dec(v_j_2739_);
                        lean_dec(v_x_2733_);
                        lean_dec(v_x_2732_);
                        return v_x_2729_;
                    } else {
                        lean_inc_ref(v_es_2734_);
                        v_isSharedCheck_2778_ = (!lean_is_exclusive(v_x_2729_)) as u8;
                        if v_isSharedCheck_2778_ == 0 {
                            v_unused_2779_ = lean_ctor_get(v_x_2729_, 0);
                            lean_dec(v_unused_2779_);
                            v___x_2743_ = v_x_2729_;
                            v_isShared_2744_ = v_isSharedCheck_2778_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2729_);
                            v___x_2743_ = lean_box(0);
                            v_isShared_2744_ = v_isSharedCheck_2778_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2780_ = lean_ctor_get(v_x_2729_, 0);
                    v_vs_2781_ = lean_ctor_get(v_x_2729_, 1);
                    v_isSharedCheck_2801_ = (!lean_is_exclusive(v_x_2729_)) as u8;
                    if v_isSharedCheck_2801_ == 0 {
                        v___x_2783_ = v_x_2729_;
                        v_isShared_2784_ = v_isSharedCheck_2801_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2781_);
                        lean_inc(v_ks_2780_);
                        lean_dec(v_x_2729_);
                        v___x_2783_ = lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2801_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2745_ = lean_array_fget(v_es_2734_, v_j_2739_);
                v___x_2746_ = lean_box(0);
                v_xs_x27_2747_ = lean_array_fset(v_es_2734_, v_j_2739_, v___x_2746_);
                match lean_obj_tag(v_v_2745_) {
                    0 => {
                        v_key_2754_ = lean_ctor_get(v_v_2745_, 0);
                        v_val_2755_ = lean_ctor_get(v_v_2745_, 1);
                        v_isSharedCheck_2765_ = (!lean_is_exclusive(v_v_2745_)) as u8;
                        if v_isSharedCheck_2765_ == 0 {
                            v___x_2757_ = v_v_2745_;
                            v_isShared_2758_ = v_isSharedCheck_2765_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2755_);
                            lean_inc(v_key_2754_);
                            lean_dec(v_v_2745_);
                            v___x_2757_ = lean_box(0);
                            v_isShared_2758_ = v_isSharedCheck_2765_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2766_ = lean_ctor_get(v_v_2745_, 0);
                        v_isSharedCheck_2776_ = (!lean_is_exclusive(v_v_2745_)) as u8;
                        if v_isSharedCheck_2776_ == 0 {
                            v___x_2768_ = v_v_2745_;
                            v_isShared_2769_ = v_isSharedCheck_2776_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2766_);
                            lean_dec(v_v_2745_);
                            v___x_2768_ = lean_box(0);
                            v_isShared_2769_ = v_isSharedCheck_2776_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2777_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2777_, 0, v_x_2732_);
                        lean_ctor_set(v___x_2777_, 1, v_x_2733_);
                        v___y_2749_ = v___x_2777_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2750_ = lean_array_fset(v_xs_x27_2747_, v_j_2739_, v___y_2749_);
                lean_dec(v_j_2739_);
                if v_isShared_2744_ == 0 {
                    lean_ctor_set(v___x_2743_, 0, v___x_2750_);
                    v___x_2752_ = v___x_2743_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
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
                    lean_del_object(v___x_2757_);
                    v___x_2760_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2754_,
                        v_val_2755_,
                        v_x_2732_,
                        v_x_2733_,
                    );
                    v___x_2761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2761_, 0, v___x_2760_);
                    v___y_2749_ = v___x_2761_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2755_);
                    lean_dec(v_key_2754_);
                    if v_isShared_2758_ == 0 {
                        lean_ctor_set(v___x_2757_, 1, v_x_2733_);
                        lean_ctor_set(v___x_2757_, 0, v_x_2732_);
                        v___x_2763_ = v___x_2757_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_x_2732_);
                        lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_x_2733_);
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
                    lean_ctor_set(v___x_2768_, 0, v___x_2772_);
                    v___x_2774_ = v___x_2768_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
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
                    v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_ks_2780_);
                    lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_vs_2781_);
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
                    v___x_2798_ = lean_unsigned_to_nat(4);
                    v___x_2799_ = lean_nat_dec_lt(v___x_2797_, v___x_2798_);
                    lean_dec(v___x_2797_);
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
                    v_ks_2790_ = lean_ctor_get(v_newNode_2787_, 0);
                    lean_inc_ref(v_ks_2790_);
                    v_vs_2791_ = lean_ctor_get(v_newNode_2787_, 1);
                    lean_inc_ref(v_vs_2791_);
                    lean_dec_ref(v_newNode_2787_);
                    v___x_2792_ = lean_unsigned_to_nat(0);
                    v___x_2793_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2);
                    v___x_2794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_x_2731_, v_ks_2790_, v_vs_2791_, v___x_2792_, v___x_2793_);
                    lean_dec_ref(v_vs_2791_);
                    lean_dec_ref(v_ks_2790_);
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
    mut v_keys_2803_: *mut LeanObject,
    mut v_vals_2804_: *mut LeanObject,
    mut v_i_2805_: *mut LeanObject,
    mut v_entries_2806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v_k_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: u64 = 0;
    let mut v_h_2813_: usize = 0;
    let mut v___x_2814_: usize = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: usize = 0;
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: usize = 0;
    let mut v_h_2819_: usize = 0;
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: u64 = 0;
    let mut v_hash_2824_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2807_ = lean_array_get_size(v_keys_2803_);
                v___x_2808_ = lean_nat_dec_lt(v_i_2805_, v___x_2807_);
                if v___x_2808_ == 0 {
                    lean_dec(v_i_2805_);
                    return v_entries_2806_;
                } else {
                    v_k_2809_ = lean_array_fget_borrowed(v_keys_2803_, v_i_2805_);
                    v_v_2810_ = lean_array_fget_borrowed(v_vals_2804_, v_i_2805_);
                    if lean_obj_tag(v_k_2809_) == 0 {
                        v___x_2823_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_2812_ = v___x_2823_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2824_ = lean_ctor_get_uint64(
                            v_k_2809_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                v___x_2815_ = lean_unsigned_to_nat(1);
                v___x_2816_ = 1usize;
                v___x_2817_ = lean_usize_sub(v_depth_2802_, v___x_2816_);
                v___x_2818_ = lean_usize_mul(v___x_2814_, v___x_2817_);
                v_h_2819_ = lean_usize_shift_right(v_h_2813_, v___x_2818_);
                v___x_2820_ = lean_nat_add(v_i_2805_, v___x_2815_);
                lean_dec(v_i_2805_);
                lean_inc(v_v_2810_);
                lean_inc(v_k_2809_);
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
    mut v_depth_2825_: *mut LeanObject,
    mut v_keys_2826_: *mut LeanObject,
    mut v_vals_2827_: *mut LeanObject,
    mut v_i_2828_: *mut LeanObject,
    mut v_entries_2829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2830_: usize = 0;
    let mut v_res_2831_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2830_ = lean_unbox_usize(v_depth_2825_);
    lean_dec(v_depth_2825_);
    v_res_2831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2830_, v_keys_2826_, v_vals_2827_, v_i_2828_, v_entries_2829_);
    lean_dec_ref(v_vals_2827_);
    lean_dec_ref(v_keys_2826_);
    return v_res_2831_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_2832_: *mut LeanObject,
    mut v_x_2833_: *mut LeanObject,
    mut v_x_2834_: *mut LeanObject,
    mut v_x_2835_: *mut LeanObject,
    mut v_x_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_371__boxed_2837_: usize = 0;
    let mut v_x_372__boxed_2838_: usize = 0;
    let mut v_res_2839_: *mut LeanObject = core::ptr::null_mut();
    v_x_371__boxed_2837_ = lean_unbox_usize(v_x_2833_);
    lean_dec(v_x_2833_);
    v_x_372__boxed_2838_ = lean_unbox_usize(v_x_2834_);
    lean_dec(v_x_2834_);
    v_res_2839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_2832_, v_x_371__boxed_2837_, v_x_372__boxed_2838_, v_x_2835_, v_x_2836_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
    mut v_x_2840_: *mut LeanObject,
    mut v_x_2841_: *mut LeanObject,
    mut v_x_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2844_: u64 = 0;
    let mut v___x_2845_: usize = 0;
    let mut v___x_2846_: usize = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: u64 = 0;
    let mut v_hash_2849_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2841_) == 0 {
                    v___x_2848_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2844_ = v___x_2848_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2849_ = lean_ctor_get_uint64(
                        v_x_2841_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_s_2850_: *mut LeanObject,
    mut v_declName_2851_: *mut LeanObject,
    mut v_eager_2852_: u8,
) -> *mut LeanObject {
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    v___x_2853_ = lean_box((v_eager_2852_) as usize);
    v___x_2854_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
            v_s_2850_,
            v_declName_2851_,
            v___x_2853_,
        );
    return v___x_2854_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_insert___boxed(
    mut v_s_2855_: *mut LeanObject,
    mut v_declName_2856_: *mut LeanObject,
    mut v_eager_2857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eager_boxed_2858_: u8 = 0;
    let mut v_res_2859_: *mut LeanObject = core::ptr::null_mut();
    v_eager_boxed_2858_ = (lean_unbox(v_eager_2857_) as u8);
    v_res_2859_ =
        l_Lean_Meta_Grind_CasesTypes_insert(v_s_2855_, v_declName_2856_, v_eager_boxed_2858_);
    return v_res_2859_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(
    mut v_00_u03b2_2860_: *mut LeanObject,
    mut v_x_2861_: *mut LeanObject,
    mut v_x_2862_: *mut LeanObject,
    mut v_x_2863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    v___x_2864_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
            v_x_2861_, v_x_2862_, v_x_2863_,
        );
    return v___x_2864_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(
    mut v_00_u03b2_2865_: *mut LeanObject,
    mut v_x_2866_: *mut LeanObject,
    mut v_x_2867_: usize,
    mut v_x_2868_: usize,
    mut v_x_2869_: *mut LeanObject,
    mut v_x_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    v___x_2871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_2866_, v_x_2867_, v_x_2868_, v_x_2869_, v_x_2870_);
    return v___x_2871_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_2872_: *mut LeanObject,
    mut v_x_2873_: *mut LeanObject,
    mut v_x_2874_: *mut LeanObject,
    mut v_x_2875_: *mut LeanObject,
    mut v_x_2876_: *mut LeanObject,
    mut v_x_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_570__boxed_2878_: usize = 0;
    let mut v_x_571__boxed_2879_: usize = 0;
    let mut v_res_2880_: *mut LeanObject = core::ptr::null_mut();
    v_x_570__boxed_2878_ = lean_unbox_usize(v_x_2874_);
    lean_dec(v_x_2874_);
    v_x_571__boxed_2879_ = lean_unbox_usize(v_x_2875_);
    lean_dec(v_x_2875_);
    v_res_2880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(v_00_u03b2_2872_, v_x_2873_, v_x_570__boxed_2878_, v_x_571__boxed_2879_, v_x_2876_, v_x_2877_);
    return v_res_2880_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2881_: *mut LeanObject,
    mut v_n_2882_: *mut LeanObject,
    mut v_k_2883_: *mut LeanObject,
    mut v_v_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v_n_2882_, v_k_2883_, v_v_2884_);
    return v___x_2885_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2886_: *mut LeanObject,
    mut v_depth_2887_: usize,
    mut v_keys_2888_: *mut LeanObject,
    mut v_vals_2889_: *mut LeanObject,
    mut v_heq_2890_: *mut LeanObject,
    mut v_i_2891_: *mut LeanObject,
    mut v_entries_2892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    v___x_2893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_2887_, v_keys_2888_, v_vals_2889_, v_i_2891_, v_entries_2892_);
    return v___x_2893_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2894_: *mut LeanObject,
    mut v_depth_2895_: *mut LeanObject,
    mut v_keys_2896_: *mut LeanObject,
    mut v_vals_2897_: *mut LeanObject,
    mut v_heq_2898_: *mut LeanObject,
    mut v_i_2899_: *mut LeanObject,
    mut v_entries_2900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2901_: usize = 0;
    let mut v_res_2902_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2901_ = lean_unbox_usize(v_depth_2895_);
    lean_dec(v_depth_2895_);
    v_res_2902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(v_00_u03b2_2894_, v_depth_boxed_2901_, v_keys_2896_, v_vals_2897_, v_heq_2898_, v_i_2899_, v_entries_2900_);
    lean_dec_ref(v_vals_2897_);
    lean_dec_ref(v_keys_2896_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2903_: *mut LeanObject,
    mut v_x_2904_: *mut LeanObject,
    mut v_x_2905_: *mut LeanObject,
    mut v_x_2906_: *mut LeanObject,
    mut v_x_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    v___x_2908_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2904_, v_x_2905_, v_x_2906_, v_x_2907_);
    return v___x_2908_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v___x_2909_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1()
-> *mut LeanObject {
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    v___x_2910_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0,
    );
    v___x_2911_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2911_, 0, v___x_2910_);
    return v___x_2911_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default() -> *mut LeanObject {
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    v___x_2912_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities() -> *mut LeanObject {
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    v___x_2913_ = l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default;
    return v___x_2913_;
}
pub unsafe fn l_Lean_Meta_Grind_SymbolPriorities_insert(
    mut v_s_2914_: *mut LeanObject,
    mut v_declName_2915_: *mut LeanObject,
    mut v_prio_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    v___x_2917_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(
            v_s_2914_,
            v_declName_2915_,
            v_prio_2916_,
        );
    return v___x_2917_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(
    mut v_x_2918_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2918_) {
        0 => {
            let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
            v___x_2919_ = lean_unsigned_to_nat(0);
            return v___x_2919_;
        }
        1 => {
            let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
            v___x_2920_ = lean_unsigned_to_nat(1);
            return v___x_2920_;
        }
        2 => {
            let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
            v___x_2921_ = lean_unsigned_to_nat(2);
            return v___x_2921_;
        }
        3 => {
            let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
            v___x_2922_ = lean_unsigned_to_nat(3);
            return v___x_2922_;
        }
        4 => {
            let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
            v___x_2923_ = lean_unsigned_to_nat(4);
            return v___x_2923_;
        }
        5 => {
            let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
            v___x_2924_ = lean_unsigned_to_nat(5);
            return v___x_2924_;
        }
        6 => {
            let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
            v___x_2925_ = lean_unsigned_to_nat(6);
            return v___x_2925_;
        }
        7 => {
            let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
            v___x_2926_ = lean_unsigned_to_nat(7);
            return v___x_2926_;
        }
        8 => {
            let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
            v___x_2927_ = lean_unsigned_to_nat(8);
            return v___x_2927_;
        }
        _ => {
            let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
            v___x_2928_ = lean_unsigned_to_nat(9);
            return v___x_2928_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___boxed(
    mut v_x_2929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2930_: *mut LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_2929_);
    lean_dec(v_x_2929_);
    return v_res_2930_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(
    mut v_t_2931_: *mut LeanObject,
    mut v_k_2932_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_2931_) {
        0 => {
            let mut v_gen_2933_: u8 = 0;
            let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
            v_gen_2933_ = lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2934_ = lean_box((v_gen_2933_) as usize);
            v___x_2935_ = lean_apply_1(v_k_2932_, v___x_2934_);
            return v___x_2935_;
        }
        1 => {
            let mut v_gen_2936_: u8 = 0;
            let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
            v_gen_2936_ = lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2937_ = lean_box((v_gen_2936_) as usize);
            v___x_2938_ = lean_apply_1(v_k_2932_, v___x_2937_);
            return v___x_2938_;
        }
        2 => {
            let mut v_gen_2939_: u8 = 0;
            let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
            v_gen_2939_ = lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2940_ = lean_box((v_gen_2939_) as usize);
            v___x_2941_ = lean_apply_1(v_k_2932_, v___x_2940_);
            return v___x_2941_;
        }
        5 => {
            let mut v_gen_2942_: u8 = 0;
            let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
            v_gen_2942_ = lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2943_ = lean_box((v_gen_2942_) as usize);
            v___x_2944_ = lean_apply_1(v_k_2932_, v___x_2943_);
            return v___x_2944_;
        }
        8 => {
            let mut v_gen_2945_: u8 = 0;
            let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
            v_gen_2945_ = lean_ctor_get_uint8(v_t_2931_, 0 as u32);
            v___x_2946_ = lean_box((v_gen_2945_) as usize);
            v___x_2947_ = lean_apply_1(v_k_2932_, v___x_2946_);
            return v___x_2947_;
        }
        _ => {
            return v_k_2932_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(
    mut v_t_2948_: *mut LeanObject,
    mut v_k_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2948_, v_k_2949_);
    lean_dec(v_t_2948_);
    return v_res_2950_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(
    mut v_motive_2951_: *mut LeanObject,
    mut v_ctorIdx_2952_: *mut LeanObject,
    mut v_t_2953_: *mut LeanObject,
    mut v_h_2954_: *mut LeanObject,
    mut v_k_2955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    v___x_2956_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2953_, v_k_2955_);
    return v___x_2956_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(
    mut v_motive_2957_: *mut LeanObject,
    mut v_ctorIdx_2958_: *mut LeanObject,
    mut v_t_2959_: *mut LeanObject,
    mut v_h_2960_: *mut LeanObject,
    mut v_k_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2962_: *mut LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(
        v_motive_2957_,
        v_ctorIdx_2958_,
        v_t_2959_,
        v_h_2960_,
        v_k_2961_,
    );
    lean_dec(v_t_2959_);
    lean_dec(v_ctorIdx_2958_);
    return v_res_2962_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(
    mut v_t_2963_: *mut LeanObject,
    mut v_eqLhs_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    v___x_2965_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2963_, v_eqLhs_2964_);
    return v___x_2965_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(
    mut v_t_2966_: *mut LeanObject,
    mut v_eqLhs_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2968_: *mut LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(v_t_2966_, v_eqLhs_2967_);
    lean_dec(v_t_2966_);
    return v_res_2968_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(
    mut v_motive_2969_: *mut LeanObject,
    mut v_t_2970_: *mut LeanObject,
    mut v_h_2971_: *mut LeanObject,
    mut v_eqLhs_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    v___x_2973_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2970_, v_eqLhs_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(
    mut v_motive_2974_: *mut LeanObject,
    mut v_t_2975_: *mut LeanObject,
    mut v_h_2976_: *mut LeanObject,
    mut v_eqLhs_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2978_: *mut LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(
        v_motive_2974_,
        v_t_2975_,
        v_h_2976_,
        v_eqLhs_2977_,
    );
    lean_dec(v_t_2975_);
    return v_res_2978_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(
    mut v_t_2979_: *mut LeanObject,
    mut v_eqRhs_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    v___x_2981_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2979_, v_eqRhs_2980_);
    return v___x_2981_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(
    mut v_t_2982_: *mut LeanObject,
    mut v_eqRhs_2983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2984_: *mut LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(v_t_2982_, v_eqRhs_2983_);
    lean_dec(v_t_2982_);
    return v_res_2984_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(
    mut v_motive_2985_: *mut LeanObject,
    mut v_t_2986_: *mut LeanObject,
    mut v_h_2987_: *mut LeanObject,
    mut v_eqRhs_2988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2986_, v_eqRhs_2988_);
    return v___x_2989_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(
    mut v_motive_2990_: *mut LeanObject,
    mut v_t_2991_: *mut LeanObject,
    mut v_h_2992_: *mut LeanObject,
    mut v_eqRhs_2993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2994_: *mut LeanObject = core::ptr::null_mut();
    v_res_2994_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(
        v_motive_2990_,
        v_t_2991_,
        v_h_2992_,
        v_eqRhs_2993_,
    );
    lean_dec(v_t_2991_);
    return v_res_2994_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(
    mut v_t_2995_: *mut LeanObject,
    mut v_eqBoth_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    v___x_2997_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_2995_, v_eqBoth_2996_);
    return v___x_2997_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(
    mut v_t_2998_: *mut LeanObject,
    mut v_eqBoth_2999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3000_: *mut LeanObject = core::ptr::null_mut();
    v_res_3000_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(v_t_2998_, v_eqBoth_2999_);
    lean_dec(v_t_2998_);
    return v_res_3000_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(
    mut v_motive_3001_: *mut LeanObject,
    mut v_t_3002_: *mut LeanObject,
    mut v_h_3003_: *mut LeanObject,
    mut v_eqBoth_3004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    v___x_3005_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3002_, v_eqBoth_3004_);
    return v___x_3005_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(
    mut v_motive_3006_: *mut LeanObject,
    mut v_t_3007_: *mut LeanObject,
    mut v_h_3008_: *mut LeanObject,
    mut v_eqBoth_3009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3010_: *mut LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(
        v_motive_3006_,
        v_t_3007_,
        v_h_3008_,
        v_eqBoth_3009_,
    );
    lean_dec(v_t_3007_);
    return v_res_3010_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(
    mut v_t_3011_: *mut LeanObject,
    mut v_eqBwd_3012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    v___x_3013_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3011_, v_eqBwd_3012_);
    return v___x_3013_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(
    mut v_t_3014_: *mut LeanObject,
    mut v_eqBwd_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3016_: *mut LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(v_t_3014_, v_eqBwd_3015_);
    lean_dec(v_t_3014_);
    return v_res_3016_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(
    mut v_motive_3017_: *mut LeanObject,
    mut v_t_3018_: *mut LeanObject,
    mut v_h_3019_: *mut LeanObject,
    mut v_eqBwd_3020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    v___x_3021_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3018_, v_eqBwd_3020_);
    return v___x_3021_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(
    mut v_motive_3022_: *mut LeanObject,
    mut v_t_3023_: *mut LeanObject,
    mut v_h_3024_: *mut LeanObject,
    mut v_eqBwd_3025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3026_: *mut LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(
        v_motive_3022_,
        v_t_3023_,
        v_h_3024_,
        v_eqBwd_3025_,
    );
    lean_dec(v_t_3023_);
    return v_res_3026_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(
    mut v_t_3027_: *mut LeanObject,
    mut v_fwd_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    v___x_3029_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3027_, v_fwd_3028_);
    return v___x_3029_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(
    mut v_t_3030_: *mut LeanObject,
    mut v_fwd_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3032_: *mut LeanObject = core::ptr::null_mut();
    v_res_3032_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(v_t_3030_, v_fwd_3031_);
    lean_dec(v_t_3030_);
    return v_res_3032_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(
    mut v_motive_3033_: *mut LeanObject,
    mut v_t_3034_: *mut LeanObject,
    mut v_h_3035_: *mut LeanObject,
    mut v_fwd_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    v___x_3037_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3034_, v_fwd_3036_);
    return v___x_3037_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(
    mut v_motive_3038_: *mut LeanObject,
    mut v_t_3039_: *mut LeanObject,
    mut v_h_3040_: *mut LeanObject,
    mut v_fwd_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(
        v_motive_3038_,
        v_t_3039_,
        v_h_3040_,
        v_fwd_3041_,
    );
    lean_dec(v_t_3039_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(
    mut v_t_3043_: *mut LeanObject,
    mut v_bwd_3044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    v___x_3045_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3043_, v_bwd_3044_);
    return v___x_3045_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(
    mut v_t_3046_: *mut LeanObject,
    mut v_bwd_3047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3048_: *mut LeanObject = core::ptr::null_mut();
    v_res_3048_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(v_t_3046_, v_bwd_3047_);
    lean_dec(v_t_3046_);
    return v_res_3048_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(
    mut v_motive_3049_: *mut LeanObject,
    mut v_t_3050_: *mut LeanObject,
    mut v_h_3051_: *mut LeanObject,
    mut v_bwd_3052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    v___x_3053_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3050_, v_bwd_3052_);
    return v___x_3053_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(
    mut v_motive_3054_: *mut LeanObject,
    mut v_t_3055_: *mut LeanObject,
    mut v_h_3056_: *mut LeanObject,
    mut v_bwd_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3058_: *mut LeanObject = core::ptr::null_mut();
    v_res_3058_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(
        v_motive_3054_,
        v_t_3055_,
        v_h_3056_,
        v_bwd_3057_,
    );
    lean_dec(v_t_3055_);
    return v_res_3058_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(
    mut v_t_3059_: *mut LeanObject,
    mut v_leftRight_3060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    v___x_3061_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3059_, v_leftRight_3060_);
    return v___x_3061_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(
    mut v_t_3062_: *mut LeanObject,
    mut v_leftRight_3063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3064_: *mut LeanObject = core::ptr::null_mut();
    v_res_3064_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(v_t_3062_, v_leftRight_3063_);
    lean_dec(v_t_3062_);
    return v_res_3064_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(
    mut v_motive_3065_: *mut LeanObject,
    mut v_t_3066_: *mut LeanObject,
    mut v_h_3067_: *mut LeanObject,
    mut v_leftRight_3068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    v___x_3069_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3066_, v_leftRight_3068_);
    return v___x_3069_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(
    mut v_motive_3070_: *mut LeanObject,
    mut v_t_3071_: *mut LeanObject,
    mut v_h_3072_: *mut LeanObject,
    mut v_leftRight_3073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3074_: *mut LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(
        v_motive_3070_,
        v_t_3071_,
        v_h_3072_,
        v_leftRight_3073_,
    );
    lean_dec(v_t_3071_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(
    mut v_t_3075_: *mut LeanObject,
    mut v_rightLeft_3076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    v___x_3077_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3075_, v_rightLeft_3076_);
    return v___x_3077_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(
    mut v_t_3078_: *mut LeanObject,
    mut v_rightLeft_3079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3080_: *mut LeanObject = core::ptr::null_mut();
    v_res_3080_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(v_t_3078_, v_rightLeft_3079_);
    lean_dec(v_t_3078_);
    return v_res_3080_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(
    mut v_motive_3081_: *mut LeanObject,
    mut v_t_3082_: *mut LeanObject,
    mut v_h_3083_: *mut LeanObject,
    mut v_rightLeft_3084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    v___x_3085_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3082_, v_rightLeft_3084_);
    return v___x_3085_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(
    mut v_motive_3086_: *mut LeanObject,
    mut v_t_3087_: *mut LeanObject,
    mut v_h_3088_: *mut LeanObject,
    mut v_rightLeft_3089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3090_: *mut LeanObject = core::ptr::null_mut();
    v_res_3090_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(
        v_motive_3086_,
        v_t_3087_,
        v_h_3088_,
        v_rightLeft_3089_,
    );
    lean_dec(v_t_3087_);
    return v_res_3090_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(
    mut v_t_3091_: *mut LeanObject,
    mut v_default_3092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3091_, v_default_3092_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(
    mut v_t_3094_: *mut LeanObject,
    mut v_default_3095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3096_: *mut LeanObject = core::ptr::null_mut();
    v_res_3096_ =
        l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(v_t_3094_, v_default_3095_);
    lean_dec(v_t_3094_);
    return v_res_3096_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(
    mut v_motive_3097_: *mut LeanObject,
    mut v_t_3098_: *mut LeanObject,
    mut v_h_3099_: *mut LeanObject,
    mut v_default_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3098_, v_default_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(
    mut v_motive_3102_: *mut LeanObject,
    mut v_t_3103_: *mut LeanObject,
    mut v_h_3104_: *mut LeanObject,
    mut v_default_3105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3106_: *mut LeanObject = core::ptr::null_mut();
    v_res_3106_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(
        v_motive_3102_,
        v_t_3103_,
        v_h_3104_,
        v_default_3105_,
    );
    lean_dec(v_t_3103_);
    return v_res_3106_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(
    mut v_t_3107_: *mut LeanObject,
    mut v_user_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    v___x_3109_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3107_, v_user_3108_);
    return v___x_3109_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(
    mut v_t_3110_: *mut LeanObject,
    mut v_user_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3112_: *mut LeanObject = core::ptr::null_mut();
    v_res_3112_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(v_t_3110_, v_user_3111_);
    lean_dec(v_t_3110_);
    return v_res_3112_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(
    mut v_motive_3113_: *mut LeanObject,
    mut v_t_3114_: *mut LeanObject,
    mut v_h_3115_: *mut LeanObject,
    mut v_user_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    v___x_3117_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_3114_, v_user_3116_);
    return v___x_3117_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(
    mut v_motive_3118_: *mut LeanObject,
    mut v_t_3119_: *mut LeanObject,
    mut v_h_3120_: *mut LeanObject,
    mut v_user_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3122_: *mut LeanObject = core::ptr::null_mut();
    v_res_3122_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(
        v_motive_3118_,
        v_t_3119_,
        v_h_3120_,
        v_user_3121_,
    );
    lean_dec(v_t_3119_);
    return v_res_3122_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(
    mut v_x_3127_: *mut LeanObject,
    mut v_x_3128_: *mut LeanObject,
) -> u8 {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
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
                lean_dec(v___x_3130_);
                lean_dec(v___x_3129_);
                if v___x_3131_ == 0 {
                    return v___x_3131_;
                } else {
                    match lean_obj_tag(v_x_3127_) {
                        0 => {
                            v_gen_3135_ = lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3136_ = lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3135_;
                            v_gen_x27_3134_ = v_gen_3136_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_gen_3137_ = lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3138_ = lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3137_;
                            v_gen_x27_3134_ = v_gen_3138_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_gen_3139_ = lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3140_ = lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3139_;
                            v_gen_x27_3134_ = v_gen_3140_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v_gen_3141_ = lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3142_ = lean_ctor_get_uint8(v_x_3128_, 0 as u32);
                            v_gen_3133_ = v_gen_3141_;
                            v_gen_x27_3134_ = v_gen_3142_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_gen_3143_ = lean_ctor_get_uint8(v_x_3127_, 0 as u32);
                            v_gen_3144_ = lean_ctor_get_uint8(v_x_3128_, 0 as u32);
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
    mut v_x_3145_: *mut LeanObject,
    mut v_x_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3147_: u8 = 0;
    let mut v_r_3148_: *mut LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_3145_, v_x_3146_);
    lean_dec(v_x_3146_);
    lean_dec(v_x_3145_);
    v_r_3148_ = lean_box((v_res_3147_) as usize);
    return v_r_3148_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13()
-> *mut LeanObject {
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    v___x_3172_ = lean_unsigned_to_nat(2);
    v___x_3173_ = lean_nat_to_int(v___x_3172_);
    return v___x_3173_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14()
-> *mut LeanObject {
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    v___x_3174_ = lean_unsigned_to_nat(1);
    v___x_3175_ = lean_nat_to_int(v___x_3174_);
    return v___x_3175_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(
    mut v_x_3200_: *mut LeanObject,
    mut v_prec_3201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gen_3237_: u8 = 0;
    let mut v___y_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gen_3251_: u8 = 0;
    let mut v___y_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gen_3265_: u8 = 0;
    let mut v___y_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: u8 = 0;
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gen_3287_: u8 = 0;
    let mut v___y_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: u8 = 0;
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: u8 = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gen_3309_: u8 = 0;
    let mut v___y_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_3200_) {
                    0 => {
                        v_gen_3237_ = lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3247_ = lean_unsigned_to_nat(1024);
                        v___x_3248_ = lean_nat_dec_le(v___x_3247_, v_prec_3201_);
                        if v___x_3248_ == 0 {
                            v___x_3249_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3239_ = v___x_3249_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3250_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3239_ = v___x_3250_;
                            state = 6;
                            continue;
                        }
                    }
                    1 => {
                        v_gen_3251_ = lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3261_ = lean_unsigned_to_nat(1024);
                        v___x_3262_ = lean_nat_dec_le(v___x_3261_, v_prec_3201_);
                        if v___x_3262_ == 0 {
                            v___x_3263_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3253_ = v___x_3263_;
                            state = 7;
                            continue;
                        } else {
                            v___x_3264_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3253_ = v___x_3264_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        v_gen_3265_ = lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3275_ = lean_unsigned_to_nat(1024);
                        v___x_3276_ = lean_nat_dec_le(v___x_3275_, v_prec_3201_);
                        if v___x_3276_ == 0 {
                            v___x_3277_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3267_ = v___x_3277_;
                            state = 8;
                            continue;
                        } else {
                            v___x_3278_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3267_ = v___x_3278_;
                            state = 8;
                            continue;
                        }
                    }
                    3 => {
                        v___x_3279_ = lean_unsigned_to_nat(1024);
                        v___x_3280_ = lean_nat_dec_le(v___x_3279_, v_prec_3201_);
                        if v___x_3280_ == 0 {
                            v___x_3281_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3217_ = v___x_3281_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3282_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3217_ = v___x_3282_;
                            state = 3;
                            continue;
                        }
                    }
                    4 => {
                        v___x_3283_ = lean_unsigned_to_nat(1024);
                        v___x_3284_ = lean_nat_dec_le(v___x_3283_, v_prec_3201_);
                        if v___x_3284_ == 0 {
                            v___x_3285_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3224_ = v___x_3285_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3286_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3224_ = v___x_3286_;
                            state = 4;
                            continue;
                        }
                    }
                    5 => {
                        v_gen_3287_ = lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3297_ = lean_unsigned_to_nat(1024);
                        v___x_3298_ = lean_nat_dec_le(v___x_3297_, v_prec_3201_);
                        if v___x_3298_ == 0 {
                            v___x_3299_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3289_ = v___x_3299_;
                            state = 9;
                            continue;
                        } else {
                            v___x_3300_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3289_ = v___x_3300_;
                            state = 9;
                            continue;
                        }
                    }
                    6 => {
                        v___x_3301_ = lean_unsigned_to_nat(1024);
                        v___x_3302_ = lean_nat_dec_le(v___x_3301_, v_prec_3201_);
                        if v___x_3302_ == 0 {
                            v___x_3303_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3210_ = v___x_3303_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3304_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3210_ = v___x_3304_;
                            state = 2;
                            continue;
                        }
                    }
                    7 => {
                        v___x_3305_ = lean_unsigned_to_nat(1024);
                        v___x_3306_ = lean_nat_dec_le(v___x_3305_, v_prec_3201_);
                        if v___x_3306_ == 0 {
                            v___x_3307_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3203_ = v___x_3307_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3308_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3203_ = v___x_3308_;
                            state = 1;
                            continue;
                        }
                    }
                    8 => {
                        v_gen_3309_ = lean_ctor_get_uint8(v_x_3200_, 0 as u32);
                        v___x_3319_ = lean_unsigned_to_nat(1024);
                        v___x_3320_ = lean_nat_dec_le(v___x_3319_, v_prec_3201_);
                        if v___x_3320_ == 0 {
                            v___x_3321_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3311_ = v___x_3321_;
                            state = 10;
                            continue;
                        } else {
                            v___x_3322_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3311_ = v___x_3322_;
                            state = 10;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3323_ = lean_unsigned_to_nat(1024);
                        v___x_3324_ = lean_nat_dec_le(v___x_3323_, v_prec_3201_);
                        if v___x_3324_ == 0 {
                            v___x_3325_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_3231_ = v___x_3325_;
                            state = 5;
                            continue;
                        } else {
                            v___x_3326_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_3231_ = v___x_3326_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3204_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1;
                lean_inc(v___y_3203_);
                v___x_3205_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3205_, 0, v___y_3203_);
                lean_ctor_set(v___x_3205_, 1, v___x_3204_);
                v___x_3206_ = 0;
                v___x_3207_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3207_, 0, v___x_3205_);
                lean_ctor_set_uint8(
                    v___x_3207_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3206_,
                );
                v___x_3208_ = l_Repr_addAppParen(v___x_3207_, v_prec_3201_);
                return v___x_3208_;
            }
            2 => {
                v___x_3211_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3;
                lean_inc(v___y_3210_);
                v___x_3212_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3212_, 0, v___y_3210_);
                lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                v___x_3213_ = 0;
                v___x_3214_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3214_, 0, v___x_3212_);
                lean_ctor_set_uint8(
                    v___x_3214_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3213_,
                );
                v___x_3215_ = l_Repr_addAppParen(v___x_3214_, v_prec_3201_);
                return v___x_3215_;
            }
            3 => {
                v___x_3218_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5;
                lean_inc(v___y_3217_);
                v___x_3219_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3219_, 0, v___y_3217_);
                lean_ctor_set(v___x_3219_, 1, v___x_3218_);
                v___x_3220_ = 0;
                v___x_3221_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3221_, 0, v___x_3219_);
                lean_ctor_set_uint8(
                    v___x_3221_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3220_,
                );
                v___x_3222_ = l_Repr_addAppParen(v___x_3221_, v_prec_3201_);
                return v___x_3222_;
            }
            4 => {
                v___x_3225_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7;
                lean_inc(v___y_3224_);
                v___x_3226_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3226_, 0, v___y_3224_);
                lean_ctor_set(v___x_3226_, 1, v___x_3225_);
                v___x_3227_ = 0;
                v___x_3228_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3228_, 0, v___x_3226_);
                lean_ctor_set_uint8(
                    v___x_3228_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3227_,
                );
                v___x_3229_ = l_Repr_addAppParen(v___x_3228_, v_prec_3201_);
                return v___x_3229_;
            }
            5 => {
                v___x_3232_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9;
                lean_inc(v___y_3231_);
                v___x_3233_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3233_, 0, v___y_3231_);
                lean_ctor_set(v___x_3233_, 1, v___x_3232_);
                v___x_3234_ = 0;
                v___x_3235_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3235_, 0, v___x_3233_);
                lean_ctor_set_uint8(
                    v___x_3235_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3234_,
                );
                v___x_3236_ = l_Repr_addAppParen(v___x_3235_, v_prec_3201_);
                return v___x_3236_;
            }
            6 => {
                v___x_3240_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12;
                v___x_3241_ = l_Bool_repr___redArg(v_gen_3237_);
                v___x_3242_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3242_, 0, v___x_3240_);
                lean_ctor_set(v___x_3242_, 1, v___x_3241_);
                lean_inc(v___y_3239_);
                v___x_3243_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3243_, 0, v___y_3239_);
                lean_ctor_set(v___x_3243_, 1, v___x_3242_);
                v___x_3244_ = 0;
                v___x_3245_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3245_, 0, v___x_3243_);
                lean_ctor_set_uint8(
                    v___x_3245_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3244_,
                );
                v___x_3246_ = l_Repr_addAppParen(v___x_3245_, v_prec_3201_);
                return v___x_3246_;
            }
            7 => {
                v___x_3254_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17;
                v___x_3255_ = l_Bool_repr___redArg(v_gen_3251_);
                v___x_3256_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3256_, 0, v___x_3254_);
                lean_ctor_set(v___x_3256_, 1, v___x_3255_);
                lean_inc(v___y_3253_);
                v___x_3257_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3257_, 0, v___y_3253_);
                lean_ctor_set(v___x_3257_, 1, v___x_3256_);
                v___x_3258_ = 0;
                v___x_3259_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3259_, 0, v___x_3257_);
                lean_ctor_set_uint8(
                    v___x_3259_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3258_,
                );
                v___x_3260_ = l_Repr_addAppParen(v___x_3259_, v_prec_3201_);
                return v___x_3260_;
            }
            8 => {
                v___x_3268_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20;
                v___x_3269_ = l_Bool_repr___redArg(v_gen_3265_);
                v___x_3270_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3270_, 0, v___x_3268_);
                lean_ctor_set(v___x_3270_, 1, v___x_3269_);
                lean_inc(v___y_3267_);
                v___x_3271_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3271_, 0, v___y_3267_);
                lean_ctor_set(v___x_3271_, 1, v___x_3270_);
                v___x_3272_ = 0;
                v___x_3273_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3273_, 0, v___x_3271_);
                lean_ctor_set_uint8(
                    v___x_3273_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3272_,
                );
                v___x_3274_ = l_Repr_addAppParen(v___x_3273_, v_prec_3201_);
                return v___x_3274_;
            }
            9 => {
                v___x_3290_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23;
                v___x_3291_ = l_Bool_repr___redArg(v_gen_3287_);
                v___x_3292_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3292_, 0, v___x_3290_);
                lean_ctor_set(v___x_3292_, 1, v___x_3291_);
                lean_inc(v___y_3289_);
                v___x_3293_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3293_, 0, v___y_3289_);
                lean_ctor_set(v___x_3293_, 1, v___x_3292_);
                v___x_3294_ = 0;
                v___x_3295_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3295_, 0, v___x_3293_);
                lean_ctor_set_uint8(
                    v___x_3295_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3294_,
                );
                v___x_3296_ = l_Repr_addAppParen(v___x_3295_, v_prec_3201_);
                return v___x_3296_;
            }
            10 => {
                v___x_3312_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26;
                v___x_3313_ = l_Bool_repr___redArg(v_gen_3309_);
                v___x_3314_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3314_, 0, v___x_3312_);
                lean_ctor_set(v___x_3314_, 1, v___x_3313_);
                lean_inc(v___y_3311_);
                v___x_3315_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3315_, 0, v___y_3311_);
                lean_ctor_set(v___x_3315_, 1, v___x_3314_);
                v___x_3316_ = 0;
                v___x_3317_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3317_, 0, v___x_3315_);
                lean_ctor_set_uint8(
                    v___x_3317_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_3327_: *mut LeanObject,
    mut v_prec_3328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3329_: *mut LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(v_x_3327_, v_prec_3328_);
    lean_dec(v_prec_3328_);
    lean_dec(v_x_3327_);
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
    mut v_x_3362_: *mut LeanObject,
) -> u64 {
    match lean_obj_tag(v_x_3362_) {
        0 => {
            let mut v_gen_3363_: u8 = 0;
            v_gen_3363_ = lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3363_ == 0 {
                let mut v___x_3364_: u64 = 0;
                v___x_3364_ = lean_uint64_once(
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
                v___x_3365_ = lean_uint64_once(
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
            v_gen_3366_ = lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3366_ == 0 {
                let mut v___x_3367_: u64 = 0;
                v___x_3367_ = lean_uint64_once(
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
                v___x_3368_ = lean_uint64_once(
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
            v_gen_3369_ = lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3369_ == 0 {
                let mut v___x_3370_: u64 = 0;
                v___x_3370_ = lean_uint64_once(
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
                v___x_3371_ = lean_uint64_once(
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
            v_gen_3374_ = lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3374_ == 0 {
                let mut v___x_3375_: u64 = 0;
                v___x_3375_ = lean_uint64_once(
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
                v___x_3376_ = lean_uint64_once(
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
            v_gen_3379_ = lean_ctor_get_uint8(v_x_3362_, 0 as u32);
            if v_gen_3379_ == 0 {
                let mut v___x_3380_: u64 = 0;
                v___x_3380_ = lean_uint64_once(
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
                v___x_3381_ = lean_uint64_once(
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
    mut v_x_3383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3384_: u64 = 0;
    let mut v_r_3385_: *mut LeanObject = core::ptr::null_mut();
    v_res_3384_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_3383_);
    lean_dec(v_x_3383_);
    v_r_3385_ = lean_box_uint64(v_res_3384_);
    return v_r_3385_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3() -> *mut LeanObject
{
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = lean_box(0);
    v___x_3394_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2;
    v___x_3395_ = l_Lean_Expr_const___override(v___x_3394_, v___x_3393_);
    return v___x_3395_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4() -> *mut LeanObject
{
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3396_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3,
    );
    v___x_3397_ = lean_unsigned_to_nat(0);
    v___x_3398_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0;
    v___x_3399_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3399_, 0, v___x_3398_);
    lean_ctor_set(v___x_3399_, 1, v___x_3397_);
    lean_ctor_set(v___x_3399_, 2, v___x_3396_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default() -> *mut LeanObject {
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    v___x_3400_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4,
    );
    return v___x_3400_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS() -> *mut LeanObject {
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
    return v___x_3401_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(
    mut v_xs_3402_: *mut LeanObject,
    mut v_ys_3403_: *mut LeanObject,
    mut v_x_3404_: *mut LeanObject,
) -> u8 {
    let mut v_zero_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3406_: u8 = 0;
    let mut v_one_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3405_ = lean_unsigned_to_nat(0);
                v_isZero_3406_ = lean_nat_dec_eq(v_x_3404_, v_zero_3405_);
                if v_isZero_3406_ == 1 {
                    lean_dec(v_x_3404_);
                    return v_isZero_3406_;
                } else {
                    v_one_3407_ = lean_unsigned_to_nat(1);
                    v_n_3408_ = lean_nat_sub(v_x_3404_, v_one_3407_);
                    lean_dec(v_x_3404_);
                    v___x_3409_ = lean_array_fget_borrowed(v_xs_3402_, v_n_3408_);
                    v___x_3410_ = lean_array_fget_borrowed(v_ys_3403_, v_n_3408_);
                    v___x_3411_ = lean_name_eq(v___x_3409_, v___x_3410_);
                    if v___x_3411_ == 0 {
                        lean_dec(v_n_3408_);
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
    mut v_xs_3413_: *mut LeanObject,
    mut v_ys_3414_: *mut LeanObject,
    mut v_x_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3416_: u8 = 0;
    let mut v_r_3417_: *mut LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(
        v_xs_3413_, v_ys_3414_, v_x_3415_,
    );
    lean_dec_ref(v_ys_3414_);
    lean_dec_ref(v_xs_3413_);
    v_r_3417_ = lean_box((v_res_3416_) as usize);
    return v_r_3417_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqCnstrRHS_beq(
    mut v_x_3418_: *mut LeanObject,
    mut v_x_3419_: *mut LeanObject,
) -> u8 {
    let mut v_levelNames_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numMVars_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelNames_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numMVars_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    v_levelNames_3420_ = lean_ctor_get(v_x_3418_, 0);
    v_numMVars_3421_ = lean_ctor_get(v_x_3418_, 1);
    v_expr_3422_ = lean_ctor_get(v_x_3418_, 2);
    v_levelNames_3423_ = lean_ctor_get(v_x_3419_, 0);
    v_numMVars_3424_ = lean_ctor_get(v_x_3419_, 1);
    v_expr_3425_ = lean_ctor_get(v_x_3419_, 2);
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
    mut v_x_3432_: *mut LeanObject,
    mut v_x_3433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3434_: u8 = 0;
    let mut v_r_3435_: *mut LeanObject = core::ptr::null_mut();
    v_res_3434_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_3432_, v_x_3433_);
    lean_dec_ref(v_x_3433_);
    lean_dec_ref(v_x_3432_);
    v_r_3435_ = lean_box((v_res_3434_) as usize);
    return v_r_3435_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(
    mut v_xs_3436_: *mut LeanObject,
    mut v_ys_3437_: *mut LeanObject,
    mut v_hsz_3438_: *mut LeanObject,
    mut v_x_3439_: *mut LeanObject,
    mut v_x_3440_: *mut LeanObject,
) -> u8 {
    let mut v___x_3441_: u8 = 0;
    v___x_3441_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(
        v_xs_3436_, v_ys_3437_, v_x_3439_,
    );
    return v___x_3441_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(
    mut v_xs_3442_: *mut LeanObject,
    mut v_ys_3443_: *mut LeanObject,
    mut v_hsz_3444_: *mut LeanObject,
    mut v_x_3445_: *mut LeanObject,
    mut v_x_3446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3447_: u8 = 0;
    let mut v_r_3448_: *mut LeanObject = core::ptr::null_mut();
    v_res_3447_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(
        v_xs_3442_,
        v_ys_3443_,
        v_hsz_3444_,
        v_x_3445_,
        v_x_3446_,
    );
    lean_dec_ref(v_ys_3443_);
    lean_dec_ref(v_xs_3442_);
    v_r_3448_ = lean_box((v_res_3447_) as usize);
    return v_r_3448_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(
    mut v_a_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    v___x_3452_ = lean_nat_to_int(v_a_3451_);
    return v___x_3452_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_3453_: *mut LeanObject,
    mut v_x_3454_: *mut LeanObject,
    mut v_x_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3455_) == 0 {
                    lean_dec(v_x_3453_);
                    return v_x_3454_;
                } else {
                    v_head_3456_ = lean_ctor_get(v_x_3455_, 0);
                    v_tail_3457_ = lean_ctor_get(v_x_3455_, 1);
                    v_isSharedCheck_3468_ = (!lean_is_exclusive(v_x_3455_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3459_ = v_x_3455_;
                        v_isShared_3460_ = v_isSharedCheck_3468_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3457_);
                        lean_inc(v_head_3456_);
                        lean_dec(v_x_3455_);
                        v___x_3459_ = lean_box(0);
                        v_isShared_3460_ = v_isSharedCheck_3468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3453_);
                if v_isShared_3460_ == 0 {
                    lean_ctor_set_tag(v___x_3459_, 5);
                    lean_ctor_set(v___x_3459_, 1, v_x_3453_);
                    lean_ctor_set(v___x_3459_, 0, v_x_3454_);
                    v___x_3462_ = v___x_3459_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_x_3454_);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_x_3453_);
                    v___x_3462_ = v_reuseFailAlloc_3467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3463_ = lean_unsigned_to_nat(0);
                v___x_3464_ = l_Lean_Name_reprPrec(v_head_3456_, v___x_3463_);
                v___x_3465_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3465_, 0, v___x_3462_);
                lean_ctor_set(v___x_3465_, 1, v___x_3464_);
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
    mut v_x_3469_: *mut LeanObject,
    mut v_x_3470_: *mut LeanObject,
    mut v_x_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3471_) == 0 {
                    lean_dec(v_x_3469_);
                    return v_x_3470_;
                } else {
                    v_head_3472_ = lean_ctor_get(v_x_3471_, 0);
                    v_tail_3473_ = lean_ctor_get(v_x_3471_, 1);
                    v_isSharedCheck_3484_ = (!lean_is_exclusive(v_x_3471_)) as u8;
                    if v_isSharedCheck_3484_ == 0 {
                        v___x_3475_ = v_x_3471_;
                        v_isShared_3476_ = v_isSharedCheck_3484_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3473_);
                        lean_inc(v_head_3472_);
                        lean_dec(v_x_3471_);
                        v___x_3475_ = lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3469_);
                if v_isShared_3476_ == 0 {
                    lean_ctor_set_tag(v___x_3475_, 5);
                    lean_ctor_set(v___x_3475_, 1, v_x_3469_);
                    lean_ctor_set(v___x_3475_, 0, v_x_3470_);
                    v___x_3478_ = v___x_3475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3483_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_x_3470_);
                    lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_x_3469_);
                    v___x_3478_ = v_reuseFailAlloc_3483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3479_ = lean_unsigned_to_nat(0);
                v___x_3480_ = l_Lean_Name_reprPrec(v_head_3472_, v___x_3479_);
                v___x_3481_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3481_, 0, v___x_3478_);
                lean_ctor_set(v___x_3481_, 1, v___x_3480_);
                v___x_3482_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_3469_, v___x_3481_, v_tail_3473_);
                return v___x_3482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(
    mut v___y_3485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3486_ = lean_unsigned_to_nat(0);
    v___x_3487_ = l_Lean_Name_reprPrec(v___y_3485_, v___x_3486_);
    return v___x_3487_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(
    mut v_x_3488_: *mut LeanObject,
    mut v_x_3489_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3488_) == 0 {
        let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3489_);
        v___x_3490_ = lean_box(0);
        return v___x_3490_;
    } else {
        let mut v_tail_3491_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3491_ = lean_ctor_get(v_x_3488_, 1);
        if lean_obj_tag(v_tail_3491_) == 0 {
            let mut v_head_3492_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3489_);
            v_head_3492_ = lean_ctor_get(v_x_3488_, 0);
            lean_inc(v_head_3492_);
            lean_dec_ref_known(v_x_3488_, 2);
            v___x_3493_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_3492_);
            return v___x_3493_;
        } else {
            let mut v_head_3494_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_3491_);
            v_head_3494_ = lean_ctor_get(v_x_3488_, 0);
            lean_inc(v_head_3494_);
            lean_dec_ref_known(v_x_3488_, 2);
            v___x_3495_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_3494_);
            v___x_3496_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_3489_, v___x_3495_, v_tail_3491_);
            return v___x_3496_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0;
    v___x_3506_ = lean_string_length(v___x_3505_);
    return v___x_3506_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v___x_3507_ = lean_obj_once(
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
    mut v_xs_3516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    v___x_3517_ = lean_array_get_size(v_xs_3516_);
    v___x_3518_ = lean_unsigned_to_nat(0);
    v___x_3519_ = lean_nat_dec_eq(v___x_3517_, v___x_3518_);
    if v___x_3519_ == 0 {
        let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
        v___x_3520_ = lean_array_to_list(v_xs_3516_);
        v___x_3521_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3;
        v___x_3522_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_3520_, v___x_3521_);
        v___x_3523_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
        v___x_3524_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7;
        v___x_3525_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3525_, 0, v___x_3524_);
        lean_ctor_set(v___x_3525_, 1, v___x_3522_);
        v___x_3526_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8;
        v___x_3527_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3527_, 0, v___x_3525_);
        lean_ctor_set(v___x_3527_, 1, v___x_3526_);
        v___x_3528_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_3528_, 0, v___x_3523_);
        lean_ctor_set(v___x_3528_, 1, v___x_3527_);
        v___x_3529_ = l_Std_Format_fill(v___x_3528_);
        return v___x_3529_;
    } else {
        let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_3516_);
        v___x_3530_ =
            l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10;
        return v___x_3530_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7() -> *mut LeanObject
{
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    v___x_3544_ = lean_unsigned_to_nat(14);
    v___x_3545_ = lean_nat_to_int(v___x_3544_);
    return v___x_3545_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    v___x_3549_ = lean_unsigned_to_nat(12);
    v___x_3550_ = lean_nat_to_int(v___x_3549_);
    return v___x_3550_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    v___x_3554_ = lean_unsigned_to_nat(8);
    v___x_3555_ = lean_nat_to_int(v___x_3554_);
    return v___x_3555_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    v___x_3557_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0;
    v___x_3558_ = lean_string_length(v___x_3557_);
    return v___x_3558_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16()
-> *mut LeanObject {
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    v___x_3559_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15,
    );
    v___x_3560_ = lean_nat_to_int(v___x_3559_);
    return v___x_3560_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(
    mut v_x_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelNames_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numMVars_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    v_levelNames_3566_ = lean_ctor_get(v_x_3565_, 0);
    lean_inc_ref(v_levelNames_3566_);
    v_numMVars_3567_ = lean_ctor_get(v_x_3565_, 1);
    lean_inc(v_numMVars_3567_);
    v_expr_3568_ = lean_ctor_get(v_x_3565_, 2);
    lean_inc_ref(v_expr_3568_);
    lean_dec_ref(v_x_3565_);
    v___x_3569_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5;
    v___x_3570_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6;
    v___x_3571_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7,
    );
    v___x_3572_ =
        l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_3566_);
    v___x_3573_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3573_, 0, v___x_3571_);
    lean_ctor_set(v___x_3573_, 1, v___x_3572_);
    v___x_3574_ = 0;
    v___x_3575_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3575_, 0, v___x_3573_);
    lean_ctor_set_uint8(
        v___x_3575_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    v___x_3576_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3576_, 0, v___x_3570_);
    lean_ctor_set(v___x_3576_, 1, v___x_3575_);
    v___x_3577_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2;
    v___x_3578_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3578_, 0, v___x_3576_);
    lean_ctor_set(v___x_3578_, 1, v___x_3577_);
    v___x_3579_ = lean_box(1);
    v___x_3580_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3580_, 0, v___x_3578_);
    lean_ctor_set(v___x_3580_, 1, v___x_3579_);
    v___x_3581_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9;
    v___x_3582_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3582_, 0, v___x_3580_);
    lean_ctor_set(v___x_3582_, 1, v___x_3581_);
    v___x_3583_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3583_, 0, v___x_3582_);
    lean_ctor_set(v___x_3583_, 1, v___x_3569_);
    v___x_3584_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10,
    );
    v___x_3585_ = l_Nat_reprFast(v_numMVars_3567_);
    v___x_3586_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3586_, 0, v___x_3585_);
    v___x_3587_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3587_, 0, v___x_3584_);
    lean_ctor_set(v___x_3587_, 1, v___x_3586_);
    v___x_3588_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3588_, 0, v___x_3587_);
    lean_ctor_set_uint8(
        v___x_3588_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    v___x_3589_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3589_, 0, v___x_3583_);
    lean_ctor_set(v___x_3589_, 1, v___x_3588_);
    v___x_3590_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3590_, 0, v___x_3589_);
    lean_ctor_set(v___x_3590_, 1, v___x_3577_);
    v___x_3591_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3591_, 0, v___x_3590_);
    lean_ctor_set(v___x_3591_, 1, v___x_3579_);
    v___x_3592_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12;
    v___x_3593_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3593_, 0, v___x_3591_);
    lean_ctor_set(v___x_3593_, 1, v___x_3592_);
    v___x_3594_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3594_, 0, v___x_3593_);
    lean_ctor_set(v___x_3594_, 1, v___x_3569_);
    v___x_3595_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13,
    );
    v___x_3596_ = lean_unsigned_to_nat(0);
    v___x_3597_ = l_Lean_instReprExpr_repr(v_expr_3568_, v___x_3596_);
    v___x_3598_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3598_, 0, v___x_3595_);
    lean_ctor_set(v___x_3598_, 1, v___x_3597_);
    v___x_3599_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3599_, 0, v___x_3598_);
    lean_ctor_set_uint8(
        v___x_3599_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    v___x_3600_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3600_, 0, v___x_3594_);
    lean_ctor_set(v___x_3600_, 1, v___x_3599_);
    v___x_3601_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once),
        _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16,
    );
    v___x_3602_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17;
    v___x_3603_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3603_, 0, v___x_3602_);
    lean_ctor_set(v___x_3603_, 1, v___x_3600_);
    v___x_3604_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18;
    v___x_3605_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3605_, 0, v___x_3603_);
    lean_ctor_set(v___x_3605_, 1, v___x_3604_);
    v___x_3606_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3606_, 0, v___x_3601_);
    lean_ctor_set(v___x_3606_, 1, v___x_3605_);
    v___x_3607_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3607_, 0, v___x_3606_);
    lean_ctor_set_uint8(
        v___x_3607_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3574_,
    );
    return v___x_3607_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprCnstrRHS_repr(
    mut v_x_3608_: *mut LeanObject,
    mut v_prec_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    v___x_3610_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_3608_);
    return v___x_3610_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(
    mut v_x_3611_: *mut LeanObject,
    mut v_prec_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3613_: *mut LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_3611_, v_prec_3612_);
    lean_dec(v_prec_3612_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(
    mut v_x_3616_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3616_) {
        0 => {
            let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
            v___x_3617_ = lean_unsigned_to_nat(0);
            return v___x_3617_;
        }
        1 => {
            let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
            v___x_3618_ = lean_unsigned_to_nat(1);
            return v___x_3618_;
        }
        2 => {
            let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
            v___x_3619_ = lean_unsigned_to_nat(2);
            return v___x_3619_;
        }
        3 => {
            let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
            v___x_3620_ = lean_unsigned_to_nat(3);
            return v___x_3620_;
        }
        4 => {
            let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
            v___x_3621_ = lean_unsigned_to_nat(4);
            return v___x_3621_;
        }
        5 => {
            let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
            v___x_3622_ = lean_unsigned_to_nat(5);
            return v___x_3622_;
        }
        6 => {
            let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
            v___x_3623_ = lean_unsigned_to_nat(6);
            return v___x_3623_;
        }
        7 => {
            let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
            v___x_3624_ = lean_unsigned_to_nat(7);
            return v___x_3624_;
        }
        8 => {
            let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
            v___x_3625_ = lean_unsigned_to_nat(8);
            return v___x_3625_;
        }
        9 => {
            let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
            v___x_3626_ = lean_unsigned_to_nat(9);
            return v___x_3626_;
        }
        _ => {
            let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
            v___x_3627_ = lean_unsigned_to_nat(10);
            return v___x_3627_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(
    mut v_x_3628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3629_: *mut LeanObject = core::ptr::null_mut();
    v_res_3629_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_3628_);
    lean_dec_ref(v_x_3628_);
    return v_res_3629_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(
    mut v_t_3630_: *mut LeanObject,
    mut v_k_3631_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_3630_) {
        0 => {
            let mut v_lhs_3632_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_3633_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_3632_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc(v_lhs_3632_);
            v_rhs_3633_ = lean_ctor_get(v_t_3630_, 1);
            lean_inc_ref(v_rhs_3633_);
            lean_dec_ref_known(v_t_3630_, 2);
            v___x_3634_ = lean_apply_2(v_k_3631_, v_lhs_3632_, v_rhs_3633_);
            return v___x_3634_;
        }
        1 => {
            let mut v_lhs_3635_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_3636_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_3635_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc(v_lhs_3635_);
            v_rhs_3636_ = lean_ctor_get(v_t_3630_, 1);
            lean_inc_ref(v_rhs_3636_);
            lean_dec_ref_known(v_t_3630_, 2);
            v___x_3637_ = lean_apply_2(v_k_3631_, v_lhs_3635_, v_rhs_3636_);
            return v___x_3637_;
        }
        2 => {
            let mut v_lhs_3638_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_3639_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_3638_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc(v_lhs_3638_);
            v_n_3639_ = lean_ctor_get(v_t_3630_, 1);
            lean_inc(v_n_3639_);
            lean_dec_ref_known(v_t_3630_, 2);
            v___x_3640_ = lean_apply_2(v_k_3631_, v_lhs_3638_, v_n_3639_);
            return v___x_3640_;
        }
        3 => {
            let mut v_lhs_3641_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_3642_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_3641_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc(v_lhs_3641_);
            v_n_3642_ = lean_ctor_get(v_t_3630_, 1);
            lean_inc(v_n_3642_);
            lean_dec_ref_known(v_t_3630_, 2);
            v___x_3643_ = lean_apply_2(v_k_3631_, v_lhs_3641_, v_n_3642_);
            return v___x_3643_;
        }
        6 => {
            let mut v_bvarIdx_3644_: *mut LeanObject = core::ptr::null_mut();
            let mut v_strict_3645_: u8 = 0;
            let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
            v_bvarIdx_3644_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc(v_bvarIdx_3644_);
            v_strict_3645_ = lean_ctor_get_uint8(
                v_t_3630_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_3630_, 1);
            v___x_3646_ = lean_box((v_strict_3645_) as usize);
            v___x_3647_ = lean_apply_2(v_k_3631_, v_bvarIdx_3644_, v___x_3646_);
            return v___x_3647_;
        }
        8 => {
            let mut v_e_3648_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
            v_e_3648_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc_ref(v_e_3648_);
            lean_dec_ref_known(v_t_3630_, 1);
            v___x_3649_ = lean_apply_1(v_k_3631_, v_e_3648_);
            return v___x_3649_;
        }
        9 => {
            let mut v_e_3650_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
            v_e_3650_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc_ref(v_e_3650_);
            lean_dec_ref_known(v_t_3630_, 1);
            v___x_3651_ = lean_apply_1(v_k_3631_, v_e_3650_);
            return v___x_3651_;
        }
        10 => {
            let mut v_bvarIdx_3652_: *mut LeanObject = core::ptr::null_mut();
            let mut v_strict_3653_: u8 = 0;
            let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
            v_bvarIdx_3652_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc(v_bvarIdx_3652_);
            v_strict_3653_ = lean_ctor_get_uint8(
                v_t_3630_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_3630_, 1);
            v___x_3654_ = lean_box((v_strict_3653_) as usize);
            v___x_3655_ = lean_apply_2(v_k_3631_, v_bvarIdx_3652_, v___x_3654_);
            return v___x_3655_;
        }
        _ => {
            let mut v_n_3656_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
            v_n_3656_ = lean_ctor_get(v_t_3630_, 0);
            lean_inc(v_n_3656_);
            lean_dec_ref(v_t_3630_);
            v___x_3657_ = lean_apply_1(v_k_3631_, v_n_3656_);
            return v___x_3657_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(
    mut v_motive_3658_: *mut LeanObject,
    mut v_ctorIdx_3659_: *mut LeanObject,
    mut v_t_3660_: *mut LeanObject,
    mut v_h_3661_: *mut LeanObject,
    mut v_k_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    v___x_3663_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3660_, v_k_3662_);
    return v___x_3663_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(
    mut v_motive_3664_: *mut LeanObject,
    mut v_ctorIdx_3665_: *mut LeanObject,
    mut v_t_3666_: *mut LeanObject,
    mut v_h_3667_: *mut LeanObject,
    mut v_k_3668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3669_: *mut LeanObject = core::ptr::null_mut();
    v_res_3669_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(
        v_motive_3664_,
        v_ctorIdx_3665_,
        v_t_3666_,
        v_h_3667_,
        v_k_3668_,
    );
    lean_dec(v_ctorIdx_3665_);
    return v_res_3669_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(
    mut v_t_3670_: *mut LeanObject,
    mut v_notDefEq_3671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    v___x_3672_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3670_, v_notDefEq_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(
    mut v_motive_3673_: *mut LeanObject,
    mut v_t_3674_: *mut LeanObject,
    mut v_h_3675_: *mut LeanObject,
    mut v_notDefEq_3676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3677_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3674_, v_notDefEq_3676_);
    return v___x_3677_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(
    mut v_t_3678_: *mut LeanObject,
    mut v_defEq_3679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    v___x_3680_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3678_, v_defEq_3679_);
    return v___x_3680_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(
    mut v_motive_3681_: *mut LeanObject,
    mut v_t_3682_: *mut LeanObject,
    mut v_h_3683_: *mut LeanObject,
    mut v_defEq_3684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    v___x_3685_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3682_, v_defEq_3684_);
    return v___x_3685_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(
    mut v_t_3686_: *mut LeanObject,
    mut v_sizeLt_3687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    v___x_3688_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3686_, v_sizeLt_3687_);
    return v___x_3688_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(
    mut v_motive_3689_: *mut LeanObject,
    mut v_t_3690_: *mut LeanObject,
    mut v_h_3691_: *mut LeanObject,
    mut v_sizeLt_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    v___x_3693_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3690_, v_sizeLt_3692_);
    return v___x_3693_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(
    mut v_t_3694_: *mut LeanObject,
    mut v_depthLt_3695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    v___x_3696_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3694_, v_depthLt_3695_);
    return v___x_3696_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(
    mut v_motive_3697_: *mut LeanObject,
    mut v_t_3698_: *mut LeanObject,
    mut v_h_3699_: *mut LeanObject,
    mut v_depthLt_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3701_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3698_, v_depthLt_3700_);
    return v___x_3701_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(
    mut v_t_3702_: *mut LeanObject,
    mut v_genLt_3703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    v___x_3704_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3702_, v_genLt_3703_);
    return v___x_3704_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(
    mut v_motive_3705_: *mut LeanObject,
    mut v_t_3706_: *mut LeanObject,
    mut v_h_3707_: *mut LeanObject,
    mut v_genLt_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    v___x_3709_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3706_, v_genLt_3708_);
    return v___x_3709_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(
    mut v_t_3710_: *mut LeanObject,
    mut v_isGround_3711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    v___x_3712_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3710_, v_isGround_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(
    mut v_motive_3713_: *mut LeanObject,
    mut v_t_3714_: *mut LeanObject,
    mut v_h_3715_: *mut LeanObject,
    mut v_isGround_3716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    v___x_3717_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3714_, v_isGround_3716_);
    return v___x_3717_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(
    mut v_t_3718_: *mut LeanObject,
    mut v_isValue_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3720_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3718_, v_isValue_3719_);
    return v___x_3720_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(
    mut v_motive_3721_: *mut LeanObject,
    mut v_t_3722_: *mut LeanObject,
    mut v_h_3723_: *mut LeanObject,
    mut v_isValue_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    v___x_3725_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3722_, v_isValue_3724_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(
    mut v_t_3726_: *mut LeanObject,
    mut v_maxInsts_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    v___x_3728_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3726_, v_maxInsts_3727_);
    return v___x_3728_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(
    mut v_motive_3729_: *mut LeanObject,
    mut v_t_3730_: *mut LeanObject,
    mut v_h_3731_: *mut LeanObject,
    mut v_maxInsts_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    v___x_3733_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3730_, v_maxInsts_3732_);
    return v___x_3733_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(
    mut v_t_3734_: *mut LeanObject,
    mut v_guard_3735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    v___x_3736_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3734_, v_guard_3735_);
    return v___x_3736_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(
    mut v_motive_3737_: *mut LeanObject,
    mut v_t_3738_: *mut LeanObject,
    mut v_h_3739_: *mut LeanObject,
    mut v_guard_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    v___x_3741_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3738_, v_guard_3740_);
    return v___x_3741_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(
    mut v_t_3742_: *mut LeanObject,
    mut v_check_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    v___x_3744_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3742_, v_check_3743_);
    return v___x_3744_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(
    mut v_motive_3745_: *mut LeanObject,
    mut v_t_3746_: *mut LeanObject,
    mut v_h_3747_: *mut LeanObject,
    mut v_check_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_3749_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3746_, v_check_3748_);
    return v___x_3749_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(
    mut v_t_3750_: *mut LeanObject,
    mut v_notValue_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    v___x_3752_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3750_, v_notValue_3751_);
    return v___x_3752_;
}
pub unsafe fn l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(
    mut v_motive_3753_: *mut LeanObject,
    mut v_t_3754_: *mut LeanObject,
    mut v_h_3755_: *mut LeanObject,
    mut v_notValue_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    v___x_3757_ =
        l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_3754_, v_notValue_3756_);
    return v___x_3757_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0()
-> *mut LeanObject {
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    v___x_3758_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
    v___x_3759_ = lean_unsigned_to_nat(0);
    v___x_3760_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3760_, 0, v___x_3759_);
    lean_ctor_set(v___x_3760_, 1, v___x_3758_);
    return v___x_3760_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default()
-> *mut LeanObject {
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    v___x_3761_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint() -> *mut LeanObject {
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
    return v___x_3762_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(
    mut v_x_3829_: *mut LeanObject,
    mut v_prec_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___y_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3856_: u8 = 0;
    let mut v_lhs_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___y_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_lhs_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3887_: u8 = 0;
    let mut v___y_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut v_lhs_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___y_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_n_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___y_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: u8 = 0;
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3957_: u8 = 0;
    let mut v_bvarIdx_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3961_: u8 = 0;
    let mut v___y_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: u8 = 0;
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_bvarIdx_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3980_: u8 = 0;
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___y_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut v_n_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___y_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v_e_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvarIdx_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4057_: u8 = 0;
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___y_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_3829_) {
                    0 => {
                        v_lhs_3831_ = lean_ctor_get(v_x_3829_, 0);
                        v_rhs_3832_ = lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3856_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3856_ == 0 {
                            v___x_3834_ = v_x_3829_;
                            v_isShared_3835_ = v_isSharedCheck_3856_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_rhs_3832_);
                            lean_inc(v_lhs_3831_);
                            lean_dec(v_x_3829_);
                            v___x_3834_ = lean_box(0);
                            v_isShared_3835_ = v_isSharedCheck_3856_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_lhs_3857_ = lean_ctor_get(v_x_3829_, 0);
                        v_rhs_3858_ = lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3882_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3882_ == 0 {
                            v___x_3860_ = v_x_3829_;
                            v_isShared_3861_ = v_isSharedCheck_3882_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_rhs_3858_);
                            lean_inc(v_lhs_3857_);
                            lean_dec(v_x_3829_);
                            v___x_3860_ = lean_box(0);
                            v_isShared_3861_ = v_isSharedCheck_3882_;
                            state = 4;
                            continue;
                        }
                    }
                    2 => {
                        v_lhs_3883_ = lean_ctor_get(v_x_3829_, 0);
                        v_n_3884_ = lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3909_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3909_ == 0 {
                            v___x_3886_ = v_x_3829_;
                            v_isShared_3887_ = v_isSharedCheck_3909_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_n_3884_);
                            lean_inc(v_lhs_3883_);
                            lean_dec(v_x_3829_);
                            v___x_3886_ = lean_box(0);
                            v_isShared_3887_ = v_isSharedCheck_3909_;
                            state = 7;
                            continue;
                        }
                    }
                    3 => {
                        v_lhs_3910_ = lean_ctor_get(v_x_3829_, 0);
                        v_n_3911_ = lean_ctor_get(v_x_3829_, 1);
                        v_isSharedCheck_3936_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3936_ == 0 {
                            v___x_3913_ = v_x_3829_;
                            v_isShared_3914_ = v_isSharedCheck_3936_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_n_3911_);
                            lean_inc(v_lhs_3910_);
                            lean_dec(v_x_3829_);
                            v___x_3913_ = lean_box(0);
                            v_isShared_3914_ = v_isSharedCheck_3936_;
                            state = 10;
                            continue;
                        }
                    }
                    4 => {
                        v_n_3937_ = lean_ctor_get(v_x_3829_, 0);
                        v_isSharedCheck_3957_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3957_ == 0 {
                            v___x_3939_ = v_x_3829_;
                            v_isShared_3940_ = v_isSharedCheck_3957_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_n_3937_);
                            lean_dec(v_x_3829_);
                            v___x_3939_ = lean_box(0);
                            v_isShared_3940_ = v_isSharedCheck_3957_;
                            state = 13;
                            continue;
                        }
                    }
                    5 => {
                        v_bvarIdx_3958_ = lean_ctor_get(v_x_3829_, 0);
                        v_isSharedCheck_3978_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_3978_ == 0 {
                            v___x_3960_ = v_x_3829_;
                            v_isShared_3961_ = v_isSharedCheck_3978_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_bvarIdx_3958_);
                            lean_dec(v_x_3829_);
                            v___x_3960_ = lean_box(0);
                            v_isShared_3961_ = v_isSharedCheck_3978_;
                            state = 16;
                            continue;
                        }
                    }
                    6 => {
                        v_bvarIdx_3979_ = lean_ctor_get(v_x_3829_, 0);
                        v_strict_3980_ = lean_ctor_get_uint8(
                            v_x_3829_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        v_isSharedCheck_4004_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_4004_ == 0 {
                            v___x_3982_ = v_x_3829_;
                            v_isShared_3983_ = v_isSharedCheck_4004_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_bvarIdx_3979_);
                            lean_dec(v_x_3829_);
                            v___x_3982_ = lean_box(0);
                            v_isShared_3983_ = v_isSharedCheck_4004_;
                            state = 19;
                            continue;
                        }
                    }
                    7 => {
                        v_n_4005_ = lean_ctor_get(v_x_3829_, 0);
                        v_isSharedCheck_4025_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_4025_ == 0 {
                            v___x_4007_ = v_x_3829_;
                            v_isShared_4008_ = v_isSharedCheck_4025_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_n_4005_);
                            lean_dec(v_x_3829_);
                            v___x_4007_ = lean_box(0);
                            v_isShared_4008_ = v_isSharedCheck_4025_;
                            state = 22;
                            continue;
                        }
                    }
                    8 => {
                        v_e_4026_ = lean_ctor_get(v_x_3829_, 0);
                        lean_inc_ref(v_e_4026_);
                        lean_dec_ref_known(v_x_3829_, 1);
                        v___x_4037_ = lean_unsigned_to_nat(1024);
                        v___x_4038_ = lean_nat_dec_le(v___x_4037_, v_prec_3830_);
                        if v___x_4038_ == 0 {
                            v___x_4039_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_4028_ = v___x_4039_;
                            state = 25;
                            continue;
                        } else {
                            v___x_4040_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_4028_ = v___x_4040_;
                            state = 25;
                            continue;
                        }
                    }
                    9 => {
                        v_e_4041_ = lean_ctor_get(v_x_3829_, 0);
                        lean_inc_ref(v_e_4041_);
                        lean_dec_ref_known(v_x_3829_, 1);
                        v___x_4052_ = lean_unsigned_to_nat(1024);
                        v___x_4053_ = lean_nat_dec_le(v___x_4052_, v_prec_3830_);
                        if v___x_4053_ == 0 {
                            v___x_4054_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
                            v___y_4043_ = v___x_4054_;
                            state = 26;
                            continue;
                        } else {
                            v___x_4055_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once), _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
                            v___y_4043_ = v___x_4055_;
                            state = 26;
                            continue;
                        }
                    }
                    _ => {
                        v_bvarIdx_4056_ = lean_ctor_get(v_x_3829_, 0);
                        v_strict_4057_ = lean_ctor_get_uint8(
                            v_x_3829_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        v_isSharedCheck_4081_ = (!lean_is_exclusive(v_x_3829_)) as u8;
                        if v_isSharedCheck_4081_ == 0 {
                            v___x_4059_ = v_x_3829_;
                            v_isShared_4060_ = v_isSharedCheck_4081_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_bvarIdx_4056_);
                            lean_dec(v_x_3829_);
                            v___x_4059_ = lean_box(0);
                            v_isShared_4060_ = v_isSharedCheck_4081_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3852_ = lean_unsigned_to_nat(1024);
                v___x_3853_ = lean_nat_dec_le(v___x_3852_, v_prec_3830_);
                if v___x_3853_ == 0 {
                    v___x_3854_ = lean_obj_once(
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
                    v___x_3855_ = lean_obj_once(
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
                v___x_3838_ = lean_box(1);
                v___x_3839_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2;
                v___x_3840_ = l_Nat_reprFast(v_lhs_3831_);
                v___x_3841_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3841_, 0, v___x_3840_);
                if v_isShared_3835_ == 0 {
                    lean_ctor_set_tag(v___x_3834_, 5);
                    lean_ctor_set(v___x_3834_, 1, v___x_3841_);
                    lean_ctor_set(v___x_3834_, 0, v___x_3839_);
                    v___x_3843_ = v___x_3834_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3839_);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3841_);
                    v___x_3843_ = v_reuseFailAlloc_3851_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3844_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3844_, 0, v___x_3843_);
                lean_ctor_set(v___x_3844_, 1, v___x_3838_);
                v___x_3845_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_3832_);
                v___x_3846_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3846_, 0, v___x_3844_);
                lean_ctor_set(v___x_3846_, 1, v___x_3845_);
                lean_inc(v___y_3837_);
                v___x_3847_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3847_, 0, v___y_3837_);
                lean_ctor_set(v___x_3847_, 1, v___x_3846_);
                v___x_3848_ = 0;
                v___x_3849_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3849_, 0, v___x_3847_);
                lean_ctor_set_uint8(
                    v___x_3849_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3848_,
                );
                v___x_3850_ = l_Repr_addAppParen(v___x_3849_, v_prec_3830_);
                return v___x_3850_;
            }
            4 => {
                v___x_3878_ = lean_unsigned_to_nat(1024);
                v___x_3879_ = lean_nat_dec_le(v___x_3878_, v_prec_3830_);
                if v___x_3879_ == 0 {
                    v___x_3880_ = lean_obj_once(
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
                    v___x_3881_ = lean_obj_once(
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
                v___x_3864_ = lean_box(1);
                v___x_3865_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5;
                v___x_3866_ = l_Nat_reprFast(v_lhs_3857_);
                v___x_3867_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3867_, 0, v___x_3866_);
                if v_isShared_3861_ == 0 {
                    lean_ctor_set_tag(v___x_3860_, 5);
                    lean_ctor_set(v___x_3860_, 1, v___x_3867_);
                    lean_ctor_set(v___x_3860_, 0, v___x_3865_);
                    v___x_3869_ = v___x_3860_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3877_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3865_);
                    lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3867_);
                    v___x_3869_ = v_reuseFailAlloc_3877_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3870_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3870_, 0, v___x_3869_);
                lean_ctor_set(v___x_3870_, 1, v___x_3864_);
                v___x_3871_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_3858_);
                v___x_3872_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3872_, 0, v___x_3870_);
                lean_ctor_set(v___x_3872_, 1, v___x_3871_);
                lean_inc(v___y_3863_);
                v___x_3873_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3873_, 0, v___y_3863_);
                lean_ctor_set(v___x_3873_, 1, v___x_3872_);
                v___x_3874_ = 0;
                v___x_3875_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3875_, 0, v___x_3873_);
                lean_ctor_set_uint8(
                    v___x_3875_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3874_,
                );
                v___x_3876_ = l_Repr_addAppParen(v___x_3875_, v_prec_3830_);
                return v___x_3876_;
            }
            7 => {
                v___x_3905_ = lean_unsigned_to_nat(1024);
                v___x_3906_ = lean_nat_dec_le(v___x_3905_, v_prec_3830_);
                if v___x_3906_ == 0 {
                    v___x_3907_ = lean_obj_once(
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
                    v___x_3908_ = lean_obj_once(
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
                v___x_3890_ = lean_box(1);
                v___x_3891_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8;
                v___x_3892_ = l_Nat_reprFast(v_lhs_3883_);
                v___x_3893_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3893_, 0, v___x_3892_);
                if v_isShared_3887_ == 0 {
                    lean_ctor_set_tag(v___x_3886_, 5);
                    lean_ctor_set(v___x_3886_, 1, v___x_3893_);
                    lean_ctor_set(v___x_3886_, 0, v___x_3891_);
                    v___x_3895_ = v___x_3886_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3891_);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3893_);
                    v___x_3895_ = v_reuseFailAlloc_3904_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3896_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3896_, 0, v___x_3895_);
                lean_ctor_set(v___x_3896_, 1, v___x_3890_);
                v___x_3897_ = l_Nat_reprFast(v_n_3884_);
                v___x_3898_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                v___x_3899_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3899_, 0, v___x_3896_);
                lean_ctor_set(v___x_3899_, 1, v___x_3898_);
                lean_inc(v___y_3889_);
                v___x_3900_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3900_, 0, v___y_3889_);
                lean_ctor_set(v___x_3900_, 1, v___x_3899_);
                v___x_3901_ = 0;
                v___x_3902_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3902_, 0, v___x_3900_);
                lean_ctor_set_uint8(
                    v___x_3902_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3901_,
                );
                v___x_3903_ = l_Repr_addAppParen(v___x_3902_, v_prec_3830_);
                return v___x_3903_;
            }
            10 => {
                v___x_3932_ = lean_unsigned_to_nat(1024);
                v___x_3933_ = lean_nat_dec_le(v___x_3932_, v_prec_3830_);
                if v___x_3933_ == 0 {
                    v___x_3934_ = lean_obj_once(
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
                    v___x_3935_ = lean_obj_once(
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
                v___x_3917_ = lean_box(1);
                v___x_3918_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11;
                v___x_3919_ = l_Nat_reprFast(v_lhs_3910_);
                v___x_3920_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3920_, 0, v___x_3919_);
                if v_isShared_3914_ == 0 {
                    lean_ctor_set_tag(v___x_3913_, 5);
                    lean_ctor_set(v___x_3913_, 1, v___x_3920_);
                    lean_ctor_set(v___x_3913_, 0, v___x_3918_);
                    v___x_3922_ = v___x_3913_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3918_);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3920_);
                    v___x_3922_ = v_reuseFailAlloc_3931_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3923_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3923_, 0, v___x_3922_);
                lean_ctor_set(v___x_3923_, 1, v___x_3917_);
                v___x_3924_ = l_Nat_reprFast(v_n_3911_);
                v___x_3925_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3925_, 0, v___x_3924_);
                v___x_3926_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3926_, 0, v___x_3923_);
                lean_ctor_set(v___x_3926_, 1, v___x_3925_);
                lean_inc(v___y_3916_);
                v___x_3927_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3927_, 0, v___y_3916_);
                lean_ctor_set(v___x_3927_, 1, v___x_3926_);
                v___x_3928_ = 0;
                v___x_3929_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3929_, 0, v___x_3927_);
                lean_ctor_set_uint8(
                    v___x_3929_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3928_,
                );
                v___x_3930_ = l_Repr_addAppParen(v___x_3929_, v_prec_3830_);
                return v___x_3930_;
            }
            13 => {
                v___x_3953_ = lean_unsigned_to_nat(1024);
                v___x_3954_ = lean_nat_dec_le(v___x_3953_, v_prec_3830_);
                if v___x_3954_ == 0 {
                    v___x_3955_ = lean_obj_once(
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
                    v___x_3956_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_3939_, 3);
                    lean_ctor_set(v___x_3939_, 0, v___x_3944_);
                    v___x_3946_ = v___x_3939_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3952_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3944_);
                    v___x_3946_ = v_reuseFailAlloc_3952_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3947_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3947_, 0, v___x_3943_);
                lean_ctor_set(v___x_3947_, 1, v___x_3946_);
                lean_inc(v___y_3942_);
                v___x_3948_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3948_, 0, v___y_3942_);
                lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = 0;
                v___x_3950_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                lean_ctor_set_uint8(
                    v___x_3950_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3949_,
                );
                v___x_3951_ = l_Repr_addAppParen(v___x_3950_, v_prec_3830_);
                return v___x_3951_;
            }
            16 => {
                v___x_3974_ = lean_unsigned_to_nat(1024);
                v___x_3975_ = lean_nat_dec_le(v___x_3974_, v_prec_3830_);
                if v___x_3975_ == 0 {
                    v___x_3976_ = lean_obj_once(
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
                    v___x_3977_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_3960_, 3);
                    lean_ctor_set(v___x_3960_, 0, v___x_3965_);
                    v___x_3967_ = v___x_3960_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3973_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3965_);
                    v___x_3967_ = v_reuseFailAlloc_3973_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3968_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3968_, 0, v___x_3964_);
                lean_ctor_set(v___x_3968_, 1, v___x_3967_);
                lean_inc(v___y_3963_);
                v___x_3969_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3969_, 0, v___y_3963_);
                lean_ctor_set(v___x_3969_, 1, v___x_3968_);
                v___x_3970_ = 0;
                v___x_3971_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3971_, 0, v___x_3969_);
                lean_ctor_set_uint8(
                    v___x_3971_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3970_,
                );
                v___x_3972_ = l_Repr_addAppParen(v___x_3971_, v_prec_3830_);
                return v___x_3972_;
            }
            19 => {
                v___x_4000_ = lean_unsigned_to_nat(1024);
                v___x_4001_ = lean_nat_dec_le(v___x_4000_, v_prec_3830_);
                if v___x_4001_ == 0 {
                    v___x_4002_ = lean_obj_once(
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
                    v___x_4003_ = lean_obj_once(
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
                v___x_3986_ = lean_box(1);
                v___x_3987_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20;
                v___x_3988_ = l_Nat_reprFast(v_bvarIdx_3979_);
                v___x_3989_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3989_, 0, v___x_3988_);
                v___x_3990_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3990_, 0, v___x_3987_);
                lean_ctor_set(v___x_3990_, 1, v___x_3989_);
                v___x_3991_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3991_, 0, v___x_3990_);
                lean_ctor_set(v___x_3991_, 1, v___x_3986_);
                v___x_3992_ = l_Bool_repr___redArg(v_strict_3980_);
                v___x_3993_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3993_, 0, v___x_3991_);
                lean_ctor_set(v___x_3993_, 1, v___x_3992_);
                lean_inc(v___y_3985_);
                v___x_3994_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3994_, 0, v___y_3985_);
                lean_ctor_set(v___x_3994_, 1, v___x_3993_);
                v___x_3995_ = 0;
                if v_isShared_3983_ == 0 {
                    lean_ctor_set(v___x_3982_, 0, v___x_3994_);
                    v___x_3997_ = v___x_3982_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = lean_alloc_ctor(6, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3994_);
                    v___x_3997_ = v_reuseFailAlloc_3999_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                lean_ctor_set_uint8(
                    v___x_3997_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3995_,
                );
                v___x_3998_ = l_Repr_addAppParen(v___x_3997_, v_prec_3830_);
                return v___x_3998_;
            }
            22 => {
                v___x_4021_ = lean_unsigned_to_nat(1024);
                v___x_4022_ = lean_nat_dec_le(v___x_4021_, v_prec_3830_);
                if v___x_4022_ == 0 {
                    v___x_4023_ = lean_obj_once(
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
                    v___x_4024_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_4007_, 3);
                    lean_ctor_set(v___x_4007_, 0, v___x_4012_);
                    v___x_4014_ = v___x_4007_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4020_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4012_);
                    v___x_4014_ = v_reuseFailAlloc_4020_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_4015_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4015_, 0, v___x_4011_);
                lean_ctor_set(v___x_4015_, 1, v___x_4014_);
                lean_inc(v___y_4010_);
                v___x_4016_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4016_, 0, v___y_4010_);
                lean_ctor_set(v___x_4016_, 1, v___x_4015_);
                v___x_4017_ = 0;
                v___x_4018_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4018_, 0, v___x_4016_);
                lean_ctor_set_uint8(
                    v___x_4018_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4017_,
                );
                v___x_4019_ = l_Repr_addAppParen(v___x_4018_, v_prec_3830_);
                return v___x_4019_;
            }
            25 => {
                v___x_4029_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26;
                v___x_4030_ = lean_unsigned_to_nat(1024);
                v___x_4031_ = l_Lean_instReprExpr_repr(v_e_4026_, v___x_4030_);
                v___x_4032_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4032_, 0, v___x_4029_);
                lean_ctor_set(v___x_4032_, 1, v___x_4031_);
                lean_inc(v___y_4028_);
                v___x_4033_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4033_, 0, v___y_4028_);
                lean_ctor_set(v___x_4033_, 1, v___x_4032_);
                v___x_4034_ = 0;
                v___x_4035_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4035_, 0, v___x_4033_);
                lean_ctor_set_uint8(
                    v___x_4035_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4034_,
                );
                v___x_4036_ = l_Repr_addAppParen(v___x_4035_, v_prec_3830_);
                return v___x_4036_;
            }
            26 => {
                v___x_4044_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29;
                v___x_4045_ = lean_unsigned_to_nat(1024);
                v___x_4046_ = l_Lean_instReprExpr_repr(v_e_4041_, v___x_4045_);
                v___x_4047_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4047_, 0, v___x_4044_);
                lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                lean_inc(v___y_4043_);
                v___x_4048_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4048_, 0, v___y_4043_);
                lean_ctor_set(v___x_4048_, 1, v___x_4047_);
                v___x_4049_ = 0;
                v___x_4050_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4050_, 0, v___x_4048_);
                lean_ctor_set_uint8(
                    v___x_4050_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4049_,
                );
                v___x_4051_ = l_Repr_addAppParen(v___x_4050_, v_prec_3830_);
                return v___x_4051_;
            }
            27 => {
                v___x_4077_ = lean_unsigned_to_nat(1024);
                v___x_4078_ = lean_nat_dec_le(v___x_4077_, v_prec_3830_);
                if v___x_4078_ == 0 {
                    v___x_4079_ = lean_obj_once(
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
                    v___x_4080_ = lean_obj_once(
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
                v___x_4063_ = lean_box(1);
                v___x_4064_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32;
                v___x_4065_ = l_Nat_reprFast(v_bvarIdx_4056_);
                v___x_4066_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4066_, 0, v___x_4065_);
                v___x_4067_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4067_, 0, v___x_4064_);
                lean_ctor_set(v___x_4067_, 1, v___x_4066_);
                v___x_4068_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4068_, 0, v___x_4067_);
                lean_ctor_set(v___x_4068_, 1, v___x_4063_);
                v___x_4069_ = l_Bool_repr___redArg(v_strict_4057_);
                v___x_4070_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4070_, 0, v___x_4068_);
                lean_ctor_set(v___x_4070_, 1, v___x_4069_);
                lean_inc(v___y_4062_);
                v___x_4071_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4071_, 0, v___y_4062_);
                lean_ctor_set(v___x_4071_, 1, v___x_4070_);
                v___x_4072_ = 0;
                if v_isShared_4060_ == 0 {
                    lean_ctor_set_tag(v___x_4059_, 6);
                    lean_ctor_set(v___x_4059_, 0, v___x_4071_);
                    v___x_4074_ = v___x_4059_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = lean_alloc_ctor(6, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4071_);
                    v___x_4074_ = v_reuseFailAlloc_4076_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                lean_ctor_set_uint8(
                    v___x_4074_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_4082_: *mut LeanObject,
    mut v_prec_4083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4084_: *mut LeanObject = core::ptr::null_mut();
    v_res_4084_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_4082_, v_prec_4083_);
    lean_dec(v_prec_4083_);
    return v_res_4084_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(
    mut v_x_4087_: *mut LeanObject,
    mut v_x_4088_: *mut LeanObject,
) -> u8 {
    let mut v_lhs_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_x27_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_x27_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: u8 = 0;
    let mut v_lhs_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_x27_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_x27_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: u8 = 0;
    let mut v___x_4102_: u8 = 0;
    let mut v_bvarIdx_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4105_: u8 = 0;
    let mut v_bvarIdx_x27_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_x27_4107_: u8 = 0;
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: u8 = 0;
    let mut v_lhs_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvarIdx_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4129_: u8 = 0;
    let mut v_bvarIdx_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4131_: u8 = 0;
    let mut v_e_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v_e_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    let mut v_bvarIdx_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4139_: u8 = 0;
    let mut v_bvarIdx_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4141_: u8 = 0;
    let mut v_n_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4109_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_4087_);
                v___x_4110_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_4088_);
                v___x_4111_ = lean_nat_dec_eq(v___x_4109_, v___x_4110_);
                lean_dec(v___x_4110_);
                lean_dec(v___x_4109_);
                if v___x_4111_ == 0 {
                    return v___x_4111_;
                } else {
                    match lean_obj_tag(v_x_4087_) {
                        0 => {
                            v_lhs_4112_ = lean_ctor_get(v_x_4087_, 0);
                            v_rhs_4113_ = lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4114_ = lean_ctor_get(v_x_4088_, 0);
                            v_rhs_4115_ = lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4090_ = v_lhs_4112_;
                            v_rhs_4091_ = v_rhs_4113_;
                            v_lhs_x27_4092_ = v_lhs_4114_;
                            v_rhs_x27_4093_ = v_rhs_4115_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_lhs_4116_ = lean_ctor_get(v_x_4087_, 0);
                            v_rhs_4117_ = lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4118_ = lean_ctor_get(v_x_4088_, 0);
                            v_rhs_4119_ = lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4090_ = v_lhs_4116_;
                            v_rhs_4091_ = v_rhs_4117_;
                            v_lhs_x27_4092_ = v_lhs_4118_;
                            v_rhs_x27_4093_ = v_rhs_4119_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_lhs_4120_ = lean_ctor_get(v_x_4087_, 0);
                            v_n_4121_ = lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4122_ = lean_ctor_get(v_x_4088_, 0);
                            v_n_4123_ = lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4097_ = v_lhs_4120_;
                            v_n_4098_ = v_n_4121_;
                            v_lhs_x27_4099_ = v_lhs_4122_;
                            v_n_x27_4100_ = v_n_4123_;
                            state = 2;
                            continue;
                        }
                        3 => {
                            v_lhs_4124_ = lean_ctor_get(v_x_4087_, 0);
                            v_n_4125_ = lean_ctor_get(v_x_4087_, 1);
                            v_lhs_4126_ = lean_ctor_get(v_x_4088_, 0);
                            v_n_4127_ = lean_ctor_get(v_x_4088_, 1);
                            v_lhs_4097_ = v_lhs_4124_;
                            v_n_4098_ = v_n_4125_;
                            v_lhs_x27_4099_ = v_lhs_4126_;
                            v_n_x27_4100_ = v_n_4127_;
                            state = 2;
                            continue;
                        }
                        6 => {
                            v_bvarIdx_4128_ = lean_ctor_get(v_x_4087_, 0);
                            v_strict_4129_ = lean_ctor_get_uint8(
                                v_x_4087_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4130_ = lean_ctor_get(v_x_4088_, 0);
                            v_strict_4131_ = lean_ctor_get_uint8(
                                v_x_4088_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4104_ = v_bvarIdx_4128_;
                            v_strict_4105_ = v_strict_4129_;
                            v_bvarIdx_x27_4106_ = v_bvarIdx_4130_;
                            v_strict_x27_4107_ = v_strict_4131_;
                            state = 3;
                            continue;
                        }
                        8 => {
                            v_e_4132_ = lean_ctor_get(v_x_4087_, 0);
                            v_e_4133_ = lean_ctor_get(v_x_4088_, 0);
                            v___x_4134_ = lean_expr_eqv(v_e_4132_, v_e_4133_);
                            return v___x_4134_;
                        }
                        9 => {
                            v_e_4135_ = lean_ctor_get(v_x_4087_, 0);
                            v_e_4136_ = lean_ctor_get(v_x_4088_, 0);
                            v___x_4137_ = lean_expr_eqv(v_e_4135_, v_e_4136_);
                            return v___x_4137_;
                        }
                        10 => {
                            v_bvarIdx_4138_ = lean_ctor_get(v_x_4087_, 0);
                            v_strict_4139_ = lean_ctor_get_uint8(
                                v_x_4087_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4140_ = lean_ctor_get(v_x_4088_, 0);
                            v_strict_4141_ = lean_ctor_get_uint8(
                                v_x_4088_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            );
                            v_bvarIdx_4104_ = v_bvarIdx_4138_;
                            v_strict_4105_ = v_strict_4139_;
                            v_bvarIdx_x27_4106_ = v_bvarIdx_4140_;
                            v_strict_x27_4107_ = v_strict_4141_;
                            state = 3;
                            continue;
                        }
                        _ => {
                            v_n_4142_ = lean_ctor_get(v_x_4087_, 0);
                            v_n_4143_ = lean_ctor_get(v_x_4088_, 0);
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
    mut v_x_4145_: *mut LeanObject,
    mut v_x_4146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4147_: u8 = 0;
    let mut v_r_4148_: *mut LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_4145_, v_x_4146_);
    lean_dec_ref(v_x_4146_);
    lean_dec_ref(v_x_4145_);
    v_r_4148_ = lean_box((v_res_4147_) as usize);
    return v_r_4148_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0()
-> *mut LeanObject {
    let mut v___x_4151_: u8 = 0;
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    v___x_4151_ = 0;
    v___x_4152_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default;
    v___x_4153_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
    v___x_4154_ = lean_box(0);
    v___x_4155_ = lean_unsigned_to_nat(0);
    v___x_4156_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3,
    );
    v___x_4157_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0;
    v___x_4158_ = lean_alloc_ctor(0, 8, (1) as u32);
    lean_ctor_set(v___x_4158_, 0, v___x_4157_);
    lean_ctor_set(v___x_4158_, 1, v___x_4156_);
    lean_ctor_set(v___x_4158_, 2, v___x_4155_);
    lean_ctor_set(v___x_4158_, 3, v___x_4154_);
    lean_ctor_set(v___x_4158_, 4, v___x_4154_);
    lean_ctor_set(v___x_4158_, 5, v___x_4153_);
    lean_ctor_set(v___x_4158_, 6, v___x_4152_);
    lean_ctor_set(v___x_4158_, 7, v___x_4154_);
    lean_ctor_set_uint8(
        v___x_4158_,
        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
        v___x_4151_,
    );
    return v___x_4158_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default() -> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    v___x_4159_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0,
    );
    return v___x_4159_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem() -> *mut LeanObject {
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
    return v___x_4160_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(
    mut v_thm_4161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symbols_4162_: *mut LeanObject = core::ptr::null_mut();
    v_symbols_4162_ = lean_ctor_get(v_thm_4161_, 4);
    lean_inc(v_symbols_4162_);
    return v_symbols_4162_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(
    mut v_thm_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4164_: *mut LeanObject = core::ptr::null_mut();
    v_res_4164_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_4163_);
    lean_dec_ref(v_thm_4163_);
    return v_res_4164_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(
    mut v_thm_4165_: *mut LeanObject,
    mut v_symbols_4166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelParams_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patterns_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minIndexable_4173_: u8 = 0;
    let mut v_cnstrs_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_unused_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_levelParams_4167_ = lean_ctor_get(v_thm_4165_, 0);
                v_proof_4168_ = lean_ctor_get(v_thm_4165_, 1);
                v_numParams_4169_ = lean_ctor_get(v_thm_4165_, 2);
                v_patterns_4170_ = lean_ctor_get(v_thm_4165_, 3);
                v_origin_4171_ = lean_ctor_get(v_thm_4165_, 5);
                v_kind_4172_ = lean_ctor_get(v_thm_4165_, 6);
                v_minIndexable_4173_ = lean_ctor_get_uint8(
                    v_thm_4165_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                v_cnstrs_4174_ = lean_ctor_get(v_thm_4165_, 7);
                v_isSharedCheck_4181_ = (!lean_is_exclusive(v_thm_4165_)) as u8;
                if v_isSharedCheck_4181_ == 0 {
                    v_unused_4182_ = lean_ctor_get(v_thm_4165_, 4);
                    lean_dec(v_unused_4182_);
                    v___x_4176_ = v_thm_4165_;
                    v_isShared_4177_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_cnstrs_4174_);
                    lean_inc(v_kind_4172_);
                    lean_inc(v_origin_4171_);
                    lean_inc(v_patterns_4170_);
                    lean_inc(v_numParams_4169_);
                    lean_inc(v_proof_4168_);
                    lean_inc(v_levelParams_4167_);
                    lean_dec(v_thm_4165_);
                    v___x_4176_ = lean_box(0);
                    v_isShared_4177_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4177_ == 0 {
                    lean_ctor_set(v___x_4176_, 4, v_symbols_4166_);
                    v___x_4179_ = v___x_4176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 8, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_levelParams_4167_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_proof_4168_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_numParams_4169_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_patterns_4170_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_symbols_4166_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 5, v_origin_4171_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 6, v_kind_4172_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 7, v_cnstrs_4174_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4180_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
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
    mut v_thm_4183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_origin_4184_: *mut LeanObject = core::ptr::null_mut();
    v_origin_4184_ = lean_ctor_get(v_thm_4183_, 5);
    lean_inc_ref(v_origin_4184_);
    return v_origin_4184_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(
    mut v_thm_4185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4186_: *mut LeanObject = core::ptr::null_mut();
    v_res_4186_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_4185_);
    lean_dec_ref(v_thm_4185_);
    return v_res_4186_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(
    mut v_thm_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_proof_4188_: *mut LeanObject = core::ptr::null_mut();
    v_proof_4188_ = lean_ctor_get(v_thm_4187_, 1);
    lean_inc_ref(v_proof_4188_);
    return v_proof_4188_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(
    mut v_thm_4189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4190_: *mut LeanObject = core::ptr::null_mut();
    v_res_4190_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_4189_);
    lean_dec_ref(v_thm_4189_);
    return v_res_4190_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(
    mut v_thm_4191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelParams_4192_: *mut LeanObject = core::ptr::null_mut();
    v_levelParams_4192_ = lean_ctor_get(v_thm_4191_, 0);
    lean_inc_ref(v_levelParams_4192_);
    return v_levelParams_4192_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(
    mut v_thm_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4194_: *mut LeanObject = core::ptr::null_mut();
    v_res_4194_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_4193_);
    lean_dec_ref(v_thm_4193_);
    return v_res_4194_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0()
-> *mut LeanObject {
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
    v___x_4208_ = lean_box(0);
    v___x_4209_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3,
    );
    v___x_4210_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0;
    v___x_4211_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4211_, 0, v___x_4210_);
    lean_ctor_set(v___x_4211_, 1, v___x_4209_);
    lean_ctor_set(v___x_4211_, 2, v___x_4208_);
    lean_ctor_set(v___x_4211_, 3, v___x_4207_);
    return v___x_4211_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default() -> *mut LeanObject {
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    v___x_4212_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem() -> *mut LeanObject {
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    v___x_4213_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
    return v___x_4213_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(
    mut v_thm_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symbols_4215_: *mut LeanObject = core::ptr::null_mut();
    v_symbols_4215_ = lean_ctor_get(v_thm_4214_, 2);
    lean_inc(v_symbols_4215_);
    return v_symbols_4215_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(
    mut v_thm_4216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4217_: *mut LeanObject = core::ptr::null_mut();
    v_res_4217_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_4216_);
    lean_dec_ref(v_thm_4216_);
    return v_res_4217_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(
    mut v_thm_4218_: *mut LeanObject,
    mut v_symbols_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelParams_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_unused_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_levelParams_4220_ = lean_ctor_get(v_thm_4218_, 0);
                v_proof_4221_ = lean_ctor_get(v_thm_4218_, 1);
                v_origin_4222_ = lean_ctor_get(v_thm_4218_, 3);
                v_isSharedCheck_4229_ = (!lean_is_exclusive(v_thm_4218_)) as u8;
                if v_isSharedCheck_4229_ == 0 {
                    v_unused_4230_ = lean_ctor_get(v_thm_4218_, 2);
                    lean_dec(v_unused_4230_);
                    v___x_4224_ = v_thm_4218_;
                    v_isShared_4225_ = v_isSharedCheck_4229_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_origin_4222_);
                    lean_inc(v_proof_4221_);
                    lean_inc(v_levelParams_4220_);
                    lean_dec(v_thm_4218_);
                    v___x_4224_ = lean_box(0);
                    v_isShared_4225_ = v_isSharedCheck_4229_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4225_ == 0 {
                    lean_ctor_set(v___x_4224_, 2, v_symbols_4219_);
                    v___x_4227_ = v___x_4224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_levelParams_4220_);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 1, v_proof_4221_);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 2, v_symbols_4219_);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 3, v_origin_4222_);
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
    mut v_thm_4231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_origin_4232_: *mut LeanObject = core::ptr::null_mut();
    v_origin_4232_ = lean_ctor_get(v_thm_4231_, 3);
    lean_inc_ref(v_origin_4232_);
    return v_origin_4232_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(
    mut v_thm_4233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4234_: *mut LeanObject = core::ptr::null_mut();
    v_res_4234_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_4233_);
    lean_dec_ref(v_thm_4233_);
    return v_res_4234_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(
    mut v_thm_4235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_proof_4236_: *mut LeanObject = core::ptr::null_mut();
    v_proof_4236_ = lean_ctor_get(v_thm_4235_, 1);
    lean_inc_ref(v_proof_4236_);
    return v_proof_4236_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(
    mut v_thm_4237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4238_: *mut LeanObject = core::ptr::null_mut();
    v_res_4238_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_4237_);
    lean_dec_ref(v_thm_4237_);
    return v_res_4238_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(
    mut v_thm_4239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelParams_4240_: *mut LeanObject = core::ptr::null_mut();
    v_levelParams_4240_ = lean_ctor_get(v_thm_4239_, 0);
    lean_inc_ref(v_levelParams_4240_);
    return v_levelParams_4240_;
}
pub unsafe fn l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(
    mut v_thm_4241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4242_: *mut LeanObject = core::ptr::null_mut();
    v_res_4242_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_4241_);
    lean_dec_ref(v_thm_4241_);
    return v_res_4242_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorIdx(mut v_x_4255_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4255_) {
        0 => {
            let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
            v___x_4256_ = lean_unsigned_to_nat(0);
            return v___x_4256_;
        }
        1 => {
            let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
            v___x_4257_ = lean_unsigned_to_nat(1);
            return v___x_4257_;
        }
        2 => {
            let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
            v___x_4258_ = lean_unsigned_to_nat(2);
            return v___x_4258_;
        }
        3 => {
            let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
            v___x_4259_ = lean_unsigned_to_nat(3);
            return v___x_4259_;
        }
        _ => {
            let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
            v___x_4260_ = lean_unsigned_to_nat(4);
            return v___x_4260_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorIdx___boxed(
    mut v_x_4261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4262_: *mut LeanObject = core::ptr::null_mut();
    v_res_4262_ = l_Lean_Meta_Grind_Entry_ctorIdx(v_x_4261_);
    lean_dec_ref(v_x_4261_);
    return v_res_4262_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorElim___redArg(
    mut v_t_4263_: *mut LeanObject,
    mut v_k_4264_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4263_) {
        2 => {
            let mut v_declName_4265_: *mut LeanObject = core::ptr::null_mut();
            let mut v_eager_4266_: u8 = 0;
            let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
            v_declName_4265_ = lean_ctor_get(v_t_4263_, 0);
            lean_inc(v_declName_4265_);
            v_eager_4266_ = lean_ctor_get_uint8(
                v_t_4263_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_4263_, 1);
            v___x_4267_ = lean_box((v_eager_4266_) as usize);
            v___x_4268_ = lean_apply_2(v_k_4264_, v_declName_4265_, v___x_4267_);
            return v___x_4268_;
        }
        3 => {
            let mut v_thm_4269_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
            v_thm_4269_ = lean_ctor_get(v_t_4263_, 0);
            lean_inc_ref(v_thm_4269_);
            lean_dec_ref_known(v_t_4263_, 1);
            v___x_4270_ = lean_apply_1(v_k_4264_, v_thm_4269_);
            return v___x_4270_;
        }
        4 => {
            let mut v_thm_4271_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
            v_thm_4271_ = lean_ctor_get(v_t_4263_, 0);
            lean_inc_ref(v_thm_4271_);
            lean_dec_ref_known(v_t_4263_, 1);
            v___x_4272_ = lean_apply_1(v_k_4264_, v_thm_4271_);
            return v___x_4272_;
        }
        _ => {
            let mut v_declName_4273_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
            v_declName_4273_ = lean_ctor_get(v_t_4263_, 0);
            lean_inc(v_declName_4273_);
            lean_dec_ref(v_t_4263_);
            v___x_4274_ = lean_apply_1(v_k_4264_, v_declName_4273_);
            return v___x_4274_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorElim(
    mut v_motive_4275_: *mut LeanObject,
    mut v_ctorIdx_4276_: *mut LeanObject,
    mut v_t_4277_: *mut LeanObject,
    mut v_h_4278_: *mut LeanObject,
    mut v_k_4279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    v___x_4280_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4277_, v_k_4279_);
    return v___x_4280_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ctorElim___boxed(
    mut v_motive_4281_: *mut LeanObject,
    mut v_ctorIdx_4282_: *mut LeanObject,
    mut v_t_4283_: *mut LeanObject,
    mut v_h_4284_: *mut LeanObject,
    mut v_k_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4286_: *mut LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_Meta_Grind_Entry_ctorElim(
        v_motive_4281_,
        v_ctorIdx_4282_,
        v_t_4283_,
        v_h_4284_,
        v_k_4285_,
    );
    lean_dec(v_ctorIdx_4282_);
    return v_res_4286_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ext_elim___redArg(
    mut v_t_4287_: *mut LeanObject,
    mut v_ext_4288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    v___x_4289_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4287_, v_ext_4288_);
    return v___x_4289_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ext_elim(
    mut v_motive_4290_: *mut LeanObject,
    mut v_t_4291_: *mut LeanObject,
    mut v_h_4292_: *mut LeanObject,
    mut v_ext_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4291_, v_ext_4293_);
    return v___x_4294_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_funCC_elim___redArg(
    mut v_t_4295_: *mut LeanObject,
    mut v_funCC_4296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    v___x_4297_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4295_, v_funCC_4296_);
    return v___x_4297_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_funCC_elim(
    mut v_motive_4298_: *mut LeanObject,
    mut v_t_4299_: *mut LeanObject,
    mut v_h_4300_: *mut LeanObject,
    mut v_funCC_4301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    v___x_4302_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4299_, v_funCC_4301_);
    return v___x_4302_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_cases_elim___redArg(
    mut v_t_4303_: *mut LeanObject,
    mut v_cases_4304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    v___x_4305_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4303_, v_cases_4304_);
    return v___x_4305_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_cases_elim(
    mut v_motive_4306_: *mut LeanObject,
    mut v_t_4307_: *mut LeanObject,
    mut v_h_4308_: *mut LeanObject,
    mut v_cases_4309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    v___x_4310_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4307_, v_cases_4309_);
    return v___x_4310_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ematch_elim___redArg(
    mut v_t_4311_: *mut LeanObject,
    mut v_ematch_4312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    v___x_4313_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4311_, v_ematch_4312_);
    return v___x_4313_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_ematch_elim(
    mut v_motive_4314_: *mut LeanObject,
    mut v_t_4315_: *mut LeanObject,
    mut v_h_4316_: *mut LeanObject,
    mut v_ematch_4317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    v___x_4318_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4315_, v_ematch_4317_);
    return v___x_4318_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_inj_elim___redArg(
    mut v_t_4319_: *mut LeanObject,
    mut v_inj_4320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    v___x_4321_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4319_, v_inj_4320_);
    return v___x_4321_;
}
pub unsafe fn l_Lean_Meta_Grind_Entry_inj_elim(
    mut v_motive_4322_: *mut LeanObject,
    mut v_t_4323_: *mut LeanObject,
    mut v_h_4324_: *mut LeanObject,
    mut v_inj_4325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    v___x_4326_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_4323_, v_inj_4325_);
    return v___x_4326_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    v___x_4331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4331_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    v___x_4332_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
    v___x_4333_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4333_, 0, v___x_4332_);
    return v___x_4333_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(
    mut v_00_u03b2_4334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    v___x_4335_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1);
    return v___x_4335_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0()
-> *mut LeanObject {
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    v___x_4336_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_box(0));
    return v___x_4336_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1()
-> *mut LeanObject {
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    v___x_4337_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
    return v___x_4337_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2()
-> *mut LeanObject {
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    v___x_4338_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1,
    );
    v___x_4339_ = l_Lean_NameSet_empty;
    v___x_4340_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0,
    );
    v___x_4341_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once),
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1,
    );
    v___x_4342_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4342_, 0, v___x_4341_);
    lean_ctor_set(v___x_4342_, 1, v___x_4340_);
    lean_ctor_set(v___x_4342_, 2, v___x_4339_);
    lean_ctor_set(v___x_4342_, 3, v___x_4338_);
    lean_ctor_set(v___x_4342_, 4, v___x_4338_);
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default() -> *mut LeanObject {
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    v___x_4343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2,
    );
    return v___x_4343_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedExtensionState() -> *mut LeanObject {
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    v___x_4344_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
    return v___x_4344_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(
    mut v_x_4345_: *mut LeanObject,
    mut v_x_4346_: *mut LeanObject,
    mut v_x_4347_: *mut LeanObject,
    mut v_x_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4353_: u8 = 0;
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4349_ = lean_ctor_get(v_x_4345_, 0);
                v_vs_4350_ = lean_ctor_get(v_x_4345_, 1);
                v_isSharedCheck_4376_ = (!lean_is_exclusive(v_x_4345_)) as u8;
                if v_isSharedCheck_4376_ == 0 {
                    v___x_4352_ = v_x_4345_;
                    v_isShared_4353_ = v_isSharedCheck_4376_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4350_);
                    lean_inc(v_ks_4349_);
                    lean_dec(v_x_4345_);
                    v___x_4352_ = lean_box(0);
                    v_isShared_4353_ = v_isSharedCheck_4376_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4354_ = lean_array_get_size(v_ks_4349_);
                v___x_4355_ = lean_nat_dec_lt(v_x_4346_, v___x_4354_);
                if v___x_4355_ == 0 {
                    lean_dec(v_x_4346_);
                    v___x_4356_ = lean_array_push(v_ks_4349_, v_x_4347_);
                    v___x_4357_ = lean_array_push(v_vs_4350_, v_x_4348_);
                    if v_isShared_4353_ == 0 {
                        lean_ctor_set(v___x_4352_, 1, v___x_4357_);
                        lean_ctor_set(v___x_4352_, 0, v___x_4356_);
                        v___x_4359_ = v___x_4352_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4356_);
                        lean_ctor_set(v_reuseFailAlloc_4360_, 1, v___x_4357_);
                        v___x_4359_ = v_reuseFailAlloc_4360_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4361_ = lean_array_fget_borrowed(v_ks_4349_, v_x_4346_);
                    v___x_4362_ = l_Lean_Meta_Grind_Origin_key(v_x_4347_);
                    v___x_4363_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_4361_);
                    v___x_4364_ = lean_name_eq(v___x_4362_, v___x_4363_);
                    lean_dec(v___x_4363_);
                    lean_dec(v___x_4362_);
                    if v___x_4364_ == 0 {
                        if v_isShared_4353_ == 0 {
                            v___x_4366_ = v___x_4352_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_ks_4349_);
                            lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_vs_4350_);
                            v___x_4366_ = v_reuseFailAlloc_4370_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4371_ = lean_array_fset(v_ks_4349_, v_x_4346_, v_x_4347_);
                        v___x_4372_ = lean_array_fset(v_vs_4350_, v_x_4346_, v_x_4348_);
                        lean_dec(v_x_4346_);
                        if v_isShared_4353_ == 0 {
                            lean_ctor_set(v___x_4352_, 1, v___x_4372_);
                            lean_ctor_set(v___x_4352_, 0, v___x_4371_);
                            v___x_4374_ = v___x_4352_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4371_);
                            lean_ctor_set(v_reuseFailAlloc_4375_, 1, v___x_4372_);
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
                v___x_4367_ = lean_unsigned_to_nat(1);
                v___x_4368_ = lean_nat_add(v_x_4346_, v___x_4367_);
                lean_dec(v_x_4346_);
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
    mut v_n_4377_: *mut LeanObject,
    mut v_k_4378_: *mut LeanObject,
    mut v_v_4379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    v___x_4380_ = lean_unsigned_to_nat(0);
    v___x_4381_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_n_4377_, v___x_4380_, v_k_4378_, v_v_4379_);
    return v___x_4381_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    v___x_4382_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4382_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(
    mut v_x_4383_: *mut LeanObject,
    mut v_x_4384_: usize,
    mut v_x_4385_: usize,
    mut v_x_4386_: *mut LeanObject,
    mut v_x_4387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: usize = 0;
    let mut v___x_4390_: usize = 0;
    let mut v___x_4391_: usize = 0;
    let mut v___x_4392_: usize = 0;
    let mut v_j_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v_v_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: u8 = 0;
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v_node_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4425_: u8 = 0;
    let mut v___x_4426_: usize = 0;
    let mut v___x_4427_: usize = 0;
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4432_: u8 = 0;
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4434_: u8 = 0;
    let mut v_unused_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4440_: u8 = 0;
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4445_: u8 = 0;
    let mut v_ks_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: usize = 0;
    let mut v___x_4452_: u8 = 0;
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v_reuseFailAlloc_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4383_) == 0 {
                    v_es_4388_ = lean_ctor_get(v_x_4383_, 0);
                    v___x_4389_ = 5usize;
                    v___x_4390_ = 1usize;
                    v___x_4391_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4392_ = lean_usize_land(v_x_4384_, v___x_4391_);
                    v_j_4393_ = lean_usize_to_nat(v___x_4392_);
                    v___x_4394_ = lean_array_get_size(v_es_4388_);
                    v___x_4395_ = lean_nat_dec_lt(v_j_4393_, v___x_4394_);
                    if v___x_4395_ == 0 {
                        lean_dec(v_j_4393_);
                        lean_dec(v_x_4387_);
                        lean_dec_ref(v_x_4386_);
                        return v_x_4383_;
                    } else {
                        lean_inc_ref(v_es_4388_);
                        v_isSharedCheck_4434_ = (!lean_is_exclusive(v_x_4383_)) as u8;
                        if v_isSharedCheck_4434_ == 0 {
                            v_unused_4435_ = lean_ctor_get(v_x_4383_, 0);
                            lean_dec(v_unused_4435_);
                            v___x_4397_ = v_x_4383_;
                            v_isShared_4398_ = v_isSharedCheck_4434_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4383_);
                            v___x_4397_ = lean_box(0);
                            v_isShared_4398_ = v_isSharedCheck_4434_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4436_ = lean_ctor_get(v_x_4383_, 0);
                    v_vs_4437_ = lean_ctor_get(v_x_4383_, 1);
                    v_isSharedCheck_4457_ = (!lean_is_exclusive(v_x_4383_)) as u8;
                    if v_isSharedCheck_4457_ == 0 {
                        v___x_4439_ = v_x_4383_;
                        v_isShared_4440_ = v_isSharedCheck_4457_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4437_);
                        lean_inc(v_ks_4436_);
                        lean_dec(v_x_4383_);
                        v___x_4439_ = lean_box(0);
                        v_isShared_4440_ = v_isSharedCheck_4457_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4399_ = lean_array_fget(v_es_4388_, v_j_4393_);
                v___x_4400_ = lean_box(0);
                v_xs_x27_4401_ = lean_array_fset(v_es_4388_, v_j_4393_, v___x_4400_);
                match lean_obj_tag(v_v_4399_) {
                    0 => {
                        v_key_4408_ = lean_ctor_get(v_v_4399_, 0);
                        v_val_4409_ = lean_ctor_get(v_v_4399_, 1);
                        v_isSharedCheck_4421_ = (!lean_is_exclusive(v_v_4399_)) as u8;
                        if v_isSharedCheck_4421_ == 0 {
                            v___x_4411_ = v_v_4399_;
                            v_isShared_4412_ = v_isSharedCheck_4421_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4409_);
                            lean_inc(v_key_4408_);
                            lean_dec(v_v_4399_);
                            v___x_4411_ = lean_box(0);
                            v_isShared_4412_ = v_isSharedCheck_4421_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4422_ = lean_ctor_get(v_v_4399_, 0);
                        v_isSharedCheck_4432_ = (!lean_is_exclusive(v_v_4399_)) as u8;
                        if v_isSharedCheck_4432_ == 0 {
                            v___x_4424_ = v_v_4399_;
                            v_isShared_4425_ = v_isSharedCheck_4432_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4422_);
                            lean_dec(v_v_4399_);
                            v___x_4424_ = lean_box(0);
                            v_isShared_4425_ = v_isSharedCheck_4432_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4433_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4433_, 0, v_x_4386_);
                        lean_ctor_set(v___x_4433_, 1, v_x_4387_);
                        v___y_4403_ = v___x_4433_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4404_ = lean_array_fset(v_xs_x27_4401_, v_j_4393_, v___y_4403_);
                lean_dec(v_j_4393_);
                if v_isShared_4398_ == 0 {
                    lean_ctor_set(v___x_4397_, 0, v___x_4404_);
                    v___x_4406_ = v___x_4397_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4404_);
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
                lean_dec(v___x_4414_);
                lean_dec(v___x_4413_);
                if v___x_4415_ == 0 {
                    lean_del_object(v___x_4411_);
                    v___x_4416_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4408_,
                        v_val_4409_,
                        v_x_4386_,
                        v_x_4387_,
                    );
                    v___x_4417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4417_, 0, v___x_4416_);
                    v___y_4403_ = v___x_4417_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4409_);
                    lean_dec(v_key_4408_);
                    if v_isShared_4412_ == 0 {
                        lean_ctor_set(v___x_4411_, 1, v_x_4387_);
                        lean_ctor_set(v___x_4411_, 0, v_x_4386_);
                        v___x_4419_ = v___x_4411_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_x_4386_);
                        lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_x_4387_);
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
                    lean_ctor_set(v___x_4424_, 0, v___x_4428_);
                    v___x_4430_ = v___x_4424_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
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
                    v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_ks_4436_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_vs_4437_);
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
                    v___x_4454_ = lean_unsigned_to_nat(4);
                    v___x_4455_ = lean_nat_dec_lt(v___x_4453_, v___x_4454_);
                    lean_dec(v___x_4453_);
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
                    v_ks_4446_ = lean_ctor_get(v_newNode_4443_, 0);
                    lean_inc_ref(v_ks_4446_);
                    v_vs_4447_ = lean_ctor_get(v_newNode_4443_, 1);
                    lean_inc_ref(v_vs_4447_);
                    lean_dec_ref(v_newNode_4443_);
                    v___x_4448_ = lean_unsigned_to_nat(0);
                    v___x_4449_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0);
                    v___x_4450_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_4385_, v_ks_4446_, v_vs_4447_, v___x_4448_, v___x_4449_);
                    lean_dec_ref(v_vs_4447_);
                    lean_dec_ref(v_ks_4446_);
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
    mut v_keys_4459_: *mut LeanObject,
    mut v_vals_4460_: *mut LeanObject,
    mut v_i_4461_: *mut LeanObject,
    mut v_entries_4462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: u8 = 0;
    let mut v_k_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4468_: u64 = 0;
    let mut v_h_4469_: usize = 0;
    let mut v___x_4470_: usize = 0;
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: usize = 0;
    let mut v___x_4473_: usize = 0;
    let mut v___x_4474_: usize = 0;
    let mut v_h_4475_: usize = 0;
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: u64 = 0;
    let mut v_hash_4481_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4463_ = lean_array_get_size(v_keys_4459_);
                v___x_4464_ = lean_nat_dec_lt(v_i_4461_, v___x_4463_);
                if v___x_4464_ == 0 {
                    lean_dec(v_i_4461_);
                    return v_entries_4462_;
                } else {
                    v_k_4465_ = lean_array_fget_borrowed(v_keys_4459_, v_i_4461_);
                    v_v_4466_ = lean_array_fget_borrowed(v_vals_4460_, v_i_4461_);
                    v___x_4479_ = l_Lean_Meta_Grind_Origin_key(v_k_4465_);
                    if lean_obj_tag(v___x_4479_) == 0 {
                        v___x_4480_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_4468_ = v___x_4480_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4481_ = lean_ctor_get_uint64(
                            v___x_4479_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        lean_dec(v___x_4479_);
                        v___y_4468_ = v_hash_4481_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4469_ = lean_uint64_to_usize(v___y_4468_);
                v___x_4470_ = 5usize;
                v___x_4471_ = lean_unsigned_to_nat(1);
                v___x_4472_ = 1usize;
                v___x_4473_ = lean_usize_sub(v_depth_4458_, v___x_4472_);
                v___x_4474_ = lean_usize_mul(v___x_4470_, v___x_4473_);
                v_h_4475_ = lean_usize_shift_right(v_h_4469_, v___x_4474_);
                v___x_4476_ = lean_nat_add(v_i_4461_, v___x_4471_);
                lean_dec(v_i_4461_);
                lean_inc(v_v_4466_);
                lean_inc(v_k_4465_);
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
    mut v_depth_4482_: *mut LeanObject,
    mut v_keys_4483_: *mut LeanObject,
    mut v_vals_4484_: *mut LeanObject,
    mut v_i_4485_: *mut LeanObject,
    mut v_entries_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4487_: usize = 0;
    let mut v_res_4488_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4487_ = lean_unbox_usize(v_depth_4482_);
    lean_dec(v_depth_4482_);
    v_res_4488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_4487_, v_keys_4483_, v_vals_4484_, v_i_4485_, v_entries_4486_);
    lean_dec_ref(v_vals_4484_);
    lean_dec_ref(v_keys_4483_);
    return v_res_4488_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_4489_: *mut LeanObject,
    mut v_x_4490_: *mut LeanObject,
    mut v_x_4491_: *mut LeanObject,
    mut v_x_4492_: *mut LeanObject,
    mut v_x_4493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1264__boxed_4494_: usize = 0;
    let mut v_x_1265__boxed_4495_: usize = 0;
    let mut v_res_4496_: *mut LeanObject = core::ptr::null_mut();
    v_x_1264__boxed_4494_ = lean_unbox_usize(v_x_4490_);
    lean_dec(v_x_4490_);
    v_x_1265__boxed_4495_ = lean_unbox_usize(v_x_4491_);
    lean_dec(v_x_4491_);
    v_res_4496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_4489_, v_x_1264__boxed_4494_, v_x_1265__boxed_4495_, v_x_4492_, v_x_4493_);
    return v_res_4496_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(
    mut v_x_4497_: *mut LeanObject,
    mut v_x_4498_: *mut LeanObject,
    mut v_x_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4501_: u64 = 0;
    let mut v___x_4502_: usize = 0;
    let mut v___x_4503_: usize = 0;
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: u64 = 0;
    let mut v_hash_4507_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4505_ = l_Lean_Meta_Grind_Origin_key(v_x_4498_);
                if lean_obj_tag(v___x_4505_) == 0 {
                    v___x_4506_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4501_ = v___x_4506_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4507_ = lean_ctor_get_uint64(
                        v___x_4505_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v___x_4505_);
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
    mut v_keys_4508_: *mut LeanObject,
    mut v_vals_4509_: *mut LeanObject,
    mut v_i_4510_: *mut LeanObject,
    mut v_k_4511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4512_ = lean_array_get_size(v_keys_4508_);
                v___x_4513_ = lean_nat_dec_lt(v_i_4510_, v___x_4512_);
                if v___x_4513_ == 0 {
                    lean_dec(v_i_4510_);
                    v___x_4514_ = lean_box(0);
                    return v___x_4514_;
                } else {
                    v_k_x27_4515_ = lean_array_fget_borrowed(v_keys_4508_, v_i_4510_);
                    v___x_4516_ = l_Lean_Meta_Grind_Origin_key(v_k_4511_);
                    v___x_4517_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_4515_);
                    v___x_4518_ = lean_name_eq(v___x_4516_, v___x_4517_);
                    lean_dec(v___x_4517_);
                    lean_dec(v___x_4516_);
                    if v___x_4518_ == 0 {
                        v___x_4519_ = lean_unsigned_to_nat(1);
                        v___x_4520_ = lean_nat_add(v_i_4510_, v___x_4519_);
                        lean_dec(v_i_4510_);
                        v_i_4510_ = v___x_4520_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4522_ = lean_array_fget_borrowed(v_vals_4509_, v_i_4510_);
                        lean_dec(v_i_4510_);
                        lean_inc(v___x_4522_);
                        v___x_4523_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4523_, 0, v___x_4522_);
                        return v___x_4523_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(
    mut v_keys_4524_: *mut LeanObject,
    mut v_vals_4525_: *mut LeanObject,
    mut v_i_4526_: *mut LeanObject,
    mut v_k_4527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4528_: *mut LeanObject = core::ptr::null_mut();
    v_res_4528_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_4524_, v_vals_4525_, v_i_4526_, v_k_4527_);
    lean_dec_ref(v_k_4527_);
    lean_dec_ref(v_vals_4525_);
    lean_dec_ref(v_keys_4524_);
    return v_res_4528_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(
    mut v_x_4529_: *mut LeanObject,
    mut v_x_4530_: usize,
    mut v_x_4531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: usize = 0;
    let mut v_j_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: u8 = 0;
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: usize = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4529_) == 0 {
                    v_es_4532_ = lean_ctor_get(v_x_4529_, 0);
                    v___x_4533_ = lean_box(2);
                    v___x_4534_ = 5usize;
                    v___x_4535_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4536_ = lean_usize_land(v_x_4530_, v___x_4535_);
                    v_j_4537_ = lean_usize_to_nat(v___x_4536_);
                    v___x_4538_ = lean_array_get_borrowed(v___x_4533_, v_es_4532_, v_j_4537_);
                    lean_dec(v_j_4537_);
                    match lean_obj_tag(v___x_4538_) {
                        0 => {
                            v_key_4539_ = lean_ctor_get(v___x_4538_, 0);
                            v_val_4540_ = lean_ctor_get(v___x_4538_, 1);
                            v___x_4541_ = l_Lean_Meta_Grind_Origin_key(v_x_4531_);
                            v___x_4542_ = l_Lean_Meta_Grind_Origin_key(v_key_4539_);
                            v___x_4543_ = lean_name_eq(v___x_4541_, v___x_4542_);
                            lean_dec(v___x_4542_);
                            lean_dec(v___x_4541_);
                            if v___x_4543_ == 0 {
                                v___x_4544_ = lean_box(0);
                                return v___x_4544_;
                            } else {
                                lean_inc(v_val_4540_);
                                v___x_4545_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4545_, 0, v_val_4540_);
                                return v___x_4545_;
                            }
                        }
                        1 => {
                            v_node_4546_ = lean_ctor_get(v___x_4538_, 0);
                            v___x_4547_ = lean_usize_shift_right(v_x_4530_, v___x_4534_);
                            v_x_4529_ = v_node_4546_;
                            v_x_4530_ = v___x_4547_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4549_ = lean_box(0);
                            return v___x_4549_;
                        }
                    }
                } else {
                    v_ks_4550_ = lean_ctor_get(v_x_4529_, 0);
                    v_vs_4551_ = lean_ctor_get(v_x_4529_, 1);
                    v___x_4552_ = lean_unsigned_to_nat(0);
                    v___x_4553_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_4550_, v_vs_4551_, v___x_4552_, v_x_4531_);
                    return v___x_4553_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(
    mut v_x_4554_: *mut LeanObject,
    mut v_x_4555_: *mut LeanObject,
    mut v_x_4556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1478__boxed_4557_: usize = 0;
    let mut v_res_4558_: *mut LeanObject = core::ptr::null_mut();
    v_x_1478__boxed_4557_ = lean_unbox_usize(v_x_4555_);
    lean_dec(v_x_4555_);
    v_res_4558_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_4554_, v_x_1478__boxed_4557_, v_x_4556_);
    lean_dec_ref(v_x_4556_);
    lean_dec_ref(v_x_4554_);
    return v_res_4558_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(
    mut v_x_4559_: *mut LeanObject,
    mut v_x_4560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4562_: u64 = 0;
    let mut v___x_4563_: usize = 0;
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u64 = 0;
    let mut v_hash_4567_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4565_ = l_Lean_Meta_Grind_Origin_key(v_x_4560_);
                if lean_obj_tag(v___x_4565_) == 0 {
                    v___x_4566_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4562_ = v___x_4566_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4567_ = lean_ctor_get_uint64(
                        v___x_4565_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v___x_4565_);
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
    mut v_x_4568_: *mut LeanObject,
    mut v_x_4569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4570_: *mut LeanObject = core::ptr::null_mut();
    v_res_4570_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_4568_, v_x_4569_);
    lean_dec_ref(v_x_4569_);
    lean_dec_ref(v_x_4568_);
    return v_res_4570_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(
    mut v_keys_4571_: *mut LeanObject,
    mut v_vals_4572_: *mut LeanObject,
    mut v_i_4573_: *mut LeanObject,
    mut v_k_4574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4575_ = lean_array_get_size(v_keys_4571_);
                v___x_4576_ = lean_nat_dec_lt(v_i_4573_, v___x_4575_);
                if v___x_4576_ == 0 {
                    lean_dec(v_i_4573_);
                    v___x_4577_ = lean_box(0);
                    return v___x_4577_;
                } else {
                    v_k_x27_4578_ = lean_array_fget_borrowed(v_keys_4571_, v_i_4573_);
                    v___x_4579_ = lean_name_eq(v_k_4574_, v_k_x27_4578_);
                    if v___x_4579_ == 0 {
                        v___x_4580_ = lean_unsigned_to_nat(1);
                        v___x_4581_ = lean_nat_add(v_i_4573_, v___x_4580_);
                        lean_dec(v_i_4573_);
                        v_i_4573_ = v___x_4581_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4583_ = lean_array_fget_borrowed(v_vals_4572_, v_i_4573_);
                        lean_dec(v_i_4573_);
                        lean_inc(v___x_4583_);
                        v___x_4584_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4584_, 0, v___x_4583_);
                        return v___x_4584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(
    mut v_keys_4585_: *mut LeanObject,
    mut v_vals_4586_: *mut LeanObject,
    mut v_i_4587_: *mut LeanObject,
    mut v_k_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4589_: *mut LeanObject = core::ptr::null_mut();
    v_res_4589_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_4585_, v_vals_4586_, v_i_4587_, v_k_4588_);
    lean_dec(v_k_4588_);
    lean_dec_ref(v_vals_4586_);
    lean_dec_ref(v_keys_4585_);
    return v_res_4589_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(
    mut v_x_4590_: *mut LeanObject,
    mut v_x_4591_: usize,
    mut v_x_4592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: usize = 0;
    let mut v___x_4596_: usize = 0;
    let mut v___x_4597_: usize = 0;
    let mut v_j_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: u8 = 0;
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: usize = 0;
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4590_) == 0 {
                    v_es_4593_ = lean_ctor_get(v_x_4590_, 0);
                    v___x_4594_ = lean_box(2);
                    v___x_4595_ = 5usize;
                    v___x_4596_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4597_ = lean_usize_land(v_x_4591_, v___x_4596_);
                    v_j_4598_ = lean_usize_to_nat(v___x_4597_);
                    v___x_4599_ = lean_array_get_borrowed(v___x_4594_, v_es_4593_, v_j_4598_);
                    lean_dec(v_j_4598_);
                    match lean_obj_tag(v___x_4599_) {
                        0 => {
                            v_key_4600_ = lean_ctor_get(v___x_4599_, 0);
                            v_val_4601_ = lean_ctor_get(v___x_4599_, 1);
                            v___x_4602_ = lean_name_eq(v_x_4592_, v_key_4600_);
                            if v___x_4602_ == 0 {
                                v___x_4603_ = lean_box(0);
                                return v___x_4603_;
                            } else {
                                lean_inc(v_val_4601_);
                                v___x_4604_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4604_, 0, v_val_4601_);
                                return v___x_4604_;
                            }
                        }
                        1 => {
                            v_node_4605_ = lean_ctor_get(v___x_4599_, 0);
                            v___x_4606_ = lean_usize_shift_right(v_x_4591_, v___x_4595_);
                            v_x_4590_ = v_node_4605_;
                            v_x_4591_ = v___x_4606_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4608_ = lean_box(0);
                            return v___x_4608_;
                        }
                    }
                } else {
                    v_ks_4609_ = lean_ctor_get(v_x_4590_, 0);
                    v_vs_4610_ = lean_ctor_get(v_x_4590_, 1);
                    v___x_4611_ = lean_unsigned_to_nat(0);
                    v___x_4612_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_4609_, v_vs_4610_, v___x_4611_, v_x_4592_);
                    return v___x_4612_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(
    mut v_x_4613_: *mut LeanObject,
    mut v_x_4614_: *mut LeanObject,
    mut v_x_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1576__boxed_4616_: usize = 0;
    let mut v_res_4617_: *mut LeanObject = core::ptr::null_mut();
    v_x_1576__boxed_4616_ = lean_unbox_usize(v_x_4614_);
    lean_dec(v_x_4614_);
    v_res_4617_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_4613_, v_x_1576__boxed_4616_, v_x_4615_);
    lean_dec(v_x_4615_);
    lean_dec_ref(v_x_4613_);
    return v_res_4617_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(
    mut v_x_4618_: *mut LeanObject,
    mut v_x_4619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4621_: u64 = 0;
    let mut v___x_4622_: usize = 0;
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: u64 = 0;
    let mut v_hash_4625_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4619_) == 0 {
                    v___x_4624_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4621_ = v___x_4624_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4625_ = lean_ctor_get_uint64(
                        v_x_4619_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_x_4626_: *mut LeanObject,
    mut v_x_4627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4628_: *mut LeanObject = core::ptr::null_mut();
    v_res_4628_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_4626_, v_x_4627_);
    lean_dec(v_x_4627_);
    lean_dec_ref(v_x_4626_);
    return v_res_4628_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    v___x_4636_ = l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_box(0));
    return v___x_4636_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(
    mut v_msg_4637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    v___f_4638_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0;
    v___f_4639_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1;
    v___f_4640_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2;
    v___f_4641_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3;
    v___f_4642_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4;
    v___f_4643_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5;
    v___f_4644_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6;
    v___x_4645_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4645_, 0, v___f_4638_);
    lean_ctor_set(v___x_4645_, 1, v___f_4639_);
    v___x_4646_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4646_, 0, v___x_4645_);
    lean_ctor_set(v___x_4646_, 1, v___f_4640_);
    lean_ctor_set(v___x_4646_, 2, v___f_4641_);
    lean_ctor_set(v___x_4646_, 3, v___f_4642_);
    lean_ctor_set(v___x_4646_, 4, v___f_4643_);
    v___x_4647_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4647_, 0, v___x_4646_);
    lean_ctor_set(v___x_4647_, 1, v___f_4644_);
    v___x_4648_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once), _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
    v___x_4649_ = l_instInhabitedOfMonad___redArg(v___x_4647_, v___x_4648_);
    v___x_4650_ = lean_panic_fn_borrowed(v___x_4649_, v_msg_4637_);
    lean_dec(v___x_4649_);
    return v___x_4650_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(
    mut v_xs_4651_: *mut LeanObject,
    mut v_v_4652_: *mut LeanObject,
    mut v_i_4653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: u8 = 0;
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4654_ = lean_array_get_size(v_xs_4651_);
                v___x_4655_ = lean_nat_dec_lt(v_i_4653_, v___x_4654_);
                if v___x_4655_ == 0 {
                    lean_dec(v_i_4653_);
                    v___x_4656_ = lean_box(0);
                    return v___x_4656_;
                } else {
                    v___x_4657_ = lean_array_fget_borrowed(v_xs_4651_, v_i_4653_);
                    v___x_4658_ = l_Lean_Meta_Grind_Origin_key(v___x_4657_);
                    v___x_4659_ = l_Lean_Meta_Grind_Origin_key(v_v_4652_);
                    v___x_4660_ = lean_name_eq(v___x_4658_, v___x_4659_);
                    lean_dec(v___x_4659_);
                    lean_dec(v___x_4658_);
                    if v___x_4660_ == 0 {
                        v___x_4661_ = lean_unsigned_to_nat(1);
                        v___x_4662_ = lean_nat_add(v_i_4653_, v___x_4661_);
                        lean_dec(v_i_4653_);
                        v_i_4653_ = v___x_4662_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4664_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4664_, 0, v_i_4653_);
                        return v___x_4664_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(
    mut v_xs_4665_: *mut LeanObject,
    mut v_v_4666_: *mut LeanObject,
    mut v_i_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4668_: *mut LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_4665_, v_v_4666_, v_i_4667_);
    lean_dec_ref(v_v_4666_);
    lean_dec_ref(v_xs_4665_);
    return v_res_4668_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(
    mut v_xs_4669_: *mut LeanObject,
    mut v_v_4670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    v___x_4671_ = lean_unsigned_to_nat(0);
    v___x_4672_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_4669_, v_v_4670_, v___x_4671_);
    return v___x_4672_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(
    mut v_xs_4673_: *mut LeanObject,
    mut v_v_4674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4675_: *mut LeanObject = core::ptr::null_mut();
    v_res_4675_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_4673_, v_v_4674_);
    lean_dec_ref(v_v_4674_);
    lean_dec_ref(v_xs_4673_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(
    mut v_x_4676_: *mut LeanObject,
    mut v_x_4677_: usize,
    mut v_x_4678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: usize = 0;
    let mut v___x_4682_: usize = 0;
    let mut v___x_4683_: usize = 0;
    let mut v_j_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: u8 = 0;
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4692_: u8 = 0;
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v_unused_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v_node_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4705_: u8 = 0;
    let mut v_entries_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: usize = 0;
    let mut v_newNode_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4722_: u8 = 0;
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4730_: u8 = 0;
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut v_unused_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4676_) == 0 {
                    v_es_4679_ = lean_ctor_get(v_x_4676_, 0);
                    v___x_4680_ = lean_box(2);
                    v___x_4681_ = 5usize;
                    v___x_4682_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_4683_ = lean_usize_land(v_x_4677_, v___x_4682_);
                    v_j_4684_ = lean_usize_to_nat(v___x_4683_);
                    v_entry_4685_ = lean_array_get(v___x_4680_, v_es_4679_, v_j_4684_);
                    match lean_obj_tag(v_entry_4685_) {
                        0 => {
                            v_key_4686_ = lean_ctor_get(v_entry_4685_, 0);
                            lean_inc(v_key_4686_);
                            lean_dec_ref_known(v_entry_4685_, 2);
                            v___x_4687_ = l_Lean_Meta_Grind_Origin_key(v_x_4678_);
                            v___x_4688_ = l_Lean_Meta_Grind_Origin_key(v_key_4686_);
                            lean_dec(v_key_4686_);
                            v___x_4689_ = lean_name_eq(v___x_4687_, v___x_4688_);
                            lean_dec(v___x_4688_);
                            lean_dec(v___x_4687_);
                            if v___x_4689_ == 0 {
                                lean_dec(v_j_4684_);
                                return v_x_4676_;
                            } else {
                                lean_inc_ref(v_es_4679_);
                                v_isSharedCheck_4697_ = (!lean_is_exclusive(v_x_4676_)) as u8;
                                if v_isSharedCheck_4697_ == 0 {
                                    v_unused_4698_ = lean_ctor_get(v_x_4676_, 0);
                                    lean_dec(v_unused_4698_);
                                    v___x_4691_ = v_x_4676_;
                                    v_isShared_4692_ = v_isSharedCheck_4697_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_x_4676_);
                                    v___x_4691_ = lean_box(0);
                                    v_isShared_4692_ = v_isSharedCheck_4697_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            lean_inc_ref(v_es_4679_);
                            v_isSharedCheck_4732_ = (!lean_is_exclusive(v_x_4676_)) as u8;
                            if v_isSharedCheck_4732_ == 0 {
                                v_unused_4733_ = lean_ctor_get(v_x_4676_, 0);
                                lean_dec(v_unused_4733_);
                                v___x_4700_ = v_x_4676_;
                                v_isShared_4701_ = v_isSharedCheck_4732_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_x_4676_);
                                v___x_4700_ = lean_box(0);
                                v_isShared_4701_ = v_isSharedCheck_4732_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_j_4684_);
                            return v_x_4676_;
                        }
                    }
                } else {
                    v_ks_4734_ = lean_ctor_get(v_x_4676_, 0);
                    v_vs_4735_ = lean_ctor_get(v_x_4676_, 1);
                    v_isSharedCheck_4749_ = (!lean_is_exclusive(v_x_4676_)) as u8;
                    if v_isSharedCheck_4749_ == 0 {
                        v___x_4737_ = v_x_4676_;
                        v_isShared_4738_ = v_isSharedCheck_4749_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_vs_4735_);
                        lean_inc(v_ks_4734_);
                        lean_dec(v_x_4676_);
                        v___x_4737_ = lean_box(0);
                        v_isShared_4738_ = v_isSharedCheck_4749_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4693_ = lean_array_set(v_es_4679_, v_j_4684_, v___x_4680_);
                lean_dec(v_j_4684_);
                if v_isShared_4692_ == 0 {
                    lean_ctor_set(v___x_4691_, 0, v___x_4693_);
                    v___x_4695_ = v___x_4691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
                    v___x_4695_ = v_reuseFailAlloc_4696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4695_;
            }
            3 => {
                v_node_4702_ = lean_ctor_get(v_entry_4685_, 0);
                v_isSharedCheck_4731_ = (!lean_is_exclusive(v_entry_4685_)) as u8;
                if v_isSharedCheck_4731_ == 0 {
                    v___x_4704_ = v_entry_4685_;
                    v_isShared_4705_ = v_isSharedCheck_4731_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_node_4702_);
                    lean_dec(v_entry_4685_);
                    v___x_4704_ = lean_box(0);
                    v_isShared_4705_ = v_isSharedCheck_4731_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_4706_ = lean_array_set(v_es_4679_, v_j_4684_, v___x_4680_);
                v___x_4707_ = lean_usize_shift_right(v_x_4677_, v___x_4681_);
                v_newNode_4708_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_4702_, v___x_4707_, v_x_4678_);
                lean_inc_ref(v_newNode_4708_);
                v___x_4709_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_4708_);
                if lean_obj_tag(v___x_4709_) == 0 {
                    if v_isShared_4705_ == 0 {
                        lean_ctor_set(v___x_4704_, 0, v_newNode_4708_);
                        v___x_4711_ = v___x_4704_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_newNode_4708_);
                        v___x_4711_ = v_reuseFailAlloc_4716_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newNode_4708_);
                    lean_del_object(v___x_4704_);
                    v_val_4717_ = lean_ctor_get(v___x_4709_, 0);
                    lean_inc(v_val_4717_);
                    lean_dec_ref_known(v___x_4709_, 1);
                    v_fst_4718_ = lean_ctor_get(v_val_4717_, 0);
                    v_snd_4719_ = lean_ctor_get(v_val_4717_, 1);
                    v_isSharedCheck_4730_ = (!lean_is_exclusive(v_val_4717_)) as u8;
                    if v_isSharedCheck_4730_ == 0 {
                        v___x_4721_ = v_val_4717_;
                        v_isShared_4722_ = v_isSharedCheck_4730_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_4719_);
                        lean_inc(v_fst_4718_);
                        lean_dec(v_val_4717_);
                        v___x_4721_ = lean_box(0);
                        v_isShared_4722_ = v_isSharedCheck_4730_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4712_ = lean_array_set(v_entries_4706_, v_j_4684_, v___x_4711_);
                lean_dec(v_j_4684_);
                if v_isShared_4701_ == 0 {
                    lean_ctor_set(v___x_4700_, 0, v___x_4712_);
                    v___x_4714_ = v___x_4700_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4712_);
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
                    v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_fst_4718_);
                    lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_snd_4719_);
                    v___x_4724_ = v_reuseFailAlloc_4729_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4725_ = lean_array_set(v_entries_4706_, v_j_4684_, v___x_4724_);
                lean_dec(v_j_4684_);
                if v_isShared_4701_ == 0 {
                    lean_ctor_set(v___x_4700_, 0, v___x_4725_);
                    v___x_4727_ = v___x_4700_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4725_);
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
                if lean_obj_tag(v___x_4739_) == 0 {
                    if v_isShared_4738_ == 0 {
                        v___x_4741_ = v___x_4737_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_ks_4734_);
                        lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_vs_4735_);
                        v___x_4741_ = v_reuseFailAlloc_4742_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_4743_ = lean_ctor_get(v___x_4739_, 0);
                    lean_inc_n(v_val_4743_, 2);
                    lean_dec_ref_known(v___x_4739_, 1);
                    v_keys_x27_4744_ = l_Array_eraseIdx___redArg(v_ks_4734_, v_val_4743_);
                    v_vals_x27_4745_ = l_Array_eraseIdx___redArg(v_vs_4735_, v_val_4743_);
                    if v_isShared_4738_ == 0 {
                        lean_ctor_set(v___x_4737_, 1, v_vals_x27_4745_);
                        lean_ctor_set(v___x_4737_, 0, v_keys_x27_4744_);
                        v___x_4747_ = v___x_4737_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_keys_x27_4744_);
                        lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_vals_x27_4745_);
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
    mut v_x_4750_: *mut LeanObject,
    mut v_x_4751_: *mut LeanObject,
    mut v_x_4752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1726__boxed_4753_: usize = 0;
    let mut v_res_4754_: *mut LeanObject = core::ptr::null_mut();
    v_x_1726__boxed_4753_ = lean_unbox_usize(v_x_4751_);
    lean_dec(v_x_4751_);
    v_res_4754_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_4750_, v_x_1726__boxed_4753_, v_x_4752_);
    lean_dec_ref(v_x_4752_);
    return v_res_4754_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(
    mut v_x_4755_: *mut LeanObject,
    mut v_x_4756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4758_: u64 = 0;
    let mut v_h_4759_: usize = 0;
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u64 = 0;
    let mut v_hash_4763_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4761_ = l_Lean_Meta_Grind_Origin_key(v_x_4756_);
                if lean_obj_tag(v___x_4761_) == 0 {
                    v___x_4762_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4758_ = v___x_4762_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4763_ = lean_ctor_get_uint64(
                        v___x_4761_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v___x_4761_);
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
    mut v_x_4764_: *mut LeanObject,
    mut v_x_4765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4766_: *mut LeanObject = core::ptr::null_mut();
    v_res_4766_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_4764_, v_x_4765_);
    lean_dec_ref(v_x_4765_);
    return v_res_4766_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    v___x_4770_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2;
    v___x_4771_ = lean_unsigned_to_nat(6);
    v___x_4772_ = lean_unsigned_to_nat(82);
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
    mut v_s_4776_: *mut LeanObject,
    mut v_thm_4777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_symbols_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patterns_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minIndexable_4789_: u8 = 0;
    let mut v_cnstrs_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4793_: u8 = 0;
    let mut v_tail_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4797_: u8 = 0;
    let mut v_constName_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_smap_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origins_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_erased_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_omap_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v_thm_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origins_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_erased_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut v_unused_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4841_: u8 = 0;
    let mut v_unused_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_symbols_4781_ = lean_ctor_get(v_thm_4777_, 4);
                lean_inc(v_symbols_4781_);
                if lean_obj_tag(v_symbols_4781_) == 1 {
                    v_head_4782_ = lean_ctor_get(v_symbols_4781_, 0);
                    lean_inc(v_head_4782_);
                    if lean_obj_tag(v_head_4782_) == 2 {
                        v_levelParams_4783_ = lean_ctor_get(v_thm_4777_, 0);
                        v_proof_4784_ = lean_ctor_get(v_thm_4777_, 1);
                        v_numParams_4785_ = lean_ctor_get(v_thm_4777_, 2);
                        v_patterns_4786_ = lean_ctor_get(v_thm_4777_, 3);
                        v_origin_4787_ = lean_ctor_get(v_thm_4777_, 5);
                        v_kind_4788_ = lean_ctor_get(v_thm_4777_, 6);
                        v_minIndexable_4789_ = lean_ctor_get_uint8(
                            v_thm_4777_,
                            (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        );
                        v_cnstrs_4790_ = lean_ctor_get(v_thm_4777_, 7);
                        v_isSharedCheck_4841_ = (!lean_is_exclusive(v_thm_4777_)) as u8;
                        if v_isSharedCheck_4841_ == 0 {
                            v_unused_4842_ = lean_ctor_get(v_thm_4777_, 4);
                            lean_dec(v_unused_4842_);
                            v___x_4792_ = v_thm_4777_;
                            v_isShared_4793_ = v_isSharedCheck_4841_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_cnstrs_4790_);
                            lean_inc(v_kind_4788_);
                            lean_inc(v_origin_4787_);
                            lean_inc(v_patterns_4786_);
                            lean_inc(v_numParams_4785_);
                            lean_inc(v_proof_4784_);
                            lean_inc(v_levelParams_4783_);
                            lean_dec(v_thm_4777_);
                            v___x_4792_ = lean_box(0);
                            v_isShared_4793_ = v_isSharedCheck_4841_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_head_4782_);
                        lean_dec_ref_known(v_symbols_4781_, 2);
                        lean_dec_ref(v_thm_4777_);
                        lean_dec_ref(v_s_4776_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_symbols_4781_);
                    lean_dec_ref(v_thm_4777_);
                    lean_dec_ref(v_s_4776_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4779_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once), _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
                v___x_4780_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_4779_);
                return v___x_4780_;
            }
            2 => {
                v_tail_4794_ = lean_ctor_get(v_symbols_4781_, 1);
                v_isSharedCheck_4839_ = (!lean_is_exclusive(v_symbols_4781_)) as u8;
                if v_isSharedCheck_4839_ == 0 {
                    v_unused_4840_ = lean_ctor_get(v_symbols_4781_, 0);
                    lean_dec(v_unused_4840_);
                    v___x_4796_ = v_symbols_4781_;
                    v_isShared_4797_ = v_isSharedCheck_4839_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_tail_4794_);
                    lean_dec(v_symbols_4781_);
                    v___x_4796_ = lean_box(0);
                    v_isShared_4797_ = v_isSharedCheck_4839_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_constName_4798_ = lean_ctor_get(v_head_4782_, 0);
                lean_inc(v_constName_4798_);
                lean_dec_ref_known(v_head_4782_, 1);
                v_smap_4799_ = lean_ctor_get(v_s_4776_, 0);
                v_origins_4800_ = lean_ctor_get(v_s_4776_, 1);
                v_erased_4801_ = lean_ctor_get(v_s_4776_, 2);
                v_omap_4802_ = lean_ctor_get(v_s_4776_, 3);
                v_isSharedCheck_4838_ = (!lean_is_exclusive(v_s_4776_)) as u8;
                if v_isSharedCheck_4838_ == 0 {
                    v___x_4804_ = v_s_4776_;
                    v_isShared_4805_ = v_isSharedCheck_4838_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_omap_4802_);
                    lean_inc(v_erased_4801_);
                    lean_inc(v_origins_4800_);
                    lean_inc(v_smap_4799_);
                    lean_dec(v_s_4776_);
                    v___x_4804_ = lean_box(0);
                    v_isShared_4805_ = v_isSharedCheck_4838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v_origin_4787_);
                if v_isShared_4793_ == 0 {
                    lean_ctor_set(v___x_4792_, 4, v_tail_4794_);
                    v_thm_4807_ = v___x_4792_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 8, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_levelParams_4783_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_proof_4784_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 2, v_numParams_4785_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 3, v_patterns_4786_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 4, v_tail_4794_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 5, v_origin_4787_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 6, v_kind_4788_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 7, v_cnstrs_4790_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4837_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        v_minIndexable_4789_,
                    );
                    v_thm_4807_ = v_reuseFailAlloc_4837_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4808_ = lean_box(0);
                lean_inc_ref(v_origin_4787_);
                v_origins_4809_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_4800_, v_origin_4787_, v___x_4808_);
                v_erased_4810_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_4801_, v_origin_4787_);
                v___x_4830_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_4799_, v_constName_4798_);
                if lean_obj_tag(v___x_4830_) == 1 {
                    v_val_4831_ = lean_ctor_get(v___x_4830_, 0);
                    lean_inc(v_val_4831_);
                    lean_dec_ref_known(v___x_4830_, 1);
                    lean_inc_ref(v_thm_4807_);
                    v___x_4832_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4832_, 0, v_thm_4807_);
                    lean_ctor_set(v___x_4832_, 1, v_val_4831_);
                    v___x_4833_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4799_, v_constName_4798_, v___x_4832_);
                    v___y_4812_ = v___x_4833_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v___x_4830_);
                    v___x_4834_ = lean_box(0);
                    lean_inc_ref(v_thm_4807_);
                    v___x_4835_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4835_, 0, v_thm_4807_);
                    lean_ctor_set(v___x_4835_, 1, v___x_4834_);
                    v___x_4836_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4799_, v_constName_4798_, v___x_4835_);
                    v___y_4812_ = v___x_4836_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4813_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_4802_, v_origin_4787_);
                if lean_obj_tag(v___x_4813_) == 1 {
                    v_val_4814_ = lean_ctor_get(v___x_4813_, 0);
                    lean_inc(v_val_4814_);
                    lean_dec_ref_known(v___x_4813_, 1);
                    if v_isShared_4797_ == 0 {
                        lean_ctor_set(v___x_4796_, 1, v_val_4814_);
                        lean_ctor_set(v___x_4796_, 0, v_thm_4807_);
                        v___x_4816_ = v___x_4796_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_thm_4807_);
                        lean_ctor_set(v_reuseFailAlloc_4821_, 1, v_val_4814_);
                        v___x_4816_ = v_reuseFailAlloc_4821_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4813_);
                    v___x_4822_ = lean_box(0);
                    if v_isShared_4797_ == 0 {
                        lean_ctor_set(v___x_4796_, 1, v___x_4822_);
                        lean_ctor_set(v___x_4796_, 0, v_thm_4807_);
                        v___x_4824_ = v___x_4796_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_thm_4807_);
                        lean_ctor_set(v_reuseFailAlloc_4829_, 1, v___x_4822_);
                        v___x_4824_ = v_reuseFailAlloc_4829_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4817_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_4802_, v_origin_4787_, v___x_4816_);
                if v_isShared_4805_ == 0 {
                    lean_ctor_set(v___x_4804_, 3, v___x_4817_);
                    lean_ctor_set(v___x_4804_, 2, v_erased_4810_);
                    lean_ctor_set(v___x_4804_, 1, v_origins_4809_);
                    lean_ctor_set(v___x_4804_, 0, v___y_4812_);
                    v___x_4819_ = v___x_4804_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___y_4812_);
                    lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_origins_4809_);
                    lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_erased_4810_);
                    lean_ctor_set(v_reuseFailAlloc_4820_, 3, v___x_4817_);
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
                    lean_ctor_set(v___x_4804_, 3, v___x_4825_);
                    lean_ctor_set(v___x_4804_, 2, v_erased_4810_);
                    lean_ctor_set(v___x_4804_, 1, v_origins_4809_);
                    lean_ctor_set(v___x_4804_, 0, v___y_4812_);
                    v___x_4827_ = v___x_4804_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___y_4812_);
                    lean_ctor_set(v_reuseFailAlloc_4828_, 1, v_origins_4809_);
                    lean_ctor_set(v_reuseFailAlloc_4828_, 2, v_erased_4810_);
                    lean_ctor_set(v_reuseFailAlloc_4828_, 3, v___x_4825_);
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
    mut v_msg_4843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    v___f_4844_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0;
    v___f_4845_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1;
    v___f_4846_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2;
    v___f_4847_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3;
    v___f_4848_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4;
    v___f_4849_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5;
    v___f_4850_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6;
    v___x_4851_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4851_, 0, v___f_4844_);
    lean_ctor_set(v___x_4851_, 1, v___f_4845_);
    v___x_4852_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4852_, 0, v___x_4851_);
    lean_ctor_set(v___x_4852_, 1, v___f_4846_);
    lean_ctor_set(v___x_4852_, 2, v___f_4847_);
    lean_ctor_set(v___x_4852_, 3, v___f_4848_);
    lean_ctor_set(v___x_4852_, 4, v___f_4849_);
    v___x_4853_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4853_, 0, v___x_4852_);
    lean_ctor_set(v___x_4853_, 1, v___f_4850_);
    v___x_4854_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once), _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
    v___x_4855_ = l_instInhabitedOfMonad___redArg(v___x_4853_, v___x_4854_);
    v___x_4856_ = lean_panic_fn_borrowed(v___x_4855_, v_msg_4843_);
    lean_dec(v___x_4855_);
    return v___x_4856_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(
    mut v_s_4857_: *mut LeanObject,
    mut v_thm_4858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_symbols_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v_tail_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4873_: u8 = 0;
    let mut v_constName_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_smap_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origins_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_erased_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_omap_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v_thm_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origins_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_erased_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v_unused_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4917_: u8 = 0;
    let mut v_unused_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_symbols_4862_ = lean_ctor_get(v_thm_4858_, 2);
                lean_inc(v_symbols_4862_);
                if lean_obj_tag(v_symbols_4862_) == 1 {
                    v_head_4863_ = lean_ctor_get(v_symbols_4862_, 0);
                    lean_inc(v_head_4863_);
                    if lean_obj_tag(v_head_4863_) == 2 {
                        v_levelParams_4864_ = lean_ctor_get(v_thm_4858_, 0);
                        v_proof_4865_ = lean_ctor_get(v_thm_4858_, 1);
                        v_origin_4866_ = lean_ctor_get(v_thm_4858_, 3);
                        v_isSharedCheck_4917_ = (!lean_is_exclusive(v_thm_4858_)) as u8;
                        if v_isSharedCheck_4917_ == 0 {
                            v_unused_4918_ = lean_ctor_get(v_thm_4858_, 2);
                            lean_dec(v_unused_4918_);
                            v___x_4868_ = v_thm_4858_;
                            v_isShared_4869_ = v_isSharedCheck_4917_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_origin_4866_);
                            lean_inc(v_proof_4865_);
                            lean_inc(v_levelParams_4864_);
                            lean_dec(v_thm_4858_);
                            v___x_4868_ = lean_box(0);
                            v_isShared_4869_ = v_isSharedCheck_4917_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_symbols_4862_, 2);
                        lean_dec(v_head_4863_);
                        lean_dec_ref(v_thm_4858_);
                        lean_dec_ref(v_s_4857_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_symbols_4862_);
                    lean_dec_ref(v_thm_4858_);
                    lean_dec_ref(v_s_4857_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4860_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once), _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
                v___x_4861_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_4860_);
                return v___x_4861_;
            }
            2 => {
                v_tail_4870_ = lean_ctor_get(v_symbols_4862_, 1);
                v_isSharedCheck_4915_ = (!lean_is_exclusive(v_symbols_4862_)) as u8;
                if v_isSharedCheck_4915_ == 0 {
                    v_unused_4916_ = lean_ctor_get(v_symbols_4862_, 0);
                    lean_dec(v_unused_4916_);
                    v___x_4872_ = v_symbols_4862_;
                    v_isShared_4873_ = v_isSharedCheck_4915_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_tail_4870_);
                    lean_dec(v_symbols_4862_);
                    v___x_4872_ = lean_box(0);
                    v_isShared_4873_ = v_isSharedCheck_4915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_constName_4874_ = lean_ctor_get(v_head_4863_, 0);
                lean_inc(v_constName_4874_);
                lean_dec_ref_known(v_head_4863_, 1);
                v_smap_4875_ = lean_ctor_get(v_s_4857_, 0);
                v_origins_4876_ = lean_ctor_get(v_s_4857_, 1);
                v_erased_4877_ = lean_ctor_get(v_s_4857_, 2);
                v_omap_4878_ = lean_ctor_get(v_s_4857_, 3);
                v_isSharedCheck_4914_ = (!lean_is_exclusive(v_s_4857_)) as u8;
                if v_isSharedCheck_4914_ == 0 {
                    v___x_4880_ = v_s_4857_;
                    v_isShared_4881_ = v_isSharedCheck_4914_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_omap_4878_);
                    lean_inc(v_erased_4877_);
                    lean_inc(v_origins_4876_);
                    lean_inc(v_smap_4875_);
                    lean_dec(v_s_4857_);
                    v___x_4880_ = lean_box(0);
                    v_isShared_4881_ = v_isSharedCheck_4914_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v_origin_4866_);
                if v_isShared_4869_ == 0 {
                    lean_ctor_set(v___x_4868_, 2, v_tail_4870_);
                    v_thm_4883_ = v___x_4868_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_levelParams_4864_);
                    lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_proof_4865_);
                    lean_ctor_set(v_reuseFailAlloc_4913_, 2, v_tail_4870_);
                    lean_ctor_set(v_reuseFailAlloc_4913_, 3, v_origin_4866_);
                    v_thm_4883_ = v_reuseFailAlloc_4913_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4884_ = lean_box(0);
                lean_inc_ref(v_origin_4866_);
                v_origins_4885_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_4876_, v_origin_4866_, v___x_4884_);
                v_erased_4886_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_4877_, v_origin_4866_);
                v___x_4906_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_4875_, v_constName_4874_);
                if lean_obj_tag(v___x_4906_) == 1 {
                    v_val_4907_ = lean_ctor_get(v___x_4906_, 0);
                    lean_inc(v_val_4907_);
                    lean_dec_ref_known(v___x_4906_, 1);
                    lean_inc_ref(v_thm_4883_);
                    v___x_4908_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4908_, 0, v_thm_4883_);
                    lean_ctor_set(v___x_4908_, 1, v_val_4907_);
                    v___x_4909_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4875_, v_constName_4874_, v___x_4908_);
                    v___y_4888_ = v___x_4909_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v___x_4906_);
                    v___x_4910_ = lean_box(0);
                    lean_inc_ref(v_thm_4883_);
                    v___x_4911_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4911_, 0, v_thm_4883_);
                    lean_ctor_set(v___x_4911_, 1, v___x_4910_);
                    v___x_4912_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_4875_, v_constName_4874_, v___x_4911_);
                    v___y_4888_ = v___x_4912_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4889_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_4878_, v_origin_4866_);
                if lean_obj_tag(v___x_4889_) == 1 {
                    v_val_4890_ = lean_ctor_get(v___x_4889_, 0);
                    lean_inc(v_val_4890_);
                    lean_dec_ref_known(v___x_4889_, 1);
                    if v_isShared_4873_ == 0 {
                        lean_ctor_set(v___x_4872_, 1, v_val_4890_);
                        lean_ctor_set(v___x_4872_, 0, v_thm_4883_);
                        v___x_4892_ = v___x_4872_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_thm_4883_);
                        lean_ctor_set(v_reuseFailAlloc_4897_, 1, v_val_4890_);
                        v___x_4892_ = v_reuseFailAlloc_4897_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4889_);
                    v___x_4898_ = lean_box(0);
                    if v_isShared_4873_ == 0 {
                        lean_ctor_set(v___x_4872_, 1, v___x_4898_);
                        lean_ctor_set(v___x_4872_, 0, v_thm_4883_);
                        v___x_4900_ = v___x_4872_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_thm_4883_);
                        lean_ctor_set(v_reuseFailAlloc_4905_, 1, v___x_4898_);
                        v___x_4900_ = v_reuseFailAlloc_4905_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4893_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_4878_, v_origin_4866_, v___x_4892_);
                if v_isShared_4881_ == 0 {
                    lean_ctor_set(v___x_4880_, 3, v___x_4893_);
                    lean_ctor_set(v___x_4880_, 2, v_erased_4886_);
                    lean_ctor_set(v___x_4880_, 1, v_origins_4885_);
                    lean_ctor_set(v___x_4880_, 0, v___y_4888_);
                    v___x_4895_ = v___x_4880_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___y_4888_);
                    lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_origins_4885_);
                    lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_erased_4886_);
                    lean_ctor_set(v_reuseFailAlloc_4896_, 3, v___x_4893_);
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
                    lean_ctor_set(v___x_4880_, 3, v___x_4901_);
                    lean_ctor_set(v___x_4880_, 2, v_erased_4886_);
                    lean_ctor_set(v___x_4880_, 1, v_origins_4885_);
                    lean_ctor_set(v___x_4880_, 0, v___y_4888_);
                    v___x_4903_ = v___x_4880_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___y_4888_);
                    lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_origins_4885_);
                    lean_ctor_set(v_reuseFailAlloc_4904_, 2, v_erased_4886_);
                    lean_ctor_set(v_reuseFailAlloc_4904_, 3, v___x_4901_);
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
    mut v_s_4919_: *mut LeanObject,
    mut v_e_4920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extThms_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funCC_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4929_: u8 = 0;
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4935_: u8 = 0;
    let mut v_declName_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extThms_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funCC_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_declName_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eager_4951_: u8 = 0;
    let mut v_casesTypes_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extThms_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funCC_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_thm_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extThms_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funCC_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4974_: u8 = 0;
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4979_: u8 = 0;
    let mut v_thm_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extThms_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funCC_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_4920_) {
                0 => {
                    v_declName_4921_ = lean_ctor_get(v_e_4920_, 0);
                    lean_inc(v_declName_4921_);
                    lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4922_ = lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4923_ = lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4924_ = lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4925_ = lean_ctor_get(v_s_4919_, 3);
                    v_inj_4926_ = lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4935_ = (!lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4935_ == 0 {
                        v___x_4928_ = v_s_4919_;
                        v_isShared_4929_ = v_isSharedCheck_4935_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_inj_4926_);
                        lean_inc(v_ematch_4925_);
                        lean_inc(v_funCC_4924_);
                        lean_inc(v_extThms_4923_);
                        lean_inc(v_casesTypes_4922_);
                        lean_dec(v_s_4919_);
                        v___x_4928_ = lean_box(0);
                        v_isShared_4929_ = v_isSharedCheck_4935_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_declName_4936_ = lean_ctor_get(v_e_4920_, 0);
                    lean_inc(v_declName_4936_);
                    lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4937_ = lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4938_ = lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4939_ = lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4940_ = lean_ctor_get(v_s_4919_, 3);
                    v_inj_4941_ = lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4949_ = (!lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4943_ = v_s_4919_;
                        v_isShared_4944_ = v_isSharedCheck_4949_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_inj_4941_);
                        lean_inc(v_ematch_4940_);
                        lean_inc(v_funCC_4939_);
                        lean_inc(v_extThms_4938_);
                        lean_inc(v_casesTypes_4937_);
                        lean_dec(v_s_4919_);
                        v___x_4943_ = lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4949_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_declName_4950_ = lean_ctor_get(v_e_4920_, 0);
                    lean_inc(v_declName_4950_);
                    v_eager_4951_ = lean_ctor_get_uint8(
                        v_e_4920_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4952_ = lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4953_ = lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4954_ = lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4955_ = lean_ctor_get(v_s_4919_, 3);
                    v_inj_4956_ = lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4965_ = (!lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4965_ == 0 {
                        v___x_4958_ = v_s_4919_;
                        v_isShared_4959_ = v_isSharedCheck_4965_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_inj_4956_);
                        lean_inc(v_ematch_4955_);
                        lean_inc(v_funCC_4954_);
                        lean_inc(v_extThms_4953_);
                        lean_inc(v_casesTypes_4952_);
                        lean_dec(v_s_4919_);
                        v___x_4958_ = lean_box(0);
                        v_isShared_4959_ = v_isSharedCheck_4965_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_thm_4966_ = lean_ctor_get(v_e_4920_, 0);
                    lean_inc_ref(v_thm_4966_);
                    lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4967_ = lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4968_ = lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4969_ = lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4970_ = lean_ctor_get(v_s_4919_, 3);
                    v_inj_4971_ = lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4979_ = (!lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4979_ == 0 {
                        v___x_4973_ = v_s_4919_;
                        v_isShared_4974_ = v_isSharedCheck_4979_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_inj_4971_);
                        lean_inc(v_ematch_4970_);
                        lean_inc(v_funCC_4969_);
                        lean_inc(v_extThms_4968_);
                        lean_inc(v_casesTypes_4967_);
                        lean_dec(v_s_4919_);
                        v___x_4973_ = lean_box(0);
                        v_isShared_4974_ = v_isSharedCheck_4979_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    v_thm_4980_ = lean_ctor_get(v_e_4920_, 0);
                    lean_inc_ref(v_thm_4980_);
                    lean_dec_ref_known(v_e_4920_, 1);
                    v_casesTypes_4981_ = lean_ctor_get(v_s_4919_, 0);
                    v_extThms_4982_ = lean_ctor_get(v_s_4919_, 1);
                    v_funCC_4983_ = lean_ctor_get(v_s_4919_, 2);
                    v_ematch_4984_ = lean_ctor_get(v_s_4919_, 3);
                    v_inj_4985_ = lean_ctor_get(v_s_4919_, 4);
                    v_isSharedCheck_4993_ = (!lean_is_exclusive(v_s_4919_)) as u8;
                    if v_isSharedCheck_4993_ == 0 {
                        v___x_4987_ = v_s_4919_;
                        v_isShared_4988_ = v_isSharedCheck_4993_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_inj_4985_);
                        lean_inc(v_ematch_4984_);
                        lean_inc(v_funCC_4983_);
                        lean_inc(v_extThms_4982_);
                        lean_inc(v_casesTypes_4981_);
                        lean_dec(v_s_4919_);
                        v___x_4987_ = lean_box(0);
                        v_isShared_4988_ = v_isSharedCheck_4993_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4930_ = lean_box(0);
                v___x_4931_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_4923_, v_declName_4921_, v___x_4930_);
                if v_isShared_4929_ == 0 {
                    lean_ctor_set(v___x_4928_, 1, v___x_4931_);
                    v___x_4933_ = v___x_4928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_casesTypes_4922_);
                    lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___x_4931_);
                    lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_funCC_4924_);
                    lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_ematch_4925_);
                    lean_ctor_set(v_reuseFailAlloc_4934_, 4, v_inj_4926_);
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
                    lean_ctor_set(v___x_4943_, 2, v___x_4945_);
                    v___x_4947_ = v___x_4943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_casesTypes_4937_);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 1, v_extThms_4938_);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 2, v___x_4945_);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 3, v_ematch_4940_);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 4, v_inj_4941_);
                    v___x_4947_ = v_reuseFailAlloc_4948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4947_;
            }
            5 => {
                v___x_4960_ = lean_box((v_eager_4951_) as usize);
                v___x_4961_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_4952_, v_declName_4950_, v___x_4960_);
                if v_isShared_4959_ == 0 {
                    lean_ctor_set(v___x_4958_, 0, v___x_4961_);
                    v___x_4963_ = v___x_4958_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4964_, 0, v___x_4961_);
                    lean_ctor_set(v_reuseFailAlloc_4964_, 1, v_extThms_4953_);
                    lean_ctor_set(v_reuseFailAlloc_4964_, 2, v_funCC_4954_);
                    lean_ctor_set(v_reuseFailAlloc_4964_, 3, v_ematch_4955_);
                    lean_ctor_set(v_reuseFailAlloc_4964_, 4, v_inj_4956_);
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
                    lean_ctor_set(v___x_4973_, 3, v___x_4975_);
                    v___x_4977_ = v___x_4973_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_casesTypes_4967_);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 1, v_extThms_4968_);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 2, v_funCC_4969_);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 3, v___x_4975_);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 4, v_inj_4971_);
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
                    lean_ctor_set(v___x_4987_, 4, v___x_4989_);
                    v___x_4991_ = v___x_4987_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_casesTypes_4981_);
                    lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_extThms_4982_);
                    lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_funCC_4983_);
                    lean_ctor_set(v_reuseFailAlloc_4992_, 3, v_ematch_4984_);
                    lean_ctor_set(v_reuseFailAlloc_4992_, 4, v___x_4989_);
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
    mut v_00_u03b2_4994_: *mut LeanObject,
    mut v_x_4995_: *mut LeanObject,
    mut v_x_4996_: *mut LeanObject,
    mut v_x_4997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    v___x_4998_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_4995_, v_x_4996_, v_x_4997_);
    return v___x_4998_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(
    mut v_00_u03b2_4999_: *mut LeanObject,
    mut v_x_5000_: *mut LeanObject,
    mut v_x_5001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    v___x_5002_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_5000_, v_x_5001_);
    return v___x_5002_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(
    mut v_00_u03b2_5003_: *mut LeanObject,
    mut v_x_5004_: *mut LeanObject,
    mut v_x_5005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5006_: *mut LeanObject = core::ptr::null_mut();
    v_res_5006_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_5003_, v_x_5004_, v_x_5005_);
    lean_dec_ref(v_x_5005_);
    return v_res_5006_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(
    mut v_00_u03b2_5007_: *mut LeanObject,
    mut v_x_5008_: *mut LeanObject,
    mut v_x_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    v___x_5010_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_5008_, v_x_5009_);
    return v___x_5010_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(
    mut v_00_u03b2_5011_: *mut LeanObject,
    mut v_x_5012_: *mut LeanObject,
    mut v_x_5013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5014_: *mut LeanObject = core::ptr::null_mut();
    v_res_5014_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_5011_, v_x_5012_, v_x_5013_);
    lean_dec_ref(v_x_5013_);
    lean_dec_ref(v_x_5012_);
    return v_res_5014_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(
    mut v_00_u03b2_5015_: *mut LeanObject,
    mut v_x_5016_: *mut LeanObject,
    mut v_x_5017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    v___x_5018_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_5016_, v_x_5017_);
    return v___x_5018_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(
    mut v_00_u03b2_5019_: *mut LeanObject,
    mut v_x_5020_: *mut LeanObject,
    mut v_x_5021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5022_: *mut LeanObject = core::ptr::null_mut();
    v_res_5022_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_5019_, v_x_5020_, v_x_5021_);
    lean_dec(v_x_5021_);
    lean_dec_ref(v_x_5020_);
    return v_res_5022_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5023_: *mut LeanObject,
    mut v_x_5024_: *mut LeanObject,
    mut v_x_5025_: usize,
    mut v_x_5026_: usize,
    mut v_x_5027_: *mut LeanObject,
    mut v_x_5028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    v___x_5029_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_5024_, v_x_5025_, v_x_5026_, v_x_5027_, v_x_5028_);
    return v___x_5029_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_5030_: *mut LeanObject,
    mut v_x_5031_: *mut LeanObject,
    mut v_x_5032_: *mut LeanObject,
    mut v_x_5033_: *mut LeanObject,
    mut v_x_5034_: *mut LeanObject,
    mut v_x_5035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2302__boxed_5036_: usize = 0;
    let mut v_x_2303__boxed_5037_: usize = 0;
    let mut v_res_5038_: *mut LeanObject = core::ptr::null_mut();
    v_x_2302__boxed_5036_ = lean_unbox_usize(v_x_5032_);
    lean_dec(v_x_5032_);
    v_x_2303__boxed_5037_ = lean_unbox_usize(v_x_5033_);
    lean_dec(v_x_5033_);
    v_res_5038_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_5030_, v_x_5031_, v_x_2302__boxed_5036_, v_x_2303__boxed_5037_, v_x_5034_, v_x_5035_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(
    mut v_00_u03b2_5039_: *mut LeanObject,
    mut v_x_5040_: *mut LeanObject,
    mut v_x_5041_: usize,
    mut v_x_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    v___x_5043_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_5040_, v_x_5041_, v_x_5042_);
    return v___x_5043_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_5044_: *mut LeanObject,
    mut v_x_5045_: *mut LeanObject,
    mut v_x_5046_: *mut LeanObject,
    mut v_x_5047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2319__boxed_5048_: usize = 0;
    let mut v_res_5049_: *mut LeanObject = core::ptr::null_mut();
    v_x_2319__boxed_5048_ = lean_unbox_usize(v_x_5046_);
    lean_dec(v_x_5046_);
    v_res_5049_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_5044_, v_x_5045_, v_x_2319__boxed_5048_, v_x_5047_);
    lean_dec_ref(v_x_5047_);
    return v_res_5049_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(
    mut v_00_u03b2_5050_: *mut LeanObject,
    mut v_x_5051_: *mut LeanObject,
    mut v_x_5052_: usize,
    mut v_x_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    v___x_5054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_5051_, v_x_5052_, v_x_5053_);
    return v___x_5054_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(
    mut v_00_u03b2_5055_: *mut LeanObject,
    mut v_x_5056_: *mut LeanObject,
    mut v_x_5057_: *mut LeanObject,
    mut v_x_5058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2330__boxed_5059_: usize = 0;
    let mut v_res_5060_: *mut LeanObject = core::ptr::null_mut();
    v_x_2330__boxed_5059_ = lean_unbox_usize(v_x_5057_);
    lean_dec(v_x_5057_);
    v_res_5060_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_5055_, v_x_5056_, v_x_2330__boxed_5059_, v_x_5058_);
    lean_dec_ref(v_x_5058_);
    lean_dec_ref(v_x_5056_);
    return v_res_5060_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(
    mut v_00_u03b2_5061_: *mut LeanObject,
    mut v_x_5062_: *mut LeanObject,
    mut v_x_5063_: usize,
    mut v_x_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v___x_5065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_5062_, v_x_5063_, v_x_5064_);
    return v___x_5065_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(
    mut v_00_u03b2_5066_: *mut LeanObject,
    mut v_x_5067_: *mut LeanObject,
    mut v_x_5068_: *mut LeanObject,
    mut v_x_5069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2341__boxed_5070_: usize = 0;
    let mut v_res_5071_: *mut LeanObject = core::ptr::null_mut();
    v_x_2341__boxed_5070_ = lean_unbox_usize(v_x_5068_);
    lean_dec(v_x_5068_);
    v_res_5071_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_5066_, v_x_5067_, v_x_2341__boxed_5070_, v_x_5069_);
    lean_dec(v_x_5069_);
    lean_dec_ref(v_x_5067_);
    return v_res_5071_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_5072_: *mut LeanObject,
    mut v_n_5073_: *mut LeanObject,
    mut v_k_5074_: *mut LeanObject,
    mut v_v_5075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    v___x_5076_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_5073_, v_k_5074_, v_v_5075_);
    return v___x_5076_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(
    mut v_00_u03b2_5077_: *mut LeanObject,
    mut v_depth_5078_: usize,
    mut v_keys_5079_: *mut LeanObject,
    mut v_vals_5080_: *mut LeanObject,
    mut v_heq_5081_: *mut LeanObject,
    mut v_i_5082_: *mut LeanObject,
    mut v_entries_5083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    v___x_5084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_5078_, v_keys_5079_, v_vals_5080_, v_i_5082_, v_entries_5083_);
    return v___x_5084_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_5085_: *mut LeanObject,
    mut v_depth_5086_: *mut LeanObject,
    mut v_keys_5087_: *mut LeanObject,
    mut v_vals_5088_: *mut LeanObject,
    mut v_heq_5089_: *mut LeanObject,
    mut v_i_5090_: *mut LeanObject,
    mut v_entries_5091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5092_: usize = 0;
    let mut v_res_5093_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5092_ = lean_unbox_usize(v_depth_5086_);
    lean_dec(v_depth_5086_);
    v_res_5093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_5085_, v_depth_boxed_5092_, v_keys_5087_, v_vals_5088_, v_heq_5089_, v_i_5090_, v_entries_5091_);
    lean_dec_ref(v_vals_5088_);
    lean_dec_ref(v_keys_5087_);
    return v_res_5093_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(
    mut v_00_u03b2_5094_: *mut LeanObject,
    mut v_keys_5095_: *mut LeanObject,
    mut v_vals_5096_: *mut LeanObject,
    mut v_heq_5097_: *mut LeanObject,
    mut v_i_5098_: *mut LeanObject,
    mut v_k_5099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    v___x_5100_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_5095_, v_vals_5096_, v_i_5098_, v_k_5099_);
    return v___x_5100_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(
    mut v_00_u03b2_5101_: *mut LeanObject,
    mut v_keys_5102_: *mut LeanObject,
    mut v_vals_5103_: *mut LeanObject,
    mut v_heq_5104_: *mut LeanObject,
    mut v_i_5105_: *mut LeanObject,
    mut v_k_5106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5107_: *mut LeanObject = core::ptr::null_mut();
    v_res_5107_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_5101_, v_keys_5102_, v_vals_5103_, v_heq_5104_, v_i_5105_, v_k_5106_);
    lean_dec_ref(v_k_5106_);
    lean_dec_ref(v_vals_5103_);
    lean_dec_ref(v_keys_5102_);
    return v_res_5107_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(
    mut v_00_u03b2_5108_: *mut LeanObject,
    mut v_keys_5109_: *mut LeanObject,
    mut v_vals_5110_: *mut LeanObject,
    mut v_heq_5111_: *mut LeanObject,
    mut v_i_5112_: *mut LeanObject,
    mut v_k_5113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    v___x_5114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_5109_, v_vals_5110_, v_i_5112_, v_k_5113_);
    return v___x_5114_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(
    mut v_00_u03b2_5115_: *mut LeanObject,
    mut v_keys_5116_: *mut LeanObject,
    mut v_vals_5117_: *mut LeanObject,
    mut v_heq_5118_: *mut LeanObject,
    mut v_i_5119_: *mut LeanObject,
    mut v_k_5120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5121_: *mut LeanObject = core::ptr::null_mut();
    v_res_5121_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_5115_, v_keys_5116_, v_vals_5117_, v_heq_5118_, v_i_5119_, v_k_5120_);
    lean_dec(v_k_5120_);
    lean_dec_ref(v_vals_5117_);
    lean_dec_ref(v_keys_5116_);
    return v_res_5121_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(
    mut v_00_u03b2_5122_: *mut LeanObject,
    mut v_x_5123_: *mut LeanObject,
    mut v_x_5124_: *mut LeanObject,
    mut v_x_5125_: *mut LeanObject,
    mut v_x_5126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    v___x_5127_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_5123_, v_x_5124_, v_x_5125_, v_x_5126_);
    return v___x_5127_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    v___x_5154_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__10;
    v___x_5155_ = l_Lean_mkAtom(v___x_5154_);
    return v___x_5155_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    v___x_5156_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12,
    );
    v___x_5157_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5158_ = lean_array_push(v___x_5157_, v___x_5156_);
    return v___x_5158_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    v___x_5167_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__17;
    v___x_5168_ = l_Lean_mkAtom(v___x_5167_);
    return v___x_5168_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    v___x_5169_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18,
    );
    v___x_5170_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5171_ = lean_array_push(v___x_5170_, v___x_5169_);
    return v___x_5171_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    v___x_5172_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19,
    );
    v___x_5173_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__16;
    v___x_5174_ = lean_box(2);
    v___x_5175_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5175_, 0, v___x_5174_);
    lean_ctor_set(v___x_5175_, 1, v___x_5173_);
    lean_ctor_set(v___x_5175_, 2, v___x_5172_);
    return v___x_5175_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    v___x_5176_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20,
    );
    v___x_5177_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13,
    );
    v___x_5178_ = lean_array_push(v___x_5177_, v___x_5176_);
    return v___x_5178_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    v___x_5179_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21,
    );
    v___x_5180_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__11;
    v___x_5181_ = lean_box(2);
    v___x_5182_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5182_, 0, v___x_5181_);
    lean_ctor_set(v___x_5182_, 1, v___x_5180_);
    lean_ctor_set(v___x_5182_, 2, v___x_5179_);
    return v___x_5182_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    v___x_5183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22,
    );
    v___x_5184_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5185_ = lean_array_push(v___x_5184_, v___x_5183_);
    return v___x_5185_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    v___x_5186_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23,
    );
    v___x_5187_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__9;
    v___x_5188_ = lean_box(2);
    v___x_5189_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5189_, 0, v___x_5188_);
    lean_ctor_set(v___x_5189_, 1, v___x_5187_);
    lean_ctor_set(v___x_5189_, 2, v___x_5186_);
    return v___x_5189_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    v___x_5190_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24,
    );
    v___x_5191_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5192_ = lean_array_push(v___x_5191_, v___x_5190_);
    return v___x_5192_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    v___x_5193_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25,
    );
    v___x_5194_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__7;
    v___x_5195_ = lean_box(2);
    v___x_5196_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5196_, 0, v___x_5195_);
    lean_ctor_set(v___x_5196_, 1, v___x_5194_);
    lean_ctor_set(v___x_5196_, 2, v___x_5193_);
    return v___x_5196_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    v___x_5197_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26,
    );
    v___x_5198_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__5;
    v___x_5199_ = lean_array_push(v___x_5198_, v___x_5197_);
    return v___x_5199_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    v___x_5200_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27,
    );
    v___x_5201_ = l_Lean_Meta_Grind_mkExtension___auto__1___closed__4;
    v___x_5202_ = lean_box(2);
    v___x_5203_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5203_, 0, v___x_5202_);
    lean_ctor_set(v___x_5203_, 1, v___x_5201_);
    lean_ctor_set(v___x_5203_, 2, v___x_5200_);
    return v___x_5203_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___auto__1() -> *mut LeanObject {
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    v___x_5204_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once),
        _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28,
    );
    return v___x_5204_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(
    mut v_msg_5205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    v___x_5206_ = lean_box(0);
    v___x_5207_ = lean_panic_fn_borrowed(v___x_5206_, v_msg_5205_);
    return v___x_5207_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    v___x_5210_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2;
    v___x_5211_ = lean_unsigned_to_nat(17);
    v___x_5212_ = lean_unsigned_to_nat(203);
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
    mut v_x_5216_: *mut LeanObject,
    mut v_e_5217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: u8 = 0;
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thm_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thm_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_5217_) {
                3 => {
                    v_thm_5226_ = lean_ctor_get(v_e_5217_, 0);
                    v_origin_5227_ = lean_ctor_get(v_thm_5226_, 5);
                    if lean_obj_tag(v_origin_5227_) == 0 {
                        v_declName_5228_ = lean_ctor_get(v_origin_5227_, 0);
                        lean_inc(v_declName_5228_);
                        v___y_5219_ = v_declName_5228_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5229_ = lean_obj_once(
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
                    v_thm_5231_ = lean_ctor_get(v_e_5217_, 0);
                    v_origin_5232_ = lean_ctor_get(v_thm_5231_, 3);
                    if lean_obj_tag(v_origin_5232_) == 0 {
                        v_declName_5233_ = lean_ctor_get(v_origin_5232_, 0);
                        lean_inc(v_declName_5233_);
                        v___y_5219_ = v_declName_5233_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5234_ = lean_obj_once(
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
                    v_declName_5236_ = lean_ctor_get(v_e_5217_, 0);
                    lean_inc(v_declName_5236_);
                    v___y_5219_ = v_declName_5236_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_5220_ = l_Lean_isPrivateName(v___y_5219_);
                lean_dec(v___y_5219_);
                if v___x_5220_ == 0 {
                    v___x_5221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5221_, 0, v_e_5217_);
                    lean_inc_ref_n(v___x_5221_, 2);
                    v___x_5222_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5222_, 0, v___x_5221_);
                    lean_ctor_set(v___x_5222_, 1, v___x_5221_);
                    lean_ctor_set(v___x_5222_, 2, v___x_5221_);
                    return v___x_5222_;
                } else {
                    v___x_5223_ = lean_box(0);
                    v___x_5224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5224_, 0, v_e_5217_);
                    v___x_5225_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5225_, 0, v___x_5223_);
                    lean_ctor_set(v___x_5225_, 1, v___x_5223_);
                    lean_ctor_set(v___x_5225_, 2, v___x_5224_);
                    return v___x_5225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___lam__0___boxed(
    mut v_x_5237_: *mut LeanObject,
    mut v_e_5238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5239_: *mut LeanObject = core::ptr::null_mut();
    v_res_5239_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_x_5237_, v_e_5238_);
    lean_dec_ref(v_x_5237_);
    return v_res_5239_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___lam__1(
    mut v___y_5240_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_5240_);
    return v___y_5240_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___lam__1___boxed(
    mut v___y_5241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5242_: *mut LeanObject = core::ptr::null_mut();
    v_res_5242_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_5241_);
    lean_dec_ref(v___y_5241_);
    return v_res_5242_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension(mut v_name_5246_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    v___f_5248_ = l_Lean_Meta_Grind_mkExtension___closed__0;
    v___f_5249_ = l_Lean_Meta_Grind_mkExtension___closed__1;
    v___x_5250_ = l_Lean_Meta_Grind_mkExtension___closed__2;
    v___x_5251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2,
    );
    v___x_5252_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_5252_, 0, v_name_5246_);
    lean_ctor_set(v___x_5252_, 1, v___x_5250_);
    lean_ctor_set(v___x_5252_, 2, v___x_5251_);
    lean_ctor_set(v___x_5252_, 3, v___f_5249_);
    lean_ctor_set(v___x_5252_, 4, v___f_5248_);
    v___x_5253_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_5252_);
    return v___x_5253_;
}
pub unsafe fn l_Lean_Meta_Grind_mkExtension___boxed(
    mut v_name_5254_: *mut LeanObject,
    mut v_a_5255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5256_: *mut LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Lean_Meta_Grind_mkExtension(v_name_5254_);
    return v_res_5256_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5257_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    v___x_5258_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
    v___x_5259_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5259_, 0, v___x_5258_);
    return v___x_5259_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    v___x_5260_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
    v___x_5261_ = lean_unsigned_to_nat(0);
    v___x_5262_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_5262_, 0, v___x_5261_);
    lean_ctor_set(v___x_5262_, 1, v___x_5261_);
    lean_ctor_set(v___x_5262_, 2, v___x_5261_);
    lean_ctor_set(v___x_5262_, 3, v___x_5261_);
    lean_ctor_set(v___x_5262_, 4, v___x_5260_);
    lean_ctor_set(v___x_5262_, 5, v___x_5260_);
    lean_ctor_set(v___x_5262_, 6, v___x_5260_);
    lean_ctor_set(v___x_5262_, 7, v___x_5260_);
    lean_ctor_set(v___x_5262_, 8, v___x_5260_);
    lean_ctor_set(v___x_5262_, 9, v___x_5260_);
    return v___x_5262_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    v___x_5263_ = lean_unsigned_to_nat(32);
    v___x_5264_ = lean_mk_empty_array_with_capacity(v___x_5263_);
    v___x_5265_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5265_, 0, v___x_5264_);
    return v___x_5265_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_5266_: usize = 0;
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    v___x_5266_ = 5usize;
    v___x_5267_ = lean_unsigned_to_nat(0);
    v___x_5268_ = lean_unsigned_to_nat(32);
    v___x_5269_ = lean_mk_empty_array_with_capacity(v___x_5268_);
    v___x_5270_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
    v___x_5271_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5271_, 0, v___x_5270_);
    lean_ctor_set(v___x_5271_, 1, v___x_5269_);
    lean_ctor_set(v___x_5271_, 2, v___x_5267_);
    lean_ctor_set(v___x_5271_, 3, v___x_5267_);
    lean_ctor_set_usize(v___x_5271_, 4, v___x_5266_);
    return v___x_5271_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    v___x_5272_ = lean_box(1);
    v___x_5273_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
    v___x_5274_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
    v___x_5275_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5275_, 0, v___x_5274_);
    lean_ctor_set(v___x_5275_, 1, v___x_5273_);
    lean_ctor_set(v___x_5275_, 2, v___x_5272_);
    return v___x_5275_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(
    mut v_msgData_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    v___x_5280_ = lean_st_ref_get(v___y_5278_);
    v_env_5281_ = lean_ctor_get(v___x_5280_, 0);
    lean_inc_ref(v_env_5281_);
    lean_dec(v___x_5280_);
    v_options_5282_ = lean_ctor_get(v___y_5277_, 2);
    v___x_5283_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
    v___x_5284_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_5282_);
    v___x_5285_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_5285_, 0, v_env_5281_);
    lean_ctor_set(v___x_5285_, 1, v___x_5283_);
    lean_ctor_set(v___x_5285_, 2, v___x_5284_);
    lean_ctor_set(v___x_5285_, 3, v_options_5282_);
    v___x_5286_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_5286_, 0, v___x_5285_);
    lean_ctor_set(v___x_5286_, 1, v_msgData_5276_);
    v___x_5287_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5287_, 0, v___x_5286_);
    return v___x_5287_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(
    mut v_msgData_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
    mut v___y_5290_: *mut LeanObject,
    mut v___y_5291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5292_: *mut LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_5288_, v___y_5289_, v___y_5290_);
    lean_dec(v___y_5290_);
    lean_dec_ref(v___y_5289_);
    return v_res_5292_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(
    mut v_msg_5293_: *mut LeanObject,
    mut v___y_5294_: *mut LeanObject,
    mut v___y_5295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5297_ = lean_ctor_get(v___y_5294_, 5);
                v___x_5298_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_5293_, v___y_5294_, v___y_5295_);
                v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
                v_isSharedCheck_5307_ = (!lean_is_exclusive(v___x_5298_)) as u8;
                if v_isSharedCheck_5307_ == 0 {
                    v___x_5301_ = v___x_5298_;
                    v_isShared_5302_ = v_isSharedCheck_5307_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5299_);
                    lean_dec(v___x_5298_);
                    v___x_5301_ = lean_box(0);
                    v_isShared_5302_ = v_isSharedCheck_5307_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5297_);
                v___x_5303_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5303_, 0, v_ref_5297_);
                lean_ctor_set(v___x_5303_, 1, v_a_5299_);
                if v_isShared_5302_ == 0 {
                    lean_ctor_set_tag(v___x_5301_, 1);
                    lean_ctor_set(v___x_5301_, 0, v___x_5303_);
                    v___x_5305_ = v___x_5301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5303_);
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
    mut v_msg_5308_: *mut LeanObject,
    mut v___y_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5312_: *mut LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_5308_, v___y_5309_, v___y_5310_);
    lean_dec(v___y_5310_);
    lean_dec_ref(v___y_5309_);
    return v_res_5312_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    v___x_5314_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0;
    v___x_5315_ = l_Lean_stringToMessageData(v___x_5314_);
    return v___x_5315_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    v___x_5317_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2;
    v___x_5318_ = l_Lean_stringToMessageData(v___x_5317_);
    return v___x_5318_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(
    mut v_declName_5319_: *mut LeanObject,
    mut v_a_5320_: *mut LeanObject,
    mut v_a_5321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: u8 = 0;
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    v___x_5323_ = lean_obj_once(
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
    v___x_5326_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5326_, 0, v___x_5323_);
    lean_ctor_set(v___x_5326_, 1, v___x_5325_);
    v___x_5327_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3,
    );
    v___x_5328_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5328_, 0, v___x_5326_);
    lean_ctor_set(v___x_5328_, 1, v___x_5327_);
    v___x_5329_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_5328_, v_a_5320_, v_a_5321_);
    return v___x_5329_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(
    mut v_declName_5330_: *mut LeanObject,
    mut v_a_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
    mut v_a_5333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5334_: *mut LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(
        v_declName_5330_,
        v_a_5331_,
        v_a_5332_,
    );
    lean_dec(v_a_5332_);
    lean_dec_ref(v_a_5331_);
    return v_res_5334_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(
    mut v_00_u03b1_5335_: *mut LeanObject,
    mut v_declName_5336_: *mut LeanObject,
    mut v_a_5337_: *mut LeanObject,
    mut v_a_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    v___x_5340_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(
        v_declName_5336_,
        v_a_5337_,
        v_a_5338_,
    );
    return v___x_5340_;
}
pub unsafe fn l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(
    mut v_00_u03b1_5341_: *mut LeanObject,
    mut v_declName_5342_: *mut LeanObject,
    mut v_a_5343_: *mut LeanObject,
    mut v_a_5344_: *mut LeanObject,
    mut v_a_5345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5346_: *mut LeanObject = core::ptr::null_mut();
    v_res_5346_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(
        v_00_u03b1_5341_,
        v_declName_5342_,
        v_a_5343_,
        v_a_5344_,
    );
    lean_dec(v_a_5344_);
    lean_dec_ref(v_a_5343_);
    return v_res_5346_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(
    mut v_00_u03b1_5347_: *mut LeanObject,
    mut v_msg_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
    mut v___y_5350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    v___x_5352_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_5348_, v___y_5349_, v___y_5350_);
    return v___x_5352_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(
    mut v_00_u03b1_5353_: *mut LeanObject,
    mut v_msg_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5358_: *mut LeanObject = core::ptr::null_mut();
    v_res_5358_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(
            v_00_u03b1_5353_,
            v_msg_5354_,
            v___y_5355_,
            v___y_5356_,
        );
    lean_dec(v___y_5356_);
    lean_dec_ref(v___y_5355_);
    return v_res_5358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_instInhabitedCasesTypes_default =
        _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCasesTypes_default);
    l_Lean_Meta_Grind_instInhabitedCasesTypes = _init_l_Lean_Meta_Grind_instInhabitedCasesTypes();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCasesTypes);
    l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default =
        _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default);
    l_Lean_Meta_Grind_instInhabitedSymbolPriorities =
        _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSymbolPriorities);
    l_Lean_Meta_Grind_instInhabitedCnstrRHS_default =
        _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default);
    l_Lean_Meta_Grind_instInhabitedCnstrRHS = _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCnstrRHS);
    l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default);
    l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint);
    l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default);
    l_Lean_Meta_Grind_instInhabitedEMatchTheorem =
        _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorem);
    l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default =
        _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default);
    l_Lean_Meta_Grind_instInhabitedInjectiveTheorem =
        _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedInjectiveTheorem);
    l_Lean_Meta_Grind_instInhabitedExtensionState_default =
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedExtensionState_default);
    l_Lean_Meta_Grind_instInhabitedExtensionState =
        _init_l_Lean_Meta_Grind_instInhabitedExtensionState();
    lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedExtensionState);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Extension(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Meta_Grind_mkExtension___auto__1 = _init_l_Lean_Meta_Grind_mkExtension___auto__1();
    lean_mark_persistent(l_Lean_Meta_Grind_mkExtension___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Extension(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
}

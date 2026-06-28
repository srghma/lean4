// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Attr
// Imports: Lean.Meta.Sym.Simp.Theorems Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Eqns
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_mkAtom, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey;
use crate::r#gen::Lean::Meta::Eqns::{
    initialize_Lean_Meta_Eqns, l_Lean_Meta_getEqnsFor_x3f, runtime_initialize_Lean_Meta_Eqns,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    initialize_Lean_Meta_Sym_Simp_Theorems,
    l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg, l_Lean_Meta_Sym_Simp_mkSymSimpExt,
    l_Lean_Meta_Sym_Simp_mkTheoremFromDecl, l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef,
    runtime_initialize_Lean_Meta_Sym_Simp_Theorems,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    initialize_Lean_Meta_Tactic_Simp_SimpTheorems, l_Lean_Meta_Simp_ignoreEquations,
    runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_ScopedEnvExtension_addCore___redArg;
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10_value: LeanStringObject<6> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15_value: LeanStringObject<9> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17_value: LeanStringObject<11> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0_value: LeanStringObject<52> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            69, 114, 97, 115, 105, 110, 103, 32, 96, 83, 121, 109, 46, 115, 105, 109, 112, 96, 32,
            97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 32, 105, 115, 32, 110, 111, 116, 32,
            115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 121, 101, 116, 46, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut LeanObject,
            72621647814721793 as *mut LeanObject,
            65793 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1: u64 = 0;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 96, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 116, 111, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            96, 58, 32, 78, 111, 32, 101, 113, 117, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111,
            114, 101, 109, 115, 32, 102, 111, 117, 110, 100, 46, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16_value: LeanStringObject<86> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 86,
        m_capacity: 86,
        m_length: 85,
        m_data: [
            96, 58, 32, 73, 116, 32, 105, 115, 32, 97, 32, 114, 101, 100, 117, 99, 105, 98, 108,
            101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 111, 114, 32, 112, 114,
            111, 106, 101, 99, 116, 105, 111, 110, 46, 32, 96, 83, 121, 109, 46, 115, 105, 109,
            112, 96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114,
            116, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 46, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18_value: LeanStringObject<68> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            96, 58, 32, 73, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112,
            111, 115, 105, 116, 105, 111, 110, 32, 110, 111, 114, 32, 97, 32, 100, 101, 102, 105,
            110, 105, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 101, 113, 117, 97, 116, 105,
            111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 46, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 121, 109, 95, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject,1027334672689396736 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 121, 109, 46, 115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 109, 83, 105, 109, 112, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject,13806531830123099675 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject,7173345859398835572 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1120_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0);
    v___x_1122_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1122_, 0, v___x_1121_);
    return v___x_1122_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1);
    v___x_1124_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1124_, 0, v___x_1123_);
    lean_ctor_set(v___x_1124_, 1, v___x_1123_);
    return v___x_1124_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v___x_1125_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1);
    v___x_1126_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1126_, 0, v___x_1125_);
    lean_ctor_set(v___x_1126_, 1, v___x_1125_);
    lean_ctor_set(v___x_1126_, 2, v___x_1125_);
    lean_ctor_set(v___x_1126_, 3, v___x_1125_);
    lean_ctor_set(v___x_1126_, 4, v___x_1125_);
    lean_ctor_set(v___x_1126_, 5, v___x_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(
    mut v_ext_1127_: *mut LeanObject,
    mut v_b_1128_: *mut LeanObject,
    mut v_kind_1129_: u8,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_unused_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1170_: u8 = 0;
    let mut v_unused_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_1134_ = lean_ctor_get(v___y_1131_, 6);
                v___x_1135_ = lean_st_ref_take(v___y_1132_);
                v_env_1136_ = lean_ctor_get(v___x_1135_, 0);
                v_nextMacroScope_1137_ = lean_ctor_get(v___x_1135_, 1);
                v_ngen_1138_ = lean_ctor_get(v___x_1135_, 2);
                v_auxDeclNGen_1139_ = lean_ctor_get(v___x_1135_, 3);
                v_traceState_1140_ = lean_ctor_get(v___x_1135_, 4);
                v_messages_1141_ = lean_ctor_get(v___x_1135_, 6);
                v_infoState_1142_ = lean_ctor_get(v___x_1135_, 7);
                v_snapshotTasks_1143_ = lean_ctor_get(v___x_1135_, 8);
                v_isSharedCheck_1170_ = (!lean_is_exclusive(v___x_1135_)) as u8;
                if v_isSharedCheck_1170_ == 0 {
                    v_unused_1171_ = lean_ctor_get(v___x_1135_, 5);
                    lean_dec(v_unused_1171_);
                    v___x_1145_ = v___x_1135_;
                    v_isShared_1146_ = v_isSharedCheck_1170_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1143_);
                    lean_inc(v_infoState_1142_);
                    lean_inc(v_messages_1141_);
                    lean_inc(v_traceState_1140_);
                    lean_inc(v_auxDeclNGen_1139_);
                    lean_inc(v_ngen_1138_);
                    lean_inc(v_nextMacroScope_1137_);
                    lean_inc(v_env_1136_);
                    lean_dec(v___x_1135_);
                    v___x_1145_ = lean_box(0);
                    v_isShared_1146_ = v_isSharedCheck_1170_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_1134_);
                v___x_1147_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_1136_,
                    v_ext_1127_,
                    v_b_1128_,
                    v_kind_1129_,
                    v_currNamespace_1134_,
                );
                v___x_1148_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
                if v_isShared_1146_ == 0 {
                    lean_ctor_set(v___x_1145_, 5, v___x_1148_);
                    lean_ctor_set(v___x_1145_, 0, v___x_1147_);
                    v___x_1150_ = v___x_1145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1147_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_nextMacroScope_1137_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_ngen_1138_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_auxDeclNGen_1139_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_traceState_1140_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 5, v___x_1148_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 6, v_messages_1141_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 7, v_infoState_1142_);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 8, v_snapshotTasks_1143_);
                    v___x_1150_ = v_reuseFailAlloc_1169_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1151_ = lean_st_ref_set(v___y_1132_, v___x_1150_);
                v___x_1152_ = lean_st_ref_take(v___y_1130_);
                v_mctx_1153_ = lean_ctor_get(v___x_1152_, 0);
                v_zetaDeltaFVarIds_1154_ = lean_ctor_get(v___x_1152_, 2);
                v_postponed_1155_ = lean_ctor_get(v___x_1152_, 3);
                v_diag_1156_ = lean_ctor_get(v___x_1152_, 4);
                v_isSharedCheck_1167_ = (!lean_is_exclusive(v___x_1152_)) as u8;
                if v_isSharedCheck_1167_ == 0 {
                    v_unused_1168_ = lean_ctor_get(v___x_1152_, 1);
                    lean_dec(v_unused_1168_);
                    v___x_1158_ = v___x_1152_;
                    v_isShared_1159_ = v_isSharedCheck_1167_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1156_);
                    lean_inc(v_postponed_1155_);
                    lean_inc(v_zetaDeltaFVarIds_1154_);
                    lean_inc(v_mctx_1153_);
                    lean_dec(v___x_1152_);
                    v___x_1158_ = lean_box(0);
                    v_isShared_1159_ = v_isSharedCheck_1167_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1160_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3);
                if v_isShared_1159_ == 0 {
                    lean_ctor_set(v___x_1158_, 1, v___x_1160_);
                    v___x_1162_ = v___x_1158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_mctx_1153_);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1160_);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_zetaDeltaFVarIds_1154_);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_postponed_1155_);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_diag_1156_);
                    v___x_1162_ = v_reuseFailAlloc_1166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1163_ = lean_st_ref_set(v___y_1130_, v___x_1162_);
                v___x_1164_ = lean_box(0);
                v___x_1165_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1165_, 0, v___x_1164_);
                return v___x_1165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___boxed(
    mut v_ext_1172_: *mut LeanObject,
    mut v_b_1173_: *mut LeanObject,
    mut v_kind_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_1179_: u8 = 0;
    let mut v_res_1180_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_1179_ = (lean_unbox(v_kind_1174_) as u8);
    v_res_1180_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_1172_, v_b_1173_, v_kind_boxed_1179_, v___y_1175_, v___y_1176_, v___y_1177_);
    lean_dec(v___y_1177_);
    lean_dec_ref(v___y_1176_);
    lean_dec(v___y_1175_);
    return v_res_1180_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(
    mut v_00_u03b1_1181_: *mut LeanObject,
    mut v_00_u03b2_1182_: *mut LeanObject,
    mut v_00_u03c3_1183_: *mut LeanObject,
    mut v_ext_1184_: *mut LeanObject,
    mut v_b_1185_: *mut LeanObject,
    mut v_kind_1186_: u8,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_1184_, v_b_1185_, v_kind_1186_, v___y_1188_, v___y_1189_, v___y_1190_);
    return v___x_1192_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___boxed(
    mut v_00_u03b1_1193_: *mut LeanObject,
    mut v_00_u03b2_1194_: *mut LeanObject,
    mut v_00_u03c3_1195_: *mut LeanObject,
    mut v_ext_1196_: *mut LeanObject,
    mut v_b_1197_: *mut LeanObject,
    mut v_kind_1198_: *mut LeanObject,
    mut v___y_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
    mut v___y_1201_: *mut LeanObject,
    mut v___y_1202_: *mut LeanObject,
    mut v___y_1203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_1204_: u8 = 0;
    let mut v_res_1205_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_1204_ = (lean_unbox(v_kind_1198_) as u8);
    v_res_1205_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(
            v_00_u03b1_1193_,
            v_00_u03b2_1194_,
            v_00_u03c3_1195_,
            v_ext_1196_,
            v_b_1197_,
            v_kind_boxed_1204_,
            v___y_1199_,
            v___y_1200_,
            v___y_1201_,
            v___y_1202_,
        );
    lean_dec(v___y_1202_);
    lean_dec_ref(v___y_1201_);
    lean_dec(v___y_1200_);
    lean_dec_ref(v___y_1199_);
    return v_res_1205_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_addSymSimpTheorem(
    mut v_ext_1206_: *mut LeanObject,
    mut v_declName_1207_: *mut LeanObject,
    mut v_attrKind_1208_: u8,
    mut v_a_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
    mut v_a_1211_: *mut LeanObject,
    mut v_a_1212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1214_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                    v_declName_1207_,
                    v_a_1209_,
                    v_a_1210_,
                    v_a_1211_,
                    v_a_1212_,
                );
                if lean_obj_tag(v___x_1214_) == 0 {
                    v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
                    lean_inc(v_a_1215_);
                    lean_dec_ref_known(v___x_1214_, 1);
                    v___x_1216_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_1206_, v_a_1215_, v_attrKind_1208_, v_a_1210_, v_a_1211_, v_a_1212_);
                    return v___x_1216_;
                } else {
                    lean_dec_ref(v_ext_1206_);
                    v_a_1217_ = lean_ctor_get(v___x_1214_, 0);
                    v_isSharedCheck_1224_ = (!lean_is_exclusive(v___x_1214_)) as u8;
                    if v_isSharedCheck_1224_ == 0 {
                        v___x_1219_ = v___x_1214_;
                        v_isShared_1220_ = v_isSharedCheck_1224_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1217_);
                        lean_dec(v___x_1214_);
                        v___x_1219_ = lean_box(0);
                        v_isShared_1220_ = v_isSharedCheck_1224_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1220_ == 0 {
                    v___x_1222_ = v___x_1219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
                    v___x_1222_ = v_reuseFailAlloc_1223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_addSymSimpTheorem___boxed(
    mut v_ext_1225_: *mut LeanObject,
    mut v_declName_1226_: *mut LeanObject,
    mut v_attrKind_1227_: *mut LeanObject,
    mut v_a_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
    mut v_a_1230_: *mut LeanObject,
    mut v_a_1231_: *mut LeanObject,
    mut v_a_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_1233_: u8 = 0;
    let mut v_res_1234_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_1233_ = (lean_unbox(v_attrKind_1227_) as u8);
    v_res_1234_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(
        v_ext_1225_,
        v_declName_1226_,
        v_attrKind_boxed_1233_,
        v_a_1228_,
        v_a_1229_,
        v_a_1230_,
        v_a_1231_,
    );
    lean_dec(v_a_1231_);
    lean_dec_ref(v_a_1230_);
    lean_dec(v_a_1229_);
    lean_dec_ref(v_a_1228_);
    return v_res_1234_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10;
    v___x_1262_ = l_Lean_mkAtom(v___x_1261_);
    return v___x_1262_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    v___x_1263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12,
    );
    v___x_1264_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5;
    v___x_1265_ = lean_array_push(v___x_1264_, v___x_1263_);
    return v___x_1265_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    v___x_1274_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17;
    v___x_1275_ = l_Lean_mkAtom(v___x_1274_);
    return v___x_1275_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1276_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18,
    );
    v___x_1277_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5;
    v___x_1278_ = lean_array_push(v___x_1277_, v___x_1276_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1279_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19,
    );
    v___x_1280_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16;
    v___x_1281_ = lean_box(2);
    v___x_1282_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1282_, 0, v___x_1281_);
    lean_ctor_set(v___x_1282_, 1, v___x_1280_);
    lean_ctor_set(v___x_1282_, 2, v___x_1279_);
    return v___x_1282_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    v___x_1283_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20,
    );
    v___x_1284_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13,
    );
    v___x_1285_ = lean_array_push(v___x_1284_, v___x_1283_);
    return v___x_1285_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1286_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21,
    );
    v___x_1287_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11;
    v___x_1288_ = lean_box(2);
    v___x_1289_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1289_, 0, v___x_1288_);
    lean_ctor_set(v___x_1289_, 1, v___x_1287_);
    lean_ctor_set(v___x_1289_, 2, v___x_1286_);
    return v___x_1289_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    v___x_1290_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22,
    );
    v___x_1291_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5;
    v___x_1292_ = lean_array_push(v___x_1291_, v___x_1290_);
    return v___x_1292_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    v___x_1293_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23,
    );
    v___x_1294_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9;
    v___x_1295_ = lean_box(2);
    v___x_1296_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1296_, 0, v___x_1295_);
    lean_ctor_set(v___x_1296_, 1, v___x_1294_);
    lean_ctor_set(v___x_1296_, 2, v___x_1293_);
    return v___x_1296_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v___x_1297_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24,
    );
    v___x_1298_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5;
    v___x_1299_ = lean_array_push(v___x_1298_, v___x_1297_);
    return v___x_1299_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1300_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25,
    );
    v___x_1301_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7;
    v___x_1302_ = lean_box(2);
    v___x_1303_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1303_, 0, v___x_1302_);
    lean_ctor_set(v___x_1303_, 1, v___x_1301_);
    lean_ctor_set(v___x_1303_, 2, v___x_1300_);
    return v___x_1303_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    v___x_1304_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26,
    );
    v___x_1305_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5;
    v___x_1306_ = lean_array_push(v___x_1305_, v___x_1304_);
    return v___x_1306_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27,
    );
    v___x_1308_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4;
    v___x_1309_ = lean_box(2);
    v___x_1310_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1310_, 0, v___x_1309_);
    lean_ctor_set(v___x_1310_, 1, v___x_1308_);
    lean_ctor_set(v___x_1310_, 2, v___x_1307_);
    return v___x_1310_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1() -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    v___x_1311_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28,
    );
    return v___x_1311_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1312_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    v___x_1313_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0);
    v___x_1314_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1314_, 0, v___x_1313_);
    return v___x_1314_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    v___x_1315_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1);
    v___x_1316_ = lean_unsigned_to_nat(0);
    v___x_1317_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1317_, 0, v___x_1316_);
    lean_ctor_set(v___x_1317_, 1, v___x_1316_);
    lean_ctor_set(v___x_1317_, 2, v___x_1316_);
    lean_ctor_set(v___x_1317_, 3, v___x_1316_);
    lean_ctor_set(v___x_1317_, 4, v___x_1315_);
    lean_ctor_set(v___x_1317_, 5, v___x_1315_);
    lean_ctor_set(v___x_1317_, 6, v___x_1315_);
    lean_ctor_set(v___x_1317_, 7, v___x_1315_);
    lean_ctor_set(v___x_1317_, 8, v___x_1315_);
    lean_ctor_set(v___x_1317_, 9, v___x_1315_);
    return v___x_1317_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    v___x_1318_ = lean_unsigned_to_nat(32);
    v___x_1319_ = lean_mk_empty_array_with_capacity(v___x_1318_);
    v___x_1320_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1320_, 0, v___x_1319_);
    return v___x_1320_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4()
-> *mut LeanObject {
    let mut v___x_1321_: usize = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1321_ = 5usize;
    v___x_1322_ = lean_unsigned_to_nat(0);
    v___x_1323_ = lean_unsigned_to_nat(32);
    v___x_1324_ = lean_mk_empty_array_with_capacity(v___x_1323_);
    v___x_1325_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3);
    v___x_1326_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1326_, 0, v___x_1325_);
    lean_ctor_set(v___x_1326_, 1, v___x_1324_);
    lean_ctor_set(v___x_1326_, 2, v___x_1322_);
    lean_ctor_set(v___x_1326_, 3, v___x_1322_);
    lean_ctor_set_usize(v___x_1326_, 4, v___x_1321_);
    return v___x_1326_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5()
-> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = lean_box(1);
    v___x_1328_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4);
    v___x_1329_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1);
    v___x_1330_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1330_, 0, v___x_1329_);
    lean_ctor_set(v___x_1330_, 1, v___x_1328_);
    lean_ctor_set(v___x_1330_, 2, v___x_1327_);
    return v___x_1330_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5(
    mut v_msgData_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = lean_st_ref_get(v___y_1333_);
    v_env_1336_ = lean_ctor_get(v___x_1335_, 0);
    lean_inc_ref(v_env_1336_);
    lean_dec(v___x_1335_);
    v_options_1337_ = lean_ctor_get(v___y_1332_, 2);
    v___x_1338_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2);
    v___x_1339_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5);
    lean_inc_ref(v_options_1337_);
    v___x_1340_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1340_, 0, v_env_1336_);
    lean_ctor_set(v___x_1340_, 1, v___x_1338_);
    lean_ctor_set(v___x_1340_, 2, v___x_1339_);
    lean_ctor_set(v___x_1340_, 3, v_options_1337_);
    v___x_1341_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1341_, 0, v___x_1340_);
    lean_ctor_set(v___x_1341_, 1, v_msgData_1331_);
    v___x_1342_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1342_, 0, v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___boxed(
    mut v_msgData_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
    mut v___y_1346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1347_: *mut LeanObject = core::ptr::null_mut();
    v_res_1347_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5(v_msgData_1343_, v___y_1344_, v___y_1345_);
    lean_dec(v___y_1345_);
    lean_dec_ref(v___y_1344_);
    return v_res_1347_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(
    mut v_msg_1348_: *mut LeanObject,
    mut v___y_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1352_ = lean_ctor_get(v___y_1349_, 5);
                v___x_1353_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5(v_msg_1348_, v___y_1349_, v___y_1350_);
                v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
                v_isSharedCheck_1362_ = (!lean_is_exclusive(v___x_1353_)) as u8;
                if v_isSharedCheck_1362_ == 0 {
                    v___x_1356_ = v___x_1353_;
                    v_isShared_1357_ = v_isSharedCheck_1362_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1354_);
                    lean_dec(v___x_1353_);
                    v___x_1356_ = lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1362_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1352_);
                v___x_1358_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1358_, 0, v_ref_1352_);
                lean_ctor_set(v___x_1358_, 1, v_a_1354_);
                if v_isShared_1357_ == 0 {
                    lean_ctor_set_tag(v___x_1356_, 1);
                    lean_ctor_set(v___x_1356_, 0, v___x_1358_);
                    v___x_1360_ = v___x_1356_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
                    v___x_1360_ = v_reuseFailAlloc_1361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg___boxed(
    mut v_msg_1363_: *mut LeanObject,
    mut v___y_1364_: *mut LeanObject,
    mut v___y_1365_: *mut LeanObject,
    mut v___y_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1367_: *mut LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(
        v_msg_1363_,
        v___y_1364_,
        v___y_1365_,
    );
    lean_dec(v___y_1365_);
    lean_dec_ref(v___y_1364_);
    return v_res_1367_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    v___x_1369_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0;
    v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
    return v___x_1370_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(
    mut v___declName_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1375_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1,
    );
    v___x_1376_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(
        v___x_1375_,
        v___y_1372_,
        v___y_1373_,
    );
    return v___x_1376_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed(
    mut v___declName_1377_: *mut LeanObject,
    mut v___y_1378_: *mut LeanObject,
    mut v___y_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1381_: *mut LeanObject = core::ptr::null_mut();
    v_res_1381_ =
        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(v___declName_1377_, v___y_1378_, v___y_1379_);
    lean_dec(v___y_1379_);
    lean_dec_ref(v___y_1378_);
    lean_dec(v___declName_1377_);
    return v_res_1381_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1(
    mut v_ext_1382_: *mut LeanObject,
    mut v_attrKind_1383_: u8,
    mut v_as_1384_: *mut LeanObject,
    mut v_sz_1385_: usize,
    mut v_i_1386_: usize,
    mut v_b_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1393_: u8 = 0;
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: usize = 0;
    let mut v___x_1399_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1393_ = lean_usize_dec_lt(v_i_1386_, v_sz_1385_);
                if v___x_1393_ == 0 {
                    lean_dec_ref(v_ext_1382_);
                    v___x_1394_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1394_, 0, v_b_1387_);
                    return v___x_1394_;
                } else {
                    v_a_1395_ = lean_array_uget_borrowed(v_as_1384_, v_i_1386_);
                    lean_inc(v_a_1395_);
                    lean_inc_ref(v_ext_1382_);
                    v___x_1396_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(
                        v_ext_1382_,
                        v_a_1395_,
                        v_attrKind_1383_,
                        v___y_1388_,
                        v___y_1389_,
                        v___y_1390_,
                        v___y_1391_,
                    );
                    if lean_obj_tag(v___x_1396_) == 0 {
                        lean_dec_ref_known(v___x_1396_, 1);
                        v___x_1397_ = lean_box(0);
                        v___x_1398_ = 1usize;
                        v___x_1399_ = lean_usize_add(v_i_1386_, v___x_1398_);
                        v_i_1386_ = v___x_1399_;
                        v_b_1387_ = v___x_1397_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_ext_1382_);
                        return v___x_1396_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1___boxed(
    mut v_ext_1401_: *mut LeanObject,
    mut v_attrKind_1402_: *mut LeanObject,
    mut v_as_1403_: *mut LeanObject,
    mut v_sz_1404_: *mut LeanObject,
    mut v_i_1405_: *mut LeanObject,
    mut v_b_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_1412_: u8 = 0;
    let mut v_sz_boxed_1413_: usize = 0;
    let mut v_i_boxed_1414_: usize = 0;
    let mut v_res_1415_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_1412_ = (lean_unbox(v_attrKind_1402_) as u8);
    v_sz_boxed_1413_ = lean_unbox_usize(v_sz_1404_);
    lean_dec(v_sz_1404_);
    v_i_boxed_1414_ = lean_unbox_usize(v_i_1405_);
    lean_dec(v_i_1405_);
    v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1(v_ext_1401_, v_attrKind_boxed_1412_, v_as_1403_, v_sz_boxed_1413_, v_i_boxed_1414_, v_b_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
    lean_dec(v___y_1410_);
    lean_dec_ref(v___y_1409_);
    lean_dec(v___y_1408_);
    lean_dec_ref(v___y_1407_);
    lean_dec_ref(v_as_1403_);
    return v_res_1415_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3(
    mut v_msgData_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1422_ = lean_st_ref_get(v___y_1420_);
    v_env_1423_ = lean_ctor_get(v___x_1422_, 0);
    lean_inc_ref(v_env_1423_);
    lean_dec(v___x_1422_);
    v___x_1424_ = lean_st_ref_get(v___y_1418_);
    v_mctx_1425_ = lean_ctor_get(v___x_1424_, 0);
    lean_inc_ref(v_mctx_1425_);
    lean_dec(v___x_1424_);
    v_lctx_1426_ = lean_ctor_get(v___y_1417_, 2);
    v_options_1427_ = lean_ctor_get(v___y_1419_, 2);
    lean_inc_ref(v_options_1427_);
    lean_inc_ref(v_lctx_1426_);
    v___x_1428_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1428_, 0, v_env_1423_);
    lean_ctor_set(v___x_1428_, 1, v_mctx_1425_);
    lean_ctor_set(v___x_1428_, 2, v_lctx_1426_);
    lean_ctor_set(v___x_1428_, 3, v_options_1427_);
    v___x_1429_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1429_, 0, v___x_1428_);
    lean_ctor_set(v___x_1429_, 1, v_msgData_1416_);
    v___x_1430_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3___boxed(
    mut v_msgData_1431_: *mut LeanObject,
    mut v___y_1432_: *mut LeanObject,
    mut v___y_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
    mut v___y_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1437_: *mut LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3(v_msgData_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
    lean_dec(v___y_1435_);
    lean_dec_ref(v___y_1434_);
    lean_dec(v___y_1433_);
    lean_dec_ref(v___y_1432_);
    return v_res_1437_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(
    mut v_msg_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
    mut v___y_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1444_ = lean_ctor_get(v___y_1441_, 5);
                v___x_1445_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3(v_msg_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
                v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
                v_isSharedCheck_1454_ = (!lean_is_exclusive(v___x_1445_)) as u8;
                if v_isSharedCheck_1454_ == 0 {
                    v___x_1448_ = v___x_1445_;
                    v_isShared_1449_ = v_isSharedCheck_1454_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1446_);
                    lean_dec(v___x_1445_);
                    v___x_1448_ = lean_box(0);
                    v_isShared_1449_ = v_isSharedCheck_1454_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1444_);
                v___x_1450_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1450_, 0, v_ref_1444_);
                lean_ctor_set(v___x_1450_, 1, v_a_1446_);
                if v_isShared_1449_ == 0 {
                    lean_ctor_set_tag(v___x_1448_, 1);
                    lean_ctor_set(v___x_1448_, 0, v___x_1450_);
                    v___x_1452_ = v___x_1448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
                    v___x_1452_ = v_reuseFailAlloc_1453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg___boxed(
    mut v_msg_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(
        v_msg_1455_,
        v___y_1456_,
        v___y_1457_,
        v___y_1458_,
        v___y_1459_,
    );
    lean_dec(v___y_1459_);
    lean_dec_ref(v___y_1458_);
    lean_dec(v___y_1457_);
    lean_dec_ref(v___y_1456_);
    return v_res_1461_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(
    mut v_ref_1462_: *mut LeanObject,
    mut v_msg_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1481_: u8 = 0;
    let mut v_cancelTk_x3f_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1483_: u8 = 0;
    let mut v_inheritedTraceOptions_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1469_ = lean_ctor_get(v___y_1466_, 0);
    v_fileMap_1470_ = lean_ctor_get(v___y_1466_, 1);
    v_options_1471_ = lean_ctor_get(v___y_1466_, 2);
    v_currRecDepth_1472_ = lean_ctor_get(v___y_1466_, 3);
    v_maxRecDepth_1473_ = lean_ctor_get(v___y_1466_, 4);
    v_ref_1474_ = lean_ctor_get(v___y_1466_, 5);
    v_currNamespace_1475_ = lean_ctor_get(v___y_1466_, 6);
    v_openDecls_1476_ = lean_ctor_get(v___y_1466_, 7);
    v_initHeartbeats_1477_ = lean_ctor_get(v___y_1466_, 8);
    v_maxHeartbeats_1478_ = lean_ctor_get(v___y_1466_, 9);
    v_quotContext_1479_ = lean_ctor_get(v___y_1466_, 10);
    v_currMacroScope_1480_ = lean_ctor_get(v___y_1466_, 11);
    v_diag_1481_ = lean_ctor_get_uint8(
        v___y_1466_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1482_ = lean_ctor_get(v___y_1466_, 12);
    v_suppressElabErrors_1483_ = lean_ctor_get_uint8(
        v___y_1466_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1484_ = lean_ctor_get(v___y_1466_, 13);
    v_ref_1485_ = l_Lean_replaceRef(v_ref_1462_, v_ref_1474_);
    lean_inc_ref(v_inheritedTraceOptions_1484_);
    lean_inc(v_cancelTk_x3f_1482_);
    lean_inc(v_currMacroScope_1480_);
    lean_inc(v_quotContext_1479_);
    lean_inc(v_maxHeartbeats_1478_);
    lean_inc(v_initHeartbeats_1477_);
    lean_inc(v_openDecls_1476_);
    lean_inc(v_currNamespace_1475_);
    lean_inc(v_maxRecDepth_1473_);
    lean_inc(v_currRecDepth_1472_);
    lean_inc_ref(v_options_1471_);
    lean_inc_ref(v_fileMap_1470_);
    lean_inc_ref(v_fileName_1469_);
    v___x_1486_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1486_, 0, v_fileName_1469_);
    lean_ctor_set(v___x_1486_, 1, v_fileMap_1470_);
    lean_ctor_set(v___x_1486_, 2, v_options_1471_);
    lean_ctor_set(v___x_1486_, 3, v_currRecDepth_1472_);
    lean_ctor_set(v___x_1486_, 4, v_maxRecDepth_1473_);
    lean_ctor_set(v___x_1486_, 5, v_ref_1485_);
    lean_ctor_set(v___x_1486_, 6, v_currNamespace_1475_);
    lean_ctor_set(v___x_1486_, 7, v_openDecls_1476_);
    lean_ctor_set(v___x_1486_, 8, v_initHeartbeats_1477_);
    lean_ctor_set(v___x_1486_, 9, v_maxHeartbeats_1478_);
    lean_ctor_set(v___x_1486_, 10, v_quotContext_1479_);
    lean_ctor_set(v___x_1486_, 11, v_currMacroScope_1480_);
    lean_ctor_set(v___x_1486_, 12, v_cancelTk_x3f_1482_);
    lean_ctor_set(v___x_1486_, 13, v_inheritedTraceOptions_1484_);
    lean_ctor_set_uint8(
        v___x_1486_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1481_,
    );
    lean_ctor_set_uint8(
        v___x_1486_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1483_,
    );
    v___x_1487_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(
        v_msg_1463_,
        v___y_1464_,
        v___y_1465_,
        v___x_1486_,
        v___y_1467_,
    );
    lean_dec_ref_known(v___x_1486_, 14);
    return v___x_1487_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(
    mut v_ref_1488_: *mut LeanObject,
    mut v_msg_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
    mut v___y_1491_: *mut LeanObject,
    mut v___y_1492_: *mut LeanObject,
    mut v___y_1493_: *mut LeanObject,
    mut v___y_1494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1495_: *mut LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_1488_, v_msg_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
    lean_dec(v___y_1493_);
    lean_dec_ref(v___y_1492_);
    lean_dec(v___y_1491_);
    lean_dec_ref(v___y_1490_);
    lean_dec(v_ref_1488_);
    return v_res_1495_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0;
    v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
    return v___x_1498_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    v___x_1500_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2;
    v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4;
    v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
    return v___x_1504_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    v___x_1506_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    v___x_1509_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1512_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v___x_1515_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
    return v___x_1516_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(
    mut v_msg_1517_: *mut LeanObject,
    mut v_declHint_1518_: *mut LeanObject,
    mut v___y_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: u8 = 0;
    let mut v_isExporting_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1521_ = lean_st_ref_get(v___y_1519_);
                v_env_1522_ = lean_ctor_get(v___x_1521_, 0);
                lean_inc_ref(v_env_1522_);
                lean_dec(v___x_1521_);
                v___x_1523_ = l_Lean_Name_isAnonymous(v_declHint_1518_);
                if v___x_1523_ == 0 {
                    v_isExporting_1524_ = lean_ctor_get_uint8(
                        v_env_1522_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1524_ == 0 {
                        lean_dec_ref(v_env_1522_);
                        lean_dec(v_declHint_1518_);
                        v___x_1525_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1525_, 0, v_msg_1517_);
                        return v___x_1525_;
                    } else {
                        lean_inc_ref(v_env_1522_);
                        v___x_1526_ = l_Lean_Environment_setExporting(v_env_1522_, v___x_1523_);
                        lean_inc(v_declHint_1518_);
                        lean_inc_ref(v___x_1526_);
                        v___x_1527_ = l_Lean_Environment_contains(
                            v___x_1526_,
                            v_declHint_1518_,
                            v_isExporting_1524_,
                        );
                        if v___x_1527_ == 0 {
                            lean_dec_ref(v___x_1526_);
                            lean_dec_ref(v_env_1522_);
                            lean_dec(v_declHint_1518_);
                            v___x_1528_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1528_, 0, v_msg_1517_);
                            return v___x_1528_;
                        } else {
                            v___x_1529_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2);
                            v___x_1530_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5);
                            v___x_1531_ = l_Lean_Options_empty;
                            v___x_1532_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1532_, 0, v___x_1526_);
                            lean_ctor_set(v___x_1532_, 1, v___x_1529_);
                            lean_ctor_set(v___x_1532_, 2, v___x_1530_);
                            lean_ctor_set(v___x_1532_, 3, v___x_1531_);
                            lean_inc(v_declHint_1518_);
                            v___x_1533_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1518_, v___x_1523_);
                            v_c_1534_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1534_, 0, v___x_1532_);
                            lean_ctor_set(v_c_1534_, 1, v___x_1533_);
                            v___x_1535_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1522_,
                                v_declHint_1518_,
                            );
                            if lean_obj_tag(v___x_1535_) == 0 {
                                lean_dec_ref(v_env_1522_);
                                lean_dec(v_declHint_1518_);
                                v___x_1536_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
                                v___x_1537_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                                lean_ctor_set(v___x_1537_, 1, v_c_1534_);
                                v___x_1538_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
                                v___x_1539_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1539_, 0, v___x_1537_);
                                lean_ctor_set(v___x_1539_, 1, v___x_1538_);
                                v___x_1540_ = l_Lean_MessageData_note(v___x_1539_);
                                v___x_1541_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1541_, 0, v_msg_1517_);
                                lean_ctor_set(v___x_1541_, 1, v___x_1540_);
                                v___x_1542_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1542_, 0, v___x_1541_);
                                return v___x_1542_;
                            } else {
                                v_val_1543_ = lean_ctor_get(v___x_1535_, 0);
                                v_isSharedCheck_1578_ = (!lean_is_exclusive(v___x_1535_)) as u8;
                                if v_isSharedCheck_1578_ == 0 {
                                    v___x_1545_ = v___x_1535_;
                                    v_isShared_1546_ = v_isSharedCheck_1578_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1543_);
                                    lean_dec(v___x_1535_);
                                    v___x_1545_ = lean_box(0);
                                    v_isShared_1546_ = v_isSharedCheck_1578_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1522_);
                    lean_dec(v_declHint_1518_);
                    v___x_1579_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1579_, 0, v_msg_1517_);
                    return v___x_1579_;
                }
            }
            1 => {
                v___x_1547_ = lean_box(0);
                v___x_1548_ = l_Lean_Environment_header(v_env_1522_);
                lean_dec_ref(v_env_1522_);
                v___x_1549_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1548_);
                v_mod_1550_ = lean_array_get(v___x_1547_, v___x_1549_, v_val_1543_);
                lean_dec(v_val_1543_);
                lean_dec_ref(v___x_1549_);
                v___x_1551_ = l_Lean_isPrivateName(v_declHint_1518_);
                lean_dec(v_declHint_1518_);
                if v___x_1551_ == 0 {
                    v___x_1552_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
                    v___x_1553_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1553_, 0, v___x_1552_);
                    lean_ctor_set(v___x_1553_, 1, v_c_1534_);
                    v___x_1554_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_1555_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1555_, 0, v___x_1553_);
                    lean_ctor_set(v___x_1555_, 1, v___x_1554_);
                    v___x_1556_ = l_Lean_MessageData_ofName(v_mod_1550_);
                    v___x_1557_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1557_, 0, v___x_1555_);
                    lean_ctor_set(v___x_1557_, 1, v___x_1556_);
                    v___x_1558_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
                    v___x_1559_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1559_, 0, v___x_1557_);
                    lean_ctor_set(v___x_1559_, 1, v___x_1558_);
                    v___x_1560_ = l_Lean_MessageData_note(v___x_1559_);
                    v___x_1561_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1561_, 0, v_msg_1517_);
                    lean_ctor_set(v___x_1561_, 1, v___x_1560_);
                    if v_isShared_1546_ == 0 {
                        lean_ctor_set_tag(v___x_1545_, 0);
                        lean_ctor_set(v___x_1545_, 0, v___x_1561_);
                        v___x_1563_ = v___x_1545_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
                        v___x_1563_ = v_reuseFailAlloc_1564_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1565_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
                    v___x_1566_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1566_, 0, v___x_1565_);
                    lean_ctor_set(v___x_1566_, 1, v_c_1534_);
                    v___x_1567_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_1568_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1568_, 0, v___x_1566_);
                    lean_ctor_set(v___x_1568_, 1, v___x_1567_);
                    v___x_1569_ = l_Lean_MessageData_ofName(v_mod_1550_);
                    v___x_1570_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1570_, 0, v___x_1568_);
                    lean_ctor_set(v___x_1570_, 1, v___x_1569_);
                    v___x_1571_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_1572_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1572_, 0, v___x_1570_);
                    lean_ctor_set(v___x_1572_, 1, v___x_1571_);
                    v___x_1573_ = l_Lean_MessageData_note(v___x_1572_);
                    v___x_1574_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1574_, 0, v_msg_1517_);
                    lean_ctor_set(v___x_1574_, 1, v___x_1573_);
                    if v_isShared_1546_ == 0 {
                        lean_ctor_set_tag(v___x_1545_, 0);
                        lean_ctor_set(v___x_1545_, 0, v___x_1574_);
                        v___x_1576_ = v___x_1545_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
                        v___x_1576_ = v_reuseFailAlloc_1577_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1563_;
            }
            3 => {
                return v___x_1576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_1580_: *mut LeanObject,
    mut v_declHint_1581_: *mut LeanObject,
    mut v___y_1582_: *mut LeanObject,
    mut v___y_1583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1584_: *mut LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_1580_, v_declHint_1581_, v___y_1582_);
    lean_dec(v___y_1582_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8(
    mut v_msg_1585_: *mut LeanObject,
    mut v_declHint_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
    mut v___y_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1592_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_1585_, v_declHint_1586_, v___y_1590_);
                v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
                v_isSharedCheck_1602_ = (!lean_is_exclusive(v___x_1592_)) as u8;
                if v_isSharedCheck_1602_ == 0 {
                    v___x_1595_ = v___x_1592_;
                    v_isShared_1596_ = v_isSharedCheck_1602_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1593_);
                    lean_dec(v___x_1592_);
                    v___x_1595_ = lean_box(0);
                    v_isShared_1596_ = v_isSharedCheck_1602_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1597_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1598_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1598_, 0, v___x_1597_);
                lean_ctor_set(v___x_1598_, 1, v_a_1593_);
                if v_isShared_1596_ == 0 {
                    lean_ctor_set(v___x_1595_, 0, v___x_1598_);
                    v___x_1600_ = v___x_1595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
                    v___x_1600_ = v_reuseFailAlloc_1601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(
    mut v_msg_1603_: *mut LeanObject,
    mut v_declHint_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
    mut v___y_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1610_: *mut LeanObject = core::ptr::null_mut();
    v_res_1610_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_1603_, v_declHint_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
    lean_dec(v___y_1608_);
    lean_dec_ref(v___y_1607_);
    lean_dec(v___y_1606_);
    lean_dec_ref(v___y_1605_);
    return v_res_1610_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(
    mut v_ref_1611_: *mut LeanObject,
    mut v_msg_1612_: *mut LeanObject,
    mut v_declHint_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1619_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_1612_, v_declHint_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
    v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
    lean_inc(v_a_1620_);
    lean_dec_ref(v___x_1619_);
    v___x_1621_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_1611_, v_a_1620_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
    return v___x_1621_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg___boxed(
    mut v_ref_1622_: *mut LeanObject,
    mut v_msg_1623_: *mut LeanObject,
    mut v_declHint_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1630_: *mut LeanObject = core::ptr::null_mut();
    v_res_1630_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_1622_, v_msg_1623_, v_declHint_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
    lean_dec(v___y_1628_);
    lean_dec_ref(v___y_1627_);
    lean_dec(v___y_1626_);
    lean_dec_ref(v___y_1625_);
    lean_dec(v_ref_1622_);
    return v_res_1630_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
    return v___x_1633_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1637_: *mut LeanObject,
    mut v_constName_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    v___x_1644_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1645_ = 0;
    lean_inc(v_constName_1638_);
    v___x_1646_ = l_Lean_MessageData_ofConstName(v_constName_1638_, v___x_1645_);
    v___x_1647_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1647_, 0, v___x_1644_);
    lean_ctor_set(v___x_1647_, 1, v___x_1646_);
    v___x_1648_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1649_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1649_, 0, v___x_1647_);
    lean_ctor_set(v___x_1649_, 1, v___x_1648_);
    v___x_1650_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_1637_, v___x_1649_, v_constName_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
    return v___x_1650_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1651_: *mut LeanObject,
    mut v_constName_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1658_: *mut LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_1651_, v_constName_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
    lean_dec(v___y_1656_);
    lean_dec_ref(v___y_1655_);
    lean_dec(v___y_1654_);
    lean_dec_ref(v___y_1653_);
    lean_dec(v_ref_1651_);
    return v_res_1658_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(
    mut v_constName_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1665_ = lean_ctor_get(v___y_1662_, 5);
    v___x_1666_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_1665_, v_constName_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
    return v___x_1666_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg___boxed(
    mut v_constName_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1673_: *mut LeanObject = core::ptr::null_mut();
    v_res_1673_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(v_constName_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
    lean_dec(v___y_1671_);
    lean_dec_ref(v___y_1670_);
    lean_dec(v___y_1669_);
    lean_dec_ref(v___y_1668_);
    return v_res_1673_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(
    mut v_constName_1674_: *mut LeanObject,
    mut v_skipRealize_1675_: u8,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1681_ = lean_st_ref_get(v___y_1679_);
                v_env_1682_ = lean_ctor_get(v___x_1681_, 0);
                lean_inc_ref(v_env_1682_);
                lean_dec(v___x_1681_);
                lean_inc(v_constName_1674_);
                v___x_1683_ = l_Lean_Environment_findAsync_x3f(
                    v_env_1682_,
                    v_constName_1674_,
                    v_skipRealize_1675_,
                );
                if lean_obj_tag(v___x_1683_) == 0 {
                    v___x_1684_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(v_constName_1674_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
                    return v___x_1684_;
                } else {
                    lean_dec(v_constName_1674_);
                    v_val_1685_ = lean_ctor_get(v___x_1683_, 0);
                    v_isSharedCheck_1692_ = (!lean_is_exclusive(v___x_1683_)) as u8;
                    if v_isSharedCheck_1692_ == 0 {
                        v___x_1687_ = v___x_1683_;
                        v_isShared_1688_ = v_isSharedCheck_1692_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1685_);
                        lean_dec(v___x_1683_);
                        v___x_1687_ = lean_box(0);
                        v_isShared_1688_ = v_isSharedCheck_1692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1688_ == 0 {
                    lean_ctor_set_tag(v___x_1687_, 0);
                    v___x_1690_ = v___x_1687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_val_1685_);
                    v___x_1690_ = v_reuseFailAlloc_1691_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___boxed(
    mut v_constName_1693_: *mut LeanObject,
    mut v_skipRealize_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_1700_: u8 = 0;
    let mut v_res_1701_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_1700_ = (lean_unbox(v_skipRealize_1694_) as u8);
    v_res_1701_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(
        v_constName_1693_,
        v_skipRealize_boxed_1700_,
        v___y_1695_,
        v___y_1696_,
        v___y_1697_,
        v___y_1698_,
    );
    lean_dec(v___y_1698_);
    lean_dec_ref(v___y_1697_);
    lean_dec(v___y_1696_);
    lean_dec_ref(v___y_1695_);
    return v_res_1701_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1() -> u64 {
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: u64 = 0;
    v___x_1708_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0;
    v___x_1709_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2() -> *mut LeanObject {
    let mut v___x_1710_: u64 = 0;
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    v___x_1710_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1,
    );
    v___x_1711_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0;
    v___x_1712_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_1712_, 0, v___x_1711_);
    lean_ctor_set_uint64(
        v___x_1712_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1710_,
    );
    return v___x_1712_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1713_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1714_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3,
    );
    v___x_1715_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1715_, 0, v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5() -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_box(1);
    v___x_1717_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4);
    v___x_1718_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4,
    );
    v___x_1719_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1719_, 0, v___x_1718_);
    lean_ctor_set(v___x_1719_, 1, v___x_1717_);
    lean_ctor_set(v___x_1719_, 2, v___x_1716_);
    return v___x_1719_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7() -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4,
    );
    v___x_1723_ = lean_unsigned_to_nat(0);
    v___x_1724_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1724_, 0, v___x_1723_);
    lean_ctor_set(v___x_1724_, 1, v___x_1723_);
    lean_ctor_set(v___x_1724_, 2, v___x_1723_);
    lean_ctor_set(v___x_1724_, 3, v___x_1723_);
    lean_ctor_set(v___x_1724_, 4, v___x_1722_);
    lean_ctor_set(v___x_1724_, 5, v___x_1722_);
    lean_ctor_set(v___x_1724_, 6, v___x_1722_);
    lean_ctor_set(v___x_1724_, 7, v___x_1722_);
    lean_ctor_set(v___x_1724_, 8, v___x_1722_);
    lean_ctor_set(v___x_1724_, 9, v___x_1722_);
    return v___x_1724_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8() -> *mut LeanObject {
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    v___x_1725_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4,
    );
    v___x_1726_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1726_, 0, v___x_1725_);
    lean_ctor_set(v___x_1726_, 1, v___x_1725_);
    lean_ctor_set(v___x_1726_, 2, v___x_1725_);
    lean_ctor_set(v___x_1726_, 3, v___x_1725_);
    lean_ctor_set(v___x_1726_, 4, v___x_1725_);
    lean_ctor_set(v___x_1726_, 5, v___x_1725_);
    return v___x_1726_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9() -> *mut LeanObject {
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1727_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4,
    );
    v___x_1728_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1728_, 0, v___x_1727_);
    lean_ctor_set(v___x_1728_, 1, v___x_1727_);
    lean_ctor_set(v___x_1728_, 2, v___x_1727_);
    lean_ctor_set(v___x_1728_, 3, v___x_1727_);
    lean_ctor_set(v___x_1728_, 4, v___x_1727_);
    return v___x_1728_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11() -> *mut LeanObject {
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10;
    v___x_1731_ = l_Lean_stringToMessageData(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13() -> *mut LeanObject {
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    v___x_1733_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12;
    v___x_1734_ = l_Lean_stringToMessageData(v___x_1733_);
    return v___x_1734_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15() -> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    v___x_1736_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14;
    v___x_1737_ = l_Lean_stringToMessageData(v___x_1736_);
    return v___x_1737_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17() -> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    v___x_1739_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16;
    v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
    return v___x_1740_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19() -> *mut LeanObject {
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v___x_1742_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18;
    v___x_1743_ = l_Lean_stringToMessageData(v___x_1742_);
    return v___x_1743_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(
    mut v___x_1744_: *mut LeanObject,
    mut v_ext_1745_: *mut LeanObject,
    mut v_attrName_1746_: *mut LeanObject,
    mut v_declName_1747_: *mut LeanObject,
    mut v_x_1748_: *mut LeanObject,
    mut v_attrKind_1749_: u8,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1754_: u8 = 0;
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1769_: u8 = 0;
    let mut v_sig_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1777_: u8 = 0;
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1793_: usize = 0;
    let mut v___x_1794_: usize = 0;
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_a_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut v_a_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1855_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1753_ = 0;
                v___x_1754_ = 1;
                v___x_1755_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2,
                );
                v___x_1756_ = lean_unsigned_to_nat(0);
                v___x_1757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4);
                v___x_1758_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5,
                );
                v___x_1759_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6;
                v___x_1760_ = lean_box(0);
                lean_inc(v___x_1744_);
                v___x_1761_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_1761_, 0, v___x_1755_);
                lean_ctor_set(v___x_1761_, 1, v___x_1744_);
                lean_ctor_set(v___x_1761_, 2, v___x_1758_);
                lean_ctor_set(v___x_1761_, 3, v___x_1759_);
                lean_ctor_set(v___x_1761_, 4, v___x_1760_);
                lean_ctor_set(v___x_1761_, 5, v___x_1756_);
                lean_ctor_set(v___x_1761_, 6, v___x_1760_);
                lean_ctor_set_uint8(
                    v___x_1761_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_1753_,
                );
                lean_ctor_set_uint8(
                    v___x_1761_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_1753_,
                );
                lean_ctor_set_uint8(
                    v___x_1761_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_1753_,
                );
                lean_ctor_set_uint8(
                    v___x_1761_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_1754_,
                );
                v___x_1762_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7,
                );
                v___x_1763_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8,
                );
                v___x_1764_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9,
                );
                v___x_1765_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1765_, 0, v___x_1762_);
                lean_ctor_set(v___x_1765_, 1, v___x_1763_);
                lean_ctor_set(v___x_1765_, 2, v___x_1744_);
                lean_ctor_set(v___x_1765_, 3, v___x_1757_);
                lean_ctor_set(v___x_1765_, 4, v___x_1764_);
                v___x_1766_ = lean_st_mk_ref(v___x_1765_);
                lean_inc(v_declName_1747_);
                v___x_1767_ =
                    l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(
                        v_declName_1747_,
                        v___x_1753_,
                        v___x_1761_,
                        v___x_1766_,
                        v___y_1750_,
                        v___y_1751_,
                    );
                if lean_obj_tag(v___x_1767_) == 0 {
                    v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
                    lean_inc(v_a_1768_);
                    lean_dec_ref_known(v___x_1767_, 1);
                    v_kind_1769_ = lean_ctor_get_uint8(
                        v_a_1768_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_sig_1770_ = lean_ctor_get(v_a_1768_, 1);
                    lean_inc_ref(v_sig_1770_);
                    lean_dec(v_a_1768_);
                    v___x_1771_ = lean_task_get_own(v_sig_1770_);
                    v_type_1772_ = lean_ctor_get(v___x_1771_, 2);
                    lean_inc_ref(v_type_1772_);
                    lean_dec(v___x_1771_);
                    v___x_1773_ = l_Lean_Meta_isProp(
                        v_type_1772_,
                        v___x_1761_,
                        v___x_1766_,
                        v___y_1750_,
                        v___y_1751_,
                    );
                    if lean_obj_tag(v___x_1773_) == 0 {
                        v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
                        v_isSharedCheck_1843_ = (!lean_is_exclusive(v___x_1773_)) as u8;
                        if v_isSharedCheck_1843_ == 0 {
                            v___x_1776_ = v___x_1773_;
                            v_isShared_1777_ = v_isSharedCheck_1843_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1774_);
                            lean_dec(v___x_1773_);
                            v___x_1776_ = lean_box(0);
                            v_isShared_1777_ = v_isSharedCheck_1843_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1766_);
                        lean_dec_ref_known(v___x_1761_, 7);
                        lean_dec(v_declName_1747_);
                        lean_dec(v_attrName_1746_);
                        lean_dec_ref(v_ext_1745_);
                        v_a_1844_ = lean_ctor_get(v___x_1773_, 0);
                        v_isSharedCheck_1851_ = (!lean_is_exclusive(v___x_1773_)) as u8;
                        if v_isSharedCheck_1851_ == 0 {
                            v___x_1846_ = v___x_1773_;
                            v_isShared_1847_ = v_isSharedCheck_1851_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1844_);
                            lean_dec(v___x_1773_);
                            v___x_1846_ = lean_box(0);
                            v_isShared_1847_ = v_isSharedCheck_1851_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1766_);
                    lean_dec_ref_known(v___x_1761_, 7);
                    lean_dec(v_declName_1747_);
                    lean_dec(v_attrName_1746_);
                    lean_dec_ref(v_ext_1745_);
                    v_a_1852_ = lean_ctor_get(v___x_1767_, 0);
                    v_isSharedCheck_1859_ = (!lean_is_exclusive(v___x_1767_)) as u8;
                    if v_isSharedCheck_1859_ == 0 {
                        v___x_1854_ = v___x_1767_;
                        v_isShared_1855_ = v_isSharedCheck_1859_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1852_);
                        lean_dec(v___x_1767_);
                        v___x_1854_ = lean_box(0);
                        v_isShared_1855_ = v_isSharedCheck_1859_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1778_ = lean_box(0);
                v___x_1786_ = (lean_unbox(v_a_1774_) as u8);
                lean_dec(v_a_1774_);
                if v___x_1786_ == 0 {
                    if v_kind_1769_ == 0 {
                        lean_inc(v_declName_1747_);
                        v___x_1787_ = l_Lean_Meta_Simp_ignoreEquations(
                            v_declName_1747_,
                            v___y_1750_,
                            v___y_1751_,
                        );
                        if lean_obj_tag(v___x_1787_) == 0 {
                            v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
                            lean_inc(v_a_1788_);
                            lean_dec_ref_known(v___x_1787_, 1);
                            v___x_1789_ = (lean_unbox(v_a_1788_) as u8);
                            lean_dec(v_a_1788_);
                            if v___x_1789_ == 0 {
                                lean_inc(v_declName_1747_);
                                v___x_1790_ = l_Lean_Meta_getEqnsFor_x3f(
                                    v_declName_1747_,
                                    v___x_1761_,
                                    v___x_1766_,
                                    v___y_1750_,
                                    v___y_1751_,
                                );
                                if lean_obj_tag(v___x_1790_) == 0 {
                                    v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
                                    lean_inc(v_a_1791_);
                                    lean_dec_ref_known(v___x_1790_, 1);
                                    if lean_obj_tag(v_a_1791_) == 1 {
                                        lean_dec(v_declName_1747_);
                                        lean_dec(v_attrName_1746_);
                                        v_val_1792_ = lean_ctor_get(v_a_1791_, 0);
                                        lean_inc(v_val_1792_);
                                        lean_dec_ref_known(v_a_1791_, 1);
                                        v_sz_1793_ = lean_array_size(v_val_1792_);
                                        v___x_1794_ = 0usize;
                                        v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1(v_ext_1745_, v_attrKind_1749_, v_val_1792_, v_sz_1793_, v___x_1794_, v___x_1778_, v___x_1761_, v___x_1766_, v___y_1750_, v___y_1751_);
                                        lean_dec_ref_known(v___x_1761_, 7);
                                        lean_dec(v_val_1792_);
                                        if lean_obj_tag(v___x_1795_) == 0 {
                                            lean_dec_ref_known(v___x_1795_, 1);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___y_1785_ = v___x_1795_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_1791_);
                                        lean_dec_ref(v_ext_1745_);
                                        v___x_1796_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once), _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11);
                                        v___x_1797_ = l_Lean_MessageData_ofName(v_attrName_1746_);
                                        v___x_1798_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_1798_, 0, v___x_1796_);
                                        lean_ctor_set(v___x_1798_, 1, v___x_1797_);
                                        v___x_1799_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once), _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13);
                                        v___x_1800_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_1800_, 0, v___x_1798_);
                                        lean_ctor_set(v___x_1800_, 1, v___x_1799_);
                                        v___x_1801_ = l_Lean_MessageData_ofConstName(
                                            v_declName_1747_,
                                            v___x_1753_,
                                        );
                                        v___x_1802_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_1802_, 0, v___x_1800_);
                                        lean_ctor_set(v___x_1802_, 1, v___x_1801_);
                                        v___x_1803_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15_once), _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15);
                                        v___x_1804_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_1804_, 0, v___x_1802_);
                                        lean_ctor_set(v___x_1804_, 1, v___x_1803_);
                                        v___x_1805_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v___x_1804_, v___x_1761_, v___x_1766_, v___y_1750_, v___y_1751_);
                                        lean_dec_ref_known(v___x_1761_, 7);
                                        v___y_1785_ = v___x_1805_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_1776_);
                                    lean_dec(v___x_1766_);
                                    lean_dec_ref_known(v___x_1761_, 7);
                                    lean_dec(v_declName_1747_);
                                    lean_dec(v_attrName_1746_);
                                    lean_dec_ref(v_ext_1745_);
                                    v_a_1806_ = lean_ctor_get(v___x_1790_, 0);
                                    v_isSharedCheck_1813_ = (!lean_is_exclusive(v___x_1790_)) as u8;
                                    if v_isSharedCheck_1813_ == 0 {
                                        v___x_1808_ = v___x_1790_;
                                        v_isShared_1809_ = v_isSharedCheck_1813_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1806_);
                                        lean_dec(v___x_1790_);
                                        v___x_1808_ = lean_box(0);
                                        v_isShared_1809_ = v_isSharedCheck_1813_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_ext_1745_);
                                v___x_1814_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once), _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11);
                                v___x_1815_ = l_Lean_MessageData_ofName(v_attrName_1746_);
                                v___x_1816_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1816_, 0, v___x_1814_);
                                lean_ctor_set(v___x_1816_, 1, v___x_1815_);
                                v___x_1817_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once), _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13);
                                v___x_1818_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1818_, 0, v___x_1816_);
                                lean_ctor_set(v___x_1818_, 1, v___x_1817_);
                                v___x_1819_ =
                                    l_Lean_MessageData_ofConstName(v_declName_1747_, v___x_1753_);
                                v___x_1820_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1820_, 0, v___x_1818_);
                                lean_ctor_set(v___x_1820_, 1, v___x_1819_);
                                v___x_1821_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17_once), _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17);
                                v___x_1822_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1822_, 0, v___x_1820_);
                                lean_ctor_set(v___x_1822_, 1, v___x_1821_);
                                v___x_1823_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v___x_1822_, v___x_1761_, v___x_1766_, v___y_1750_, v___y_1751_);
                                lean_dec_ref_known(v___x_1761_, 7);
                                v___y_1785_ = v___x_1823_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1776_);
                            lean_dec(v___x_1766_);
                            lean_dec_ref_known(v___x_1761_, 7);
                            lean_dec(v_declName_1747_);
                            lean_dec(v_attrName_1746_);
                            lean_dec_ref(v_ext_1745_);
                            v_a_1824_ = lean_ctor_get(v___x_1787_, 0);
                            v_isSharedCheck_1831_ = (!lean_is_exclusive(v___x_1787_)) as u8;
                            if v_isSharedCheck_1831_ == 0 {
                                v___x_1826_ = v___x_1787_;
                                v_isShared_1827_ = v_isSharedCheck_1831_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1824_);
                                lean_dec(v___x_1787_);
                                v___x_1826_ = lean_box(0);
                                v_isShared_1827_ = v_isSharedCheck_1831_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_ext_1745_);
                        v___x_1832_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once
                            ),
                            _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11,
                        );
                        v___x_1833_ = l_Lean_MessageData_ofName(v_attrName_1746_);
                        v___x_1834_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1834_, 0, v___x_1832_);
                        lean_ctor_set(v___x_1834_, 1, v___x_1833_);
                        v___x_1835_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once
                            ),
                            _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13,
                        );
                        v___x_1836_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1836_, 0, v___x_1834_);
                        lean_ctor_set(v___x_1836_, 1, v___x_1835_);
                        v___x_1837_ = l_Lean_MessageData_ofConstName(v_declName_1747_, v___x_1753_);
                        v___x_1838_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1838_, 0, v___x_1836_);
                        lean_ctor_set(v___x_1838_, 1, v___x_1837_);
                        v___x_1839_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19_once
                            ),
                            _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19,
                        );
                        v___x_1840_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1840_, 0, v___x_1838_);
                        lean_ctor_set(v___x_1840_, 1, v___x_1839_);
                        v___x_1841_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v___x_1840_, v___x_1761_, v___x_1766_, v___y_1750_, v___y_1751_);
                        lean_dec_ref_known(v___x_1761_, 7);
                        v___y_1785_ = v___x_1841_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_attrName_1746_);
                    v___x_1842_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(
                        v_ext_1745_,
                        v_declName_1747_,
                        v_attrKind_1749_,
                        v___x_1761_,
                        v___x_1766_,
                        v___y_1750_,
                        v___y_1751_,
                    );
                    lean_dec_ref_known(v___x_1761_, 7);
                    v___y_1785_ = v___x_1842_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1780_ = lean_st_ref_get(v___x_1766_);
                lean_dec(v___x_1766_);
                lean_dec(v___x_1780_);
                if v_isShared_1777_ == 0 {
                    lean_ctor_set(v___x_1776_, 0, v___x_1778_);
                    v___x_1782_ = v___x_1776_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1778_);
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1782_;
            }
            4 => {
                if lean_obj_tag(v___y_1785_) == 0 {
                    lean_dec_ref_known(v___y_1785_, 1);
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_1776_);
                    lean_dec(v___x_1766_);
                    return v___y_1785_;
                }
            }
            5 => {
                if v_isShared_1809_ == 0 {
                    v___x_1811_ = v___x_1808_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
                    v___x_1811_ = v_reuseFailAlloc_1812_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1811_;
            }
            7 => {
                if v_isShared_1827_ == 0 {
                    v___x_1829_ = v___x_1826_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
                    v___x_1829_ = v_reuseFailAlloc_1830_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1829_;
            }
            9 => {
                if v_isShared_1847_ == 0 {
                    v___x_1849_ = v___x_1846_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
                    v___x_1849_ = v_reuseFailAlloc_1850_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1849_;
            }
            11 => {
                if v_isShared_1855_ == 0 {
                    v___x_1857_ = v___x_1854_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
                    v___x_1857_ = v_reuseFailAlloc_1858_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed(
    mut v___x_1860_: *mut LeanObject,
    mut v_ext_1861_: *mut LeanObject,
    mut v_attrName_1862_: *mut LeanObject,
    mut v_declName_1863_: *mut LeanObject,
    mut v_x_1864_: *mut LeanObject,
    mut v_attrKind_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_1869_: u8 = 0;
    let mut v_res_1870_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_1869_ = (lean_unbox(v_attrKind_1865_) as u8);
    v_res_1870_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(
        v___x_1860_,
        v_ext_1861_,
        v_attrName_1862_,
        v_declName_1863_,
        v_x_1864_,
        v_attrKind_boxed_1869_,
        v___y_1866_,
        v___y_1867_,
    );
    lean_dec(v___y_1867_);
    lean_dec_ref(v___y_1866_);
    lean_dec(v_x_1864_);
    return v_res_1870_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpAttr(
    mut v_attrName_1872_: *mut LeanObject,
    mut v_attrDescr_1873_: *mut LeanObject,
    mut v_ext_1874_: *mut LeanObject,
    mut v_ref_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___f_1877_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0;
    v___x_1878_ = lean_box(1);
    lean_inc(v_attrName_1872_);
    v___f_1879_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_1879_, 0, v___x_1878_);
    lean_closure_set(v___f_1879_, 1, v_ext_1874_);
    lean_closure_set(v___f_1879_, 2, v_attrName_1872_);
    v___x_1880_ = 1;
    v___x_1881_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_1881_, 0, v_ref_1875_);
    lean_ctor_set(v___x_1881_, 1, v_attrName_1872_);
    lean_ctor_set(v___x_1881_, 2, v_attrDescr_1873_);
    lean_ctor_set_uint8(
        v___x_1881_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_1880_,
    );
    v___x_1882_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1882_, 0, v___x_1881_);
    lean_ctor_set(v___x_1882_, 1, v___f_1879_);
    lean_ctor_set(v___x_1882_, 2, v___f_1877_);
    v___x_1883_ = l_Lean_registerBuiltinAttribute(v___x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpAttr___boxed(
    mut v_attrName_1884_: *mut LeanObject,
    mut v_attrDescr_1885_: *mut LeanObject,
    mut v_ext_1886_: *mut LeanObject,
    mut v_ref_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1889_: *mut LeanObject = core::ptr::null_mut();
    v_res_1889_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(
        v_attrName_1884_,
        v_attrDescr_1885_,
        v_ext_1886_,
        v_ref_1887_,
    );
    return v_res_1889_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2(
    mut v_00_u03b1_1890_: *mut LeanObject,
    mut v_msg_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(
        v_msg_1891_,
        v___y_1892_,
        v___y_1893_,
        v___y_1894_,
        v___y_1895_,
    );
    return v___x_1897_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___boxed(
    mut v_00_u03b1_1898_: *mut LeanObject,
    mut v_msg_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
    mut v___y_1903_: *mut LeanObject,
    mut v___y_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1905_: *mut LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2(
        v_00_u03b1_1898_,
        v_msg_1899_,
        v___y_1900_,
        v___y_1901_,
        v___y_1902_,
        v___y_1903_,
    );
    lean_dec(v___y_1903_);
    lean_dec_ref(v___y_1902_);
    lean_dec(v___y_1901_);
    lean_dec_ref(v___y_1900_);
    return v_res_1905_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3(
    mut v_00_u03b1_1906_: *mut LeanObject,
    mut v_msg_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(
        v_msg_1907_,
        v___y_1908_,
        v___y_1909_,
    );
    return v___x_1911_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___boxed(
    mut v_00_u03b1_1912_: *mut LeanObject,
    mut v_msg_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1917_: *mut LeanObject = core::ptr::null_mut();
    v_res_1917_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3(
        v_00_u03b1_1912_,
        v_msg_1913_,
        v___y_1914_,
        v___y_1915_,
    );
    lean_dec(v___y_1915_);
    lean_dec_ref(v___y_1914_);
    return v_res_1917_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(
    mut v_00_u03b1_1918_: *mut LeanObject,
    mut v_constName_1919_: *mut LeanObject,
    mut v___y_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(v_constName_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
    return v___x_1925_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___boxed(
    mut v_00_u03b1_1926_: *mut LeanObject,
    mut v_constName_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_00_u03b1_1926_, v_constName_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
    lean_dec(v___y_1931_);
    lean_dec_ref(v___y_1930_);
    lean_dec(v___y_1929_);
    lean_dec_ref(v___y_1928_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1934_: *mut LeanObject,
    mut v_ref_1935_: *mut LeanObject,
    mut v_constName_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_1935_, v_constName_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
    return v___x_1942_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1943_: *mut LeanObject,
    mut v_ref_1944_: *mut LeanObject,
    mut v_constName_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1951_: *mut LeanObject = core::ptr::null_mut();
    v_res_1951_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1(v_00_u03b1_1943_, v_ref_1944_, v_constName_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
    lean_dec(v___y_1949_);
    lean_dec_ref(v___y_1948_);
    lean_dec(v___y_1947_);
    lean_dec_ref(v___y_1946_);
    lean_dec(v_ref_1944_);
    return v_res_1951_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7(
    mut v_00_u03b1_1952_: *mut LeanObject,
    mut v_ref_1953_: *mut LeanObject,
    mut v_msg_1954_: *mut LeanObject,
    mut v_declHint_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
    mut v___y_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_1953_, v_msg_1954_, v_declHint_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
    return v___x_1961_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___boxed(
    mut v_00_u03b1_1962_: *mut LeanObject,
    mut v_ref_1963_: *mut LeanObject,
    mut v_msg_1964_: *mut LeanObject,
    mut v_declHint_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
    mut v___y_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1971_: *mut LeanObject = core::ptr::null_mut();
    v_res_1971_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7(v_00_u03b1_1962_, v_ref_1963_, v_msg_1964_, v_declHint_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
    lean_dec(v___y_1969_);
    lean_dec_ref(v___y_1968_);
    lean_dec(v___y_1967_);
    lean_dec_ref(v___y_1966_);
    lean_dec(v_ref_1963_);
    return v_res_1971_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(
    mut v_msg_1972_: *mut LeanObject,
    mut v_declHint_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
    mut v___y_1975_: *mut LeanObject,
    mut v___y_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    v___x_1979_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_1972_, v_declHint_1973_, v___y_1977_);
    return v___x_1979_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(
    mut v_msg_1980_: *mut LeanObject,
    mut v_declHint_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1987_: *mut LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
    lean_dec(v___y_1985_);
    lean_dec_ref(v___y_1984_);
    lean_dec(v___y_1983_);
    lean_dec_ref(v___y_1982_);
    return v_res_1987_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9(
    mut v_00_u03b1_1988_: *mut LeanObject,
    mut v_ref_1989_: *mut LeanObject,
    mut v_msg_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_1989_, v_msg_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
    return v___x_1996_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(
    mut v_00_u03b1_1997_: *mut LeanObject,
    mut v_ref_1998_: *mut LeanObject,
    mut v_msg_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2005_: *mut LeanObject = core::ptr::null_mut();
    v_res_2005_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9(v_00_u03b1_1997_, v_ref_1998_, v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
    lean_dec(v___y_2003_);
    lean_dec_ref(v___y_2002_);
    lean_dec(v___y_2001_);
    lean_dec_ref(v___y_2000_);
    lean_dec(v_ref_1998_);
    return v_res_2005_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1() -> *mut LeanObject {
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    v___x_2006_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28,
    );
    return v___x_2006_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(
    mut v_a_2007_: *mut LeanObject,
    mut v_x_2008_: *mut LeanObject,
) -> u8 {
    let mut v___x_2009_: u8 = 0;
    let mut v_key_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2008_) == 0 {
                    v___x_2009_ = 0;
                    return v___x_2009_;
                } else {
                    v_key_2010_ = lean_ctor_get(v_x_2008_, 0);
                    v_tail_2011_ = lean_ctor_get(v_x_2008_, 2);
                    v___x_2012_ = lean_name_eq(v_key_2010_, v_a_2007_);
                    if v___x_2012_ == 0 {
                        v_x_2008_ = v_tail_2011_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2012_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg___boxed(
    mut v_a_2014_: *mut LeanObject,
    mut v_x_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2016_: u8 = 0;
    let mut v_r_2017_: *mut LeanObject = core::ptr::null_mut();
    v_res_2016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_2014_, v_x_2015_);
    lean_dec(v_x_2015_);
    lean_dec(v_a_2014_);
    v_r_2017_ = lean_box((v_res_2016_) as usize);
    return v_r_2017_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(
    mut v_a_2018_: *mut LeanObject,
    mut v_b_2019_: *mut LeanObject,
    mut v_x_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2020_) == 0 {
                    lean_dec(v_b_2019_);
                    lean_dec(v_a_2018_);
                    return v_x_2020_;
                } else {
                    v_key_2021_ = lean_ctor_get(v_x_2020_, 0);
                    v_value_2022_ = lean_ctor_get(v_x_2020_, 1);
                    v_tail_2023_ = lean_ctor_get(v_x_2020_, 2);
                    v_isSharedCheck_2035_ = (!lean_is_exclusive(v_x_2020_)) as u8;
                    if v_isSharedCheck_2035_ == 0 {
                        v___x_2025_ = v_x_2020_;
                        v_isShared_2026_ = v_isSharedCheck_2035_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2023_);
                        lean_inc(v_value_2022_);
                        lean_inc(v_key_2021_);
                        lean_dec(v_x_2020_);
                        v___x_2025_ = lean_box(0);
                        v_isShared_2026_ = v_isSharedCheck_2035_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2027_ = lean_name_eq(v_key_2021_, v_a_2018_);
                if v___x_2027_ == 0 {
                    v___x_2028_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_2018_, v_b_2019_, v_tail_2023_);
                    if v_isShared_2026_ == 0 {
                        lean_ctor_set(v___x_2025_, 2, v___x_2028_);
                        v___x_2030_ = v___x_2025_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_key_2021_);
                        lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_value_2022_);
                        lean_ctor_set(v_reuseFailAlloc_2031_, 2, v___x_2028_);
                        v___x_2030_ = v_reuseFailAlloc_2031_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2022_);
                    lean_dec(v_key_2021_);
                    if v_isShared_2026_ == 0 {
                        lean_ctor_set(v___x_2025_, 1, v_b_2019_);
                        lean_ctor_set(v___x_2025_, 0, v_a_2018_);
                        v___x_2033_ = v___x_2025_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2018_);
                        lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_b_2019_);
                        lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_tail_2023_);
                        v___x_2033_ = v_reuseFailAlloc_2034_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2030_;
            }
            3 => {
                return v___x_2033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: u64 = 0;
    v___x_2036_ = lean_unsigned_to_nat(1723);
    v___x_2037_ = lean_uint64_of_nat(v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_2038_: *mut LeanObject,
    mut v_x_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2048_: u64 = 0;
    let mut v___x_2049_: u64 = 0;
    let mut v___x_2050_: u64 = 0;
    let mut v_fold_2051_: u64 = 0;
    let mut v___x_2052_: u64 = 0;
    let mut v___x_2053_: u64 = 0;
    let mut v___x_2054_: u64 = 0;
    let mut v___x_2055_: usize = 0;
    let mut v___x_2056_: usize = 0;
    let mut v___x_2057_: usize = 0;
    let mut v___x_2058_: usize = 0;
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u64 = 0;
    let mut v_hash_2067_: u64 = 0;
    let mut v_isSharedCheck_2068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2039_) == 0 {
                    return v_x_2038_;
                } else {
                    v_key_2040_ = lean_ctor_get(v_x_2039_, 0);
                    v_value_2041_ = lean_ctor_get(v_x_2039_, 1);
                    v_tail_2042_ = lean_ctor_get(v_x_2039_, 2);
                    v_isSharedCheck_2068_ = (!lean_is_exclusive(v_x_2039_)) as u8;
                    if v_isSharedCheck_2068_ == 0 {
                        v___x_2044_ = v_x_2039_;
                        v_isShared_2045_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2042_);
                        lean_inc(v_value_2041_);
                        lean_inc(v_key_2040_);
                        lean_dec(v_x_2039_);
                        v___x_2044_ = lean_box(0);
                        v_isShared_2045_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2046_ = lean_array_get_size(v_x_2038_);
                if lean_obj_tag(v_key_2040_) == 0 {
                    v___x_2066_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_2048_ = v___x_2066_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2067_ = lean_ctor_get_uint64(
                        v_key_2040_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2048_ = v_hash_2067_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2049_ = 32u64;
                v___x_2050_ = lean_uint64_shift_right(v___y_2048_, v___x_2049_);
                v_fold_2051_ = lean_uint64_xor(v___y_2048_, v___x_2050_);
                v___x_2052_ = 16u64;
                v___x_2053_ = lean_uint64_shift_right(v_fold_2051_, v___x_2052_);
                v___x_2054_ = lean_uint64_xor(v_fold_2051_, v___x_2053_);
                v___x_2055_ = lean_uint64_to_usize(v___x_2054_);
                v___x_2056_ = lean_usize_of_nat(v___x_2046_);
                v___x_2057_ = 1usize;
                v___x_2058_ = lean_usize_sub(v___x_2056_, v___x_2057_);
                v___x_2059_ = lean_usize_land(v___x_2055_, v___x_2058_);
                v___x_2060_ = lean_array_uget_borrowed(v_x_2038_, v___x_2059_);
                lean_inc(v___x_2060_);
                if v_isShared_2045_ == 0 {
                    lean_ctor_set(v___x_2044_, 2, v___x_2060_);
                    v___x_2062_ = v___x_2044_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_key_2040_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_value_2041_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 2, v___x_2060_);
                    v___x_2062_ = v_reuseFailAlloc_2065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2063_ = lean_array_uset(v_x_2038_, v___x_2059_, v___x_2062_);
                v_x_2038_ = v___x_2063_;
                v_x_2039_ = v_tail_2042_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(
    mut v_i_2069_: *mut LeanObject,
    mut v_source_2070_: *mut LeanObject,
    mut v_target_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: u8 = 0;
    let mut v_es_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2072_ = lean_array_get_size(v_source_2070_);
                v___x_2073_ = lean_nat_dec_lt(v_i_2069_, v___x_2072_);
                if v___x_2073_ == 0 {
                    lean_dec_ref(v_source_2070_);
                    lean_dec(v_i_2069_);
                    return v_target_2071_;
                } else {
                    v_es_2074_ = lean_array_fget(v_source_2070_, v_i_2069_);
                    v___x_2075_ = lean_box(0);
                    v_source_2076_ = lean_array_fset(v_source_2070_, v_i_2069_, v___x_2075_);
                    v_target_2077_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2071_, v_es_2074_);
                    v___x_2078_ = lean_unsigned_to_nat(1);
                    v___x_2079_ = lean_nat_add(v_i_2069_, v___x_2078_);
                    lean_dec(v_i_2069_);
                    v_i_2069_ = v___x_2079_;
                    v_source_2070_ = v_source_2076_;
                    v_target_2071_ = v_target_2077_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(
    mut v_data_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    v___x_2082_ = lean_array_get_size(v_data_2081_);
    v___x_2083_ = lean_unsigned_to_nat(2);
    v_nbuckets_2084_ = lean_nat_mul(v___x_2082_, v___x_2083_);
    v___x_2085_ = lean_unsigned_to_nat(0);
    v___x_2086_ = lean_box(0);
    v___x_2087_ = lean_mk_array(v_nbuckets_2084_, v___x_2086_);
    v___x_2088_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_2085_, v_data_2081_, v___x_2087_);
    return v___x_2088_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(
    mut v_m_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
    mut v_b_2091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2096_: u8 = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2099_: u64 = 0;
    let mut v___x_2100_: u64 = 0;
    let mut v___x_2101_: u64 = 0;
    let mut v_fold_2102_: u64 = 0;
    let mut v___x_2103_: u64 = 0;
    let mut v___x_2104_: u64 = 0;
    let mut v___x_2105_: u64 = 0;
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: usize = 0;
    let mut v___x_2108_: usize = 0;
    let mut v___x_2109_: usize = 0;
    let mut v___x_2110_: usize = 0;
    let mut v_bkt_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v_val_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u64 = 0;
    let mut v_hash_2138_: u64 = 0;
    let mut v_isSharedCheck_2139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2092_ = lean_ctor_get(v_m_2089_, 0);
                v_buckets_2093_ = lean_ctor_get(v_m_2089_, 1);
                v_isSharedCheck_2139_ = (!lean_is_exclusive(v_m_2089_)) as u8;
                if v_isSharedCheck_2139_ == 0 {
                    v___x_2095_ = v_m_2089_;
                    v_isShared_2096_ = v_isSharedCheck_2139_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2093_);
                    lean_inc(v_size_2092_);
                    lean_dec(v_m_2089_);
                    v___x_2095_ = lean_box(0);
                    v_isShared_2096_ = v_isSharedCheck_2139_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2097_ = lean_array_get_size(v_buckets_2093_);
                if lean_obj_tag(v_a_2090_) == 0 {
                    v___x_2137_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_2099_ = v___x_2137_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2138_ = lean_ctor_get_uint64(
                        v_a_2090_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2099_ = v_hash_2138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2100_ = 32u64;
                v___x_2101_ = lean_uint64_shift_right(v___y_2099_, v___x_2100_);
                v_fold_2102_ = lean_uint64_xor(v___y_2099_, v___x_2101_);
                v___x_2103_ = 16u64;
                v___x_2104_ = lean_uint64_shift_right(v_fold_2102_, v___x_2103_);
                v___x_2105_ = lean_uint64_xor(v_fold_2102_, v___x_2104_);
                v___x_2106_ = lean_uint64_to_usize(v___x_2105_);
                v___x_2107_ = lean_usize_of_nat(v___x_2097_);
                v___x_2108_ = 1usize;
                v___x_2109_ = lean_usize_sub(v___x_2107_, v___x_2108_);
                v___x_2110_ = lean_usize_land(v___x_2106_, v___x_2109_);
                v_bkt_2111_ = lean_array_uget_borrowed(v_buckets_2093_, v___x_2110_);
                v___x_2112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_2090_, v_bkt_2111_);
                if v___x_2112_ == 0 {
                    v___x_2113_ = lean_unsigned_to_nat(1);
                    v_size_x27_2114_ = lean_nat_add(v_size_2092_, v___x_2113_);
                    lean_dec(v_size_2092_);
                    lean_inc(v_bkt_2111_);
                    v___x_2115_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2115_, 0, v_a_2090_);
                    lean_ctor_set(v___x_2115_, 1, v_b_2091_);
                    lean_ctor_set(v___x_2115_, 2, v_bkt_2111_);
                    v_buckets_x27_2116_ =
                        lean_array_uset(v_buckets_2093_, v___x_2110_, v___x_2115_);
                    v___x_2117_ = lean_unsigned_to_nat(4);
                    v___x_2118_ = lean_nat_mul(v_size_x27_2114_, v___x_2117_);
                    v___x_2119_ = lean_unsigned_to_nat(3);
                    v___x_2120_ = lean_nat_div(v___x_2118_, v___x_2119_);
                    lean_dec(v___x_2118_);
                    v___x_2121_ = lean_array_get_size(v_buckets_x27_2116_);
                    v___x_2122_ = lean_nat_dec_le(v___x_2120_, v___x_2121_);
                    lean_dec(v___x_2120_);
                    if v___x_2122_ == 0 {
                        v_val_2123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_2116_);
                        if v_isShared_2096_ == 0 {
                            lean_ctor_set(v___x_2095_, 1, v_val_2123_);
                            lean_ctor_set(v___x_2095_, 0, v_size_x27_2114_);
                            v___x_2125_ = v___x_2095_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_size_x27_2114_);
                            lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_val_2123_);
                            v___x_2125_ = v_reuseFailAlloc_2126_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2096_ == 0 {
                            lean_ctor_set(v___x_2095_, 1, v_buckets_x27_2116_);
                            lean_ctor_set(v___x_2095_, 0, v_size_x27_2114_);
                            v___x_2128_ = v___x_2095_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_size_x27_2114_);
                            lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_buckets_x27_2116_);
                            v___x_2128_ = v_reuseFailAlloc_2129_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2111_);
                    v___x_2130_ = lean_box(0);
                    v_buckets_x27_2131_ =
                        lean_array_uset(v_buckets_2093_, v___x_2110_, v___x_2130_);
                    v___x_2132_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_2090_, v_b_2091_, v_bkt_2111_);
                    v___x_2133_ = lean_array_uset(v_buckets_x27_2131_, v___x_2110_, v___x_2132_);
                    if v_isShared_2096_ == 0 {
                        lean_ctor_set(v___x_2095_, 1, v___x_2133_);
                        v___x_2135_ = v___x_2095_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_size_2092_);
                        lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2133_);
                        v___x_2135_ = v_reuseFailAlloc_2136_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2125_;
            }
            4 => {
                return v___x_2128_;
            }
            5 => {
                return v___x_2135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_registerSymSimpAttr(
    mut v_attrName_2140_: *mut LeanObject,
    mut v_attrDescr_2141_: *mut LeanObject,
    mut v_ref_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2149_: u8 = 0;
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_unused_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_ref_2142_);
                v___x_2144_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v_ref_2142_);
                if lean_obj_tag(v___x_2144_) == 0 {
                    v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
                    lean_inc_n(v_a_2145_, 2);
                    lean_dec_ref_known(v___x_2144_, 1);
                    lean_inc(v_attrName_2140_);
                    v___x_2146_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(
                        v_attrName_2140_,
                        v_attrDescr_2141_,
                        v_a_2145_,
                        v_ref_2142_,
                    );
                    if lean_obj_tag(v___x_2146_) == 0 {
                        v_isSharedCheck_2157_ = (!lean_is_exclusive(v___x_2146_)) as u8;
                        if v_isSharedCheck_2157_ == 0 {
                            v_unused_2158_ = lean_ctor_get(v___x_2146_, 0);
                            lean_dec(v_unused_2158_);
                            v___x_2148_ = v___x_2146_;
                            v_isShared_2149_ = v_isSharedCheck_2157_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2146_);
                            v___x_2148_ = lean_box(0);
                            v_isShared_2149_ = v_isSharedCheck_2157_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2145_);
                        lean_dec(v_attrName_2140_);
                        v_a_2159_ = lean_ctor_get(v___x_2146_, 0);
                        v_isSharedCheck_2166_ = (!lean_is_exclusive(v___x_2146_)) as u8;
                        if v_isSharedCheck_2166_ == 0 {
                            v___x_2161_ = v___x_2146_;
                            v_isShared_2162_ = v_isSharedCheck_2166_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2159_);
                            lean_dec(v___x_2146_);
                            v___x_2161_ = lean_box(0);
                            v_isShared_2162_ = v_isSharedCheck_2166_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_ref_2142_);
                    lean_dec_ref(v_attrDescr_2141_);
                    lean_dec(v_attrName_2140_);
                    return v___x_2144_;
                }
            }
            1 => {
                v___x_2150_ = l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef;
                v___x_2151_ = lean_st_ref_take(v___x_2150_);
                lean_inc(v_a_2145_);
                v___x_2152_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v___x_2151_, v_attrName_2140_, v_a_2145_);
                v___x_2153_ = lean_st_ref_set(v___x_2150_, v___x_2152_);
                if v_isShared_2149_ == 0 {
                    lean_ctor_set(v___x_2148_, 0, v_a_2145_);
                    v___x_2155_ = v___x_2148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2145_);
                    v___x_2155_ = v_reuseFailAlloc_2156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2155_;
            }
            3 => {
                if v_isShared_2162_ == 0 {
                    v___x_2164_ = v___x_2161_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
                    v___x_2164_ = v_reuseFailAlloc_2165_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_registerSymSimpAttr___boxed(
    mut v_attrName_2167_: *mut LeanObject,
    mut v_attrDescr_2168_: *mut LeanObject,
    mut v_ref_2169_: *mut LeanObject,
    mut v_a_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2171_: *mut LeanObject = core::ptr::null_mut();
    v_res_2171_ =
        l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v_attrName_2167_, v_attrDescr_2168_, v_ref_2169_);
    return v_res_2171_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0(
    mut v_00_u03b2_2172_: *mut LeanObject,
    mut v_m_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
    mut v_b_2175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    v___x_2176_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v_m_2173_, v_a_2174_, v_b_2175_);
    return v___x_2176_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(
    mut v_00_u03b2_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
    mut v_x_2179_: *mut LeanObject,
) -> u8 {
    let mut v___x_2180_: u8 = 0;
    v___x_2180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_2178_, v_x_2179_);
    return v___x_2180_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___boxed(
    mut v_00_u03b2_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_x_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2184_: u8 = 0;
    let mut v_r_2185_: *mut LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(v_00_u03b2_2181_, v_a_2182_, v_x_2183_);
    lean_dec(v_x_2183_);
    lean_dec(v_a_2182_);
    v_r_2185_ = lean_box((v_res_2184_) as usize);
    return v_r_2185_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1(
    mut v_00_u03b2_2186_: *mut LeanObject,
    mut v_data_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    v___x_2188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_data_2187_);
    return v___x_2188_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2(
    mut v_00_u03b2_2189_: *mut LeanObject,
    mut v_a_2190_: *mut LeanObject,
    mut v_b_2191_: *mut LeanObject,
    mut v_x_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    v___x_2193_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_2190_, v_b_2191_, v_x_2192_);
    return v___x_2193_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2194_: *mut LeanObject,
    mut v_i_2195_: *mut LeanObject,
    mut v_source_2196_: *mut LeanObject,
    mut v_target_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    v___x_2198_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_2195_, v_source_2196_, v_target_2197_);
    return v___x_2198_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2199_: *mut LeanObject,
    mut v_x_2200_: *mut LeanObject,
    mut v_x_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    v___x_2202_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2200_, v_x_2201_);
    return v___x_2202_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v___x_2218_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_;
    v___x_2219_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_;
    v___x_2220_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_;
    v___x_2221_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_2218_, v___x_2219_, v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2____boxed(
    mut v_a_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2223_: *mut LeanObject = core::ptr::null_mut();
    v_res_2223_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
    return v_res_2223_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(
    mut v_a_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    v___x_2226_ = l_Lean_Meta_Sym_Simp_symSimpExtension;
    v___x_2227_ =
        l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_2226_, v_a_2224_);
    return v___x_2227_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg___boxed(
    mut v_a_2228_: *mut LeanObject,
    mut v_a_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2230_: *mut LeanObject = core::ptr::null_mut();
    v_res_2230_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_2228_);
    lean_dec(v_a_2228_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpTheorems(
    mut v_a_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    v___x_2234_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_2232_);
    return v___x_2234_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpTheorems___boxed(
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
    mut v_a_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2238_: *mut LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems(v_a_2235_, v_a_2236_);
    lean_dec(v_a_2236_);
    lean_dec_ref(v_a_2235_);
    return v_res_2238_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Sym_Simp_symSimpExtension = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_symSimpExtension);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1 =
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1();
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1);
    l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1 =
        _init_l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1();
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Attr(builtin);
}

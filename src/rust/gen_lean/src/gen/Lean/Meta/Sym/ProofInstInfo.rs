// Lean compiler output
// Module: Lean.Meta.Sym.ProofInstInfo
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.IsClass Lean.Meta.Sym.Util Lean.Meta.Sym.Eta
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_infer_type, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::Eta::{
    initialize_Lean_Meta_Sym_Eta, l_Lean_Meta_Sym_etaReduceAll,
    runtime_initialize_Lean_Meta_Sym_Eta,
};
use crate::r#gen::Lean::Meta::Sym::IsClass::{
    initialize_Lean_Meta_Sym_IsClass, l_Lean_Meta_Sym_isClass_x3f,
    runtime_initialize_Lean_Meta_Sym_IsClass,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_unfoldReducible,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Transform::{l_Lean_Core_betaReduce, l_Lean_Meta_zetaReduce};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_preprocessType(
    mut v_type_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ =
        l_Lean_Meta_Sym_unfoldReducible(v_type_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
    if crate::leanh::lean_obj_tag(v___x_1110_) == 0 {
        let mut v_a_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1111_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
        crate::leanh::lean_inc(v_a_1111_);
        crate::leanh::lean_dec_ref_known(v___x_1110_, 1);
        v___x_1112_ = l_Lean_Core_betaReduce(v_a_1111_, v_a_1107_, v_a_1108_);
        if crate::leanh::lean_obj_tag(v___x_1112_) == 0 {
            let mut v_a_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1114_: u8 = 0;
            let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1113_ = crate::leanh::lean_ctor_get(v___x_1112_, 0);
            crate::leanh::lean_inc(v_a_1113_);
            crate::leanh::lean_dec_ref_known(v___x_1112_, 1);
            v___x_1114_ = 1;
            v___x_1115_ = l_Lean_Meta_zetaReduce(
                v_a_1113_,
                v___x_1114_,
                v___x_1114_,
                v___x_1114_,
                v_a_1105_,
                v_a_1106_,
                v_a_1107_,
                v_a_1108_,
            );
            if crate::leanh::lean_obj_tag(v___x_1115_) == 0 {
                let mut v_a_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_1116_ = crate::leanh::lean_ctor_get(v___x_1115_, 0);
                crate::leanh::lean_inc(v_a_1116_);
                crate::leanh::lean_dec_ref_known(v___x_1115_, 1);
                v___x_1117_ = l_Lean_Meta_Sym_etaReduceAll(v_a_1116_, v_a_1107_, v_a_1108_);
                return v___x_1117_;
            } else {
                return v___x_1115_;
            }
        } else {
            return v___x_1112_;
        }
    } else {
        return v___x_1110_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_preprocessType___boxed(
    mut v_type_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1124_ =
        l_Lean_Meta_Sym_preprocessType(v_type_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
    crate::leanh::lean_dec(v_a_1122_);
    crate::leanh::lean_dec_ref(v_a_1121_);
    crate::leanh::lean_dec(v_a_1120_);
    crate::leanh::lean_dec_ref(v_a_1119_);
    return v_res_1124_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0(
    mut v___x_1125_: *mut crate::leanh::LeanObject,
    mut v_as_1126_: *mut crate::leanh::LeanObject,
    mut v_sz_1127_: usize,
    mut v_i_1128_: usize,
    mut v_b_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___y_1146_: u8 = 0;
    let mut v___y_1147_: u8 = 0;
    let mut v_found_1148_: u8 = 0;
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: usize = 0;
    let mut v___x_1155_: usize = 0;
    let mut v_reuseFailAlloc_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1159_: u8 = 0;
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: u8 = 0;
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: u8 = 0;
    let mut v_a_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v_a_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: u8 = 0;
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_a_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1135_ = lean_usize_dec_lt(v_i_1128_, v_sz_1127_);
                if v___x_1135_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1125_);
                    v___x_1136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1136_, 0, v_b_1129_);
                    return v___x_1136_;
                } else {
                    v_a_1137_ = lean_array_uget_borrowed(v_as_1126_, v_i_1128_);
                    crate::leanh::lean_inc(v___y_1133_);
                    crate::leanh::lean_inc_ref(v___y_1132_);
                    crate::leanh::lean_inc(v___y_1131_);
                    crate::leanh::lean_inc_ref(v___y_1130_);
                    crate::leanh::lean_inc(v_a_1137_);
                    v___x_1138_ = lean_infer_type(
                        v_a_1137_,
                        v___y_1130_,
                        v___y_1131_,
                        v___y_1132_,
                        v___y_1133_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1138_) == 0 {
                        v_a_1139_ = crate::leanh::lean_ctor_get(v___x_1138_, 0);
                        crate::leanh::lean_inc(v_a_1139_);
                        crate::leanh::lean_dec_ref_known(v___x_1138_, 1);
                        v_fst_1140_ = crate::leanh::lean_ctor_get(v_b_1129_, 0);
                        v_snd_1141_ = crate::leanh::lean_ctor_get(v_b_1129_, 1);
                        v_isSharedCheck_1178_ = (!crate::leanh::lean_is_exclusive(v_b_1129_)) as u8;
                        if v_isSharedCheck_1178_ == 0 {
                            v___x_1143_ = v_b_1129_;
                            v_isShared_1144_ = v_isSharedCheck_1178_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1141_);
                            crate::leanh::lean_inc(v_fst_1140_);
                            crate::leanh::lean_dec(v_b_1129_);
                            v___x_1143_ = crate::leanh::lean_box(0);
                            v_isShared_1144_ = v_isSharedCheck_1178_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1129_);
                        crate::leanh::lean_dec_ref(v___x_1125_);
                        v_a_1179_ = crate::leanh::lean_ctor_get(v___x_1138_, 0);
                        v_isSharedCheck_1186_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1138_)) as u8;
                        if v_isSharedCheck_1186_ == 0 {
                            v___x_1181_ = v___x_1138_;
                            v_isShared_1182_ = v_isSharedCheck_1186_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1179_);
                            crate::leanh::lean_dec(v___x_1138_);
                            v___x_1181_ = crate::leanh::lean_box(0);
                            v_isShared_1182_ = v_isSharedCheck_1186_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1139_);
                crate::leanh::lean_inc_ref(v___x_1125_);
                v___x_1176_ = l_Lean_Meta_Sym_isClass_x3f(v___x_1125_, v_a_1139_);
                if crate::leanh::lean_obj_tag(v___x_1176_) == 0 {
                    v___x_1177_ = 0;
                    v___y_1159_ = v___x_1177_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1176_, 1);
                    v___y_1159_ = v___x_1135_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1149_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_1149_, 0 as u32, v___y_1146_);
                crate::leanh::lean_ctor_set_uint8(v___x_1149_, 1 as u32, v___y_1147_);
                v___x_1150_ = lean_array_push(v_fst_1140_, v___x_1149_);
                v___x_1151_ = crate::leanh::lean_box((v_found_1148_) as usize);
                if v_isShared_1144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1143_, 1, v___x_1151_);
                    crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1150_);
                    v___x_1153_ = v___x_1143_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1151_);
                    v___x_1153_ = v_reuseFailAlloc_1157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1154_ = 1usize;
                v___x_1155_ = lean_usize_add(v_i_1128_, v___x_1154_);
                v_i_1128_ = v___x_1155_;
                v_b_1129_ = v___x_1153_;
                state = 0;
                continue;
            }
            4 => {
                v___x_1160_ = l_Lean_Meta_isProp(
                    v_a_1139_,
                    v___y_1130_,
                    v___y_1131_,
                    v___y_1132_,
                    v___y_1133_,
                );
                if crate::leanh::lean_obj_tag(v___x_1160_) == 0 {
                    if v___y_1159_ == 0 {
                        v_a_1161_ = crate::leanh::lean_ctor_get(v___x_1160_, 0);
                        crate::leanh::lean_inc(v_a_1161_);
                        crate::leanh::lean_dec_ref_known(v___x_1160_, 1);
                        v___x_1162_ = (crate::leanh::lean_unbox(v_a_1161_) as u8);
                        if v___x_1162_ == 0 {
                            v___x_1163_ = (crate::leanh::lean_unbox(v_a_1161_) as u8);
                            crate::leanh::lean_dec(v_a_1161_);
                            v___x_1164_ = (crate::leanh::lean_unbox(v_snd_1141_) as u8);
                            crate::leanh::lean_dec(v_snd_1141_);
                            v___y_1146_ = v___x_1163_;
                            v___y_1147_ = v___y_1159_;
                            v_found_1148_ = v___x_1164_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_1141_);
                            v___x_1165_ = (crate::leanh::lean_unbox(v_a_1161_) as u8);
                            crate::leanh::lean_dec(v_a_1161_);
                            v___y_1146_ = v___x_1165_;
                            v___y_1147_ = v___y_1159_;
                            v_found_1148_ = v___x_1135_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1141_);
                        v_a_1166_ = crate::leanh::lean_ctor_get(v___x_1160_, 0);
                        crate::leanh::lean_inc(v_a_1166_);
                        crate::leanh::lean_dec_ref_known(v___x_1160_, 1);
                        v___x_1167_ = (crate::leanh::lean_unbox(v_a_1166_) as u8);
                        crate::leanh::lean_dec(v_a_1166_);
                        v___y_1146_ = v___x_1167_;
                        v___y_1147_ = v___y_1159_;
                        v_found_1148_ = v___x_1135_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1143_);
                    crate::leanh::lean_dec(v_snd_1141_);
                    crate::leanh::lean_dec(v_fst_1140_);
                    crate::leanh::lean_dec_ref(v___x_1125_);
                    v_a_1168_ = crate::leanh::lean_ctor_get(v___x_1160_, 0);
                    v_isSharedCheck_1175_ = (!crate::leanh::lean_is_exclusive(v___x_1160_)) as u8;
                    if v_isSharedCheck_1175_ == 0 {
                        v___x_1170_ = v___x_1160_;
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1168_);
                        crate::leanh::lean_dec(v___x_1160_);
                        v___x_1170_ = crate::leanh::lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1171_ == 0 {
                    v___x_1173_ = v___x_1170_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
                    v___x_1173_ = v_reuseFailAlloc_1174_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1173_;
            }
            7 => {
                if v_isShared_1182_ == 0 {
                    v___x_1184_ = v___x_1181_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
                    v___x_1184_ = v_reuseFailAlloc_1185_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0___boxed(
    mut v___x_1187_: *mut crate::leanh::LeanObject,
    mut v_as_1188_: *mut crate::leanh::LeanObject,
    mut v_sz_1189_: *mut crate::leanh::LeanObject,
    mut v_i_1190_: *mut crate::leanh::LeanObject,
    mut v_b_1191_: *mut crate::leanh::LeanObject,
    mut v___y_1192_: *mut crate::leanh::LeanObject,
    mut v___y_1193_: *mut crate::leanh::LeanObject,
    mut v___y_1194_: *mut crate::leanh::LeanObject,
    mut v___y_1195_: *mut crate::leanh::LeanObject,
    mut v___y_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1197_: usize = 0;
    let mut v_i_boxed_1198_: usize = 0;
    let mut v_res_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1197_ = crate::leanh::lean_unbox_usize(v_sz_1189_);
    crate::leanh::lean_dec(v_sz_1189_);
    v_i_boxed_1198_ = crate::leanh::lean_unbox_usize(v_i_1190_);
    crate::leanh::lean_dec(v_i_1190_);
    v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0(v___x_1187_, v_as_1188_, v_sz_boxed_1197_, v_i_boxed_1198_, v_b_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
    crate::leanh::lean_dec(v___y_1195_);
    crate::leanh::lean_dec_ref(v___y_1194_);
    crate::leanh::lean_dec(v___y_1193_);
    crate::leanh::lean_dec_ref(v___y_1192_);
    crate::leanh::lean_dec_ref(v_as_1188_);
    return v_res_1199_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(
    mut v_xs_1206_: *mut crate::leanh::LeanObject,
    mut v_a_1207_: *mut crate::leanh::LeanObject,
    mut v_a_1208_: *mut crate::leanh::LeanObject,
    mut v_a_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1215_: usize = 0;
    let mut v___x_1216_: usize = 0;
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v_snd_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: u8 = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut v_a_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1212_ = lean_st_ref_get(v_a_1210_);
                v_env_1213_ = crate::leanh::lean_ctor_get(v___x_1212_, 0);
                crate::leanh::lean_inc_ref(v_env_1213_);
                crate::leanh::lean_dec(v___x_1212_);
                v___x_1214_ = l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___closed__1;
                v_sz_1215_ = lean_array_size(v_xs_1206_);
                v___x_1216_ = 0usize;
                v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkProofInstArgInfo_x3f_spec__0(v_env_1213_, v_xs_1206_, v_sz_1215_, v___x_1216_, v___x_1214_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
                if crate::leanh::lean_obj_tag(v___x_1217_) == 0 {
                    v_a_1218_ = crate::leanh::lean_ctor_get(v___x_1217_, 0);
                    v_isSharedCheck_1233_ = (!crate::leanh::lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1233_ == 0 {
                        v___x_1220_ = v___x_1217_;
                        v_isShared_1221_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1218_);
                        crate::leanh::lean_dec(v___x_1217_);
                        v___x_1220_ = crate::leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1234_ = crate::leanh::lean_ctor_get(v___x_1217_, 0);
                    v_isSharedCheck_1241_ = (!crate::leanh::lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1236_ = v___x_1217_;
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1234_);
                        crate::leanh::lean_dec(v___x_1217_);
                        v___x_1236_ = crate::leanh::lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1222_ = crate::leanh::lean_ctor_get(v_a_1218_, 1);
                v___x_1223_ = (crate::leanh::lean_unbox(v_snd_1222_) as u8);
                if v___x_1223_ == 0 {
                    crate::leanh::lean_dec(v_a_1218_);
                    v___x_1224_ = crate::leanh::lean_box(0);
                    if v_isShared_1221_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1224_);
                        v___x_1226_ = v___x_1220_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
                        v___x_1226_ = v_reuseFailAlloc_1227_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_fst_1228_ = crate::leanh::lean_ctor_get(v_a_1218_, 0);
                    crate::leanh::lean_inc(v_fst_1228_);
                    crate::leanh::lean_dec(v_a_1218_);
                    v___x_1229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1229_, 0, v_fst_1228_);
                    if v_isShared_1221_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1229_);
                        v___x_1231_ = v___x_1220_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
                        v___x_1231_ = v_reuseFailAlloc_1232_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1226_;
            }
            3 => {
                return v___x_1231_;
            }
            4 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstArgInfo_x3f___boxed(
    mut v_xs_1242_: *mut crate::leanh::LeanObject,
    mut v_a_1243_: *mut crate::leanh::LeanObject,
    mut v_a_1244_: *mut crate::leanh::LeanObject,
    mut v_a_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(
        v_xs_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_,
    );
    crate::leanh::lean_dec(v_a_1246_);
    crate::leanh::lean_dec_ref(v_a_1245_);
    crate::leanh::lean_dec(v_a_1244_);
    crate::leanh::lean_dec_ref(v_a_1243_);
    crate::leanh::lean_dec_ref(v_xs_1242_);
    return v_res_1248_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0(
    mut v_k_1249_: *mut crate::leanh::LeanObject,
    mut v_b_1250_: *mut crate::leanh::LeanObject,
    mut v_c_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1255_);
    crate::leanh::lean_inc_ref(v___y_1254_);
    crate::leanh::lean_inc(v___y_1253_);
    crate::leanh::lean_inc_ref(v___y_1252_);
    v___x_1257_ = crate::leanh::lean_apply_7(
        v_k_1249_,
        v_b_1250_,
        v_c_1251_,
        v___y_1252_,
        v___y_1253_,
        v___y_1254_,
        v___y_1255_,
        crate::leanh::lean_box(0),
    );
    return v___x_1257_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0___boxed(
    mut v_k_1258_: *mut crate::leanh::LeanObject,
    mut v_b_1259_: *mut crate::leanh::LeanObject,
    mut v_c_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0(v_k_1258_, v_b_1259_, v_c_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
    crate::leanh::lean_dec(v___y_1264_);
    crate::leanh::lean_dec_ref(v___y_1263_);
    crate::leanh::lean_dec(v___y_1262_);
    crate::leanh::lean_dec_ref(v___y_1261_);
    return v_res_1266_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(
    mut v_type_1267_: *mut crate::leanh::LeanObject,
    mut v_k_1268_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1269_: u8,
    mut v_whnfType_1270_: u8,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_a_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1276_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1276_, 0, v_k_1268_);
                v___x_1277_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_1267_,
                    v___f_1276_,
                    v_cleanupAnnotations_1269_,
                    v_whnfType_1270_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                    v___y_1274_,
                );
                if crate::leanh::lean_obj_tag(v___x_1277_) == 0 {
                    v_a_1278_ = crate::leanh::lean_ctor_get(v___x_1277_, 0);
                    v_isSharedCheck_1285_ = (!crate::leanh::lean_is_exclusive(v___x_1277_)) as u8;
                    if v_isSharedCheck_1285_ == 0 {
                        v___x_1280_ = v___x_1277_;
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1278_);
                        crate::leanh::lean_dec(v___x_1277_);
                        v___x_1280_ = crate::leanh::lean_box(0);
                        v_isShared_1281_ = v_isSharedCheck_1285_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1286_ = crate::leanh::lean_ctor_get(v___x_1277_, 0);
                    v_isSharedCheck_1293_ = (!crate::leanh::lean_is_exclusive(v___x_1277_)) as u8;
                    if v_isSharedCheck_1293_ == 0 {
                        v___x_1288_ = v___x_1277_;
                        v_isShared_1289_ = v_isSharedCheck_1293_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1286_);
                        crate::leanh::lean_dec(v___x_1277_);
                        v___x_1288_ = crate::leanh::lean_box(0);
                        v_isShared_1289_ = v_isSharedCheck_1293_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1281_ == 0 {
                    v___x_1283_ = v___x_1280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
                    v___x_1283_ = v_reuseFailAlloc_1284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1283_;
            }
            3 => {
                if v_isShared_1289_ == 0 {
                    v___x_1291_ = v___x_1288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
                    v___x_1291_ = v_reuseFailAlloc_1292_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg___boxed(
    mut v_type_1294_: *mut crate::leanh::LeanObject,
    mut v_k_1295_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1296_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1303_: u8 = 0;
    let mut v_whnfType_boxed_1304_: u8 = 0;
    let mut v_res_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1303_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1296_) as u8);
    v_whnfType_boxed_1304_ = (crate::leanh::lean_unbox(v_whnfType_1297_) as u8);
    v_res_1305_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(v_type_1294_, v_k_1295_, v_cleanupAnnotations_boxed_1303_, v_whnfType_boxed_1304_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
    crate::leanh::lean_dec(v___y_1301_);
    crate::leanh::lean_dec_ref(v___y_1300_);
    crate::leanh::lean_dec(v___y_1299_);
    crate::leanh::lean_dec_ref(v___y_1298_);
    return v_res_1305_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1(
    mut v_00_u03b1_1306_: *mut crate::leanh::LeanObject,
    mut v_type_1307_: *mut crate::leanh::LeanObject,
    mut v_k_1308_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1309_: u8,
    mut v_whnfType_1310_: u8,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(v_type_1307_, v_k_1308_, v_cleanupAnnotations_1309_, v_whnfType_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
    return v___x_1316_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___boxed(
    mut v_00_u03b1_1317_: *mut crate::leanh::LeanObject,
    mut v_type_1318_: *mut crate::leanh::LeanObject,
    mut v_k_1319_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1320_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1327_: u8 = 0;
    let mut v_whnfType_boxed_1328_: u8 = 0;
    let mut v_res_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1327_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1320_) as u8);
    v_whnfType_boxed_1328_ = (crate::leanh::lean_unbox(v_whnfType_1321_) as u8);
    v_res_1329_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1(
            v_00_u03b1_1317_,
            v_type_1318_,
            v_k_1319_,
            v_cleanupAnnotations_boxed_1327_,
            v_whnfType_boxed_1328_,
            v___y_1322_,
            v___y_1323_,
            v___y_1324_,
            v___y_1325_,
        );
    crate::leanh::lean_dec(v___y_1325_);
    crate::leanh::lean_dec_ref(v___y_1324_);
    crate::leanh::lean_dec(v___y_1323_);
    crate::leanh::lean_dec_ref(v___y_1322_);
    return v_res_1329_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0(
    mut v_xs_1330_: *mut crate::leanh::LeanObject,
    mut v_x_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(
        v_xs_1330_,
        v___y_1332_,
        v___y_1333_,
        v___y_1334_,
        v___y_1335_,
    );
    return v___x_1337_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0___boxed(
    mut v_xs_1338_: *mut crate::leanh::LeanObject,
    mut v_x_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f___lam__0(
        v_xs_1338_,
        v_x_1339_,
        v___y_1340_,
        v___y_1341_,
        v___y_1342_,
        v___y_1343_,
    );
    crate::leanh::lean_dec(v___y_1343_);
    crate::leanh::lean_dec_ref(v___y_1342_);
    crate::leanh::lean_dec(v___y_1341_);
    crate::leanh::lean_dec_ref(v___y_1340_);
    crate::leanh::lean_dec_ref(v_x_1339_);
    crate::leanh::lean_dec_ref(v_xs_1338_);
    return v_res_1345_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_1348_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1348_, 0, v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_1350_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1351_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1351_, 0, v___x_1350_);
    crate::leanh::lean_ctor_set(v___x_1351_, 1, v___x_1350_);
    crate::leanh::lean_ctor_set(v___x_1351_, 2, v___x_1350_);
    crate::leanh::lean_ctor_set(v___x_1351_, 3, v___x_1350_);
    crate::leanh::lean_ctor_set(v___x_1351_, 4, v___x_1349_);
    crate::leanh::lean_ctor_set(v___x_1351_, 5, v___x_1349_);
    crate::leanh::lean_ctor_set(v___x_1351_, 6, v___x_1349_);
    crate::leanh::lean_ctor_set(v___x_1351_, 7, v___x_1349_);
    crate::leanh::lean_ctor_set(v___x_1351_, 8, v___x_1349_);
    crate::leanh::lean_ctor_set(v___x_1351_, 9, v___x_1349_);
    return v___x_1351_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1353_ = lean_mk_empty_array_with_capacity(v___x_1352_);
    v___x_1354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1354_, 0, v___x_1353_);
    return v___x_1354_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1355_: usize = 0;
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = 5usize;
    v___x_1356_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1357_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1358_ = lean_mk_empty_array_with_capacity(v___x_1357_);
    v___x_1359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_1360_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1360_, 0, v___x_1359_);
    crate::leanh::lean_ctor_set(v___x_1360_, 1, v___x_1358_);
    crate::leanh::lean_ctor_set(v___x_1360_, 2, v___x_1356_);
    crate::leanh::lean_ctor_set(v___x_1360_, 3, v___x_1356_);
    crate::leanh::lean_ctor_set_usize(v___x_1360_, 4, v___x_1355_);
    return v___x_1360_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1361_ = crate::leanh::lean_box(1);
    v___x_1362_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_1363_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_1364_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1363_);
    crate::leanh::lean_ctor_set(v___x_1364_, 1, v___x_1362_);
    crate::leanh::lean_ctor_set(v___x_1364_, 2, v___x_1361_);
    return v___x_1364_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
    return v___x_1367_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1369_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
    return v___x_1370_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
    return v___x_1373_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
    return v___x_1376_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1378_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
    return v___x_1379_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
    return v___x_1382_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
    return v___x_1385_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_msg_1386_: *mut crate::leanh::LeanObject,
    mut v_declHint_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v_isExporting_1393_: u8 = 0;
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ = lean_st_ref_get(v___y_1388_);
                v_env_1391_ = crate::leanh::lean_ctor_get(v___x_1390_, 0);
                crate::leanh::lean_inc_ref(v_env_1391_);
                crate::leanh::lean_dec(v___x_1390_);
                v___x_1392_ = l_Lean_Name_isAnonymous(v_declHint_1387_);
                if v___x_1392_ == 0 {
                    v_isExporting_1393_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1391_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1393_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1391_);
                        crate::leanh::lean_dec(v_declHint_1387_);
                        v___x_1394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1394_, 0, v_msg_1386_);
                        return v___x_1394_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1391_);
                        v___x_1395_ = l_Lean_Environment_setExporting(v_env_1391_, v___x_1392_);
                        crate::leanh::lean_inc(v_declHint_1387_);
                        crate::leanh::lean_inc_ref(v___x_1395_);
                        v___x_1396_ = l_Lean_Environment_contains(
                            v___x_1395_,
                            v_declHint_1387_,
                            v_isExporting_1393_,
                        );
                        if v___x_1396_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1395_);
                            crate::leanh::lean_dec_ref(v_env_1391_);
                            crate::leanh::lean_dec(v_declHint_1387_);
                            v___x_1397_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1397_, 0, v_msg_1386_);
                            return v___x_1397_;
                        } else {
                            v___x_1398_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_1399_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_1400_ = l_Lean_Options_empty;
                            v___x_1401_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1401_, 0, v___x_1395_);
                            crate::leanh::lean_ctor_set(v___x_1401_, 1, v___x_1398_);
                            crate::leanh::lean_ctor_set(v___x_1401_, 2, v___x_1399_);
                            crate::leanh::lean_ctor_set(v___x_1401_, 3, v___x_1400_);
                            crate::leanh::lean_inc(v_declHint_1387_);
                            v___x_1402_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1387_, v___x_1392_);
                            v_c_1403_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1403_, 0, v___x_1401_);
                            crate::leanh::lean_ctor_set(v_c_1403_, 1, v___x_1402_);
                            v___x_1404_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1391_,
                                v_declHint_1387_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1404_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1391_);
                                crate::leanh::lean_dec(v_declHint_1387_);
                                v___x_1405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_1406_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
                                crate::leanh::lean_ctor_set(v___x_1406_, 1, v_c_1403_);
                                v___x_1407_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_1408_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1408_, 0, v___x_1406_);
                                crate::leanh::lean_ctor_set(v___x_1408_, 1, v___x_1407_);
                                v___x_1409_ = l_Lean_MessageData_note(v___x_1408_);
                                v___x_1410_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1410_, 0, v_msg_1386_);
                                crate::leanh::lean_ctor_set(v___x_1410_, 1, v___x_1409_);
                                v___x_1411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1411_, 0, v___x_1410_);
                                return v___x_1411_;
                            } else {
                                v_val_1412_ = crate::leanh::lean_ctor_get(v___x_1404_, 0);
                                v_isSharedCheck_1447_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1404_)) as u8;
                                if v_isSharedCheck_1447_ == 0 {
                                    v___x_1414_ = v___x_1404_;
                                    v_isShared_1415_ = v_isSharedCheck_1447_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1412_);
                                    crate::leanh::lean_dec(v___x_1404_);
                                    v___x_1414_ = crate::leanh::lean_box(0);
                                    v_isShared_1415_ = v_isSharedCheck_1447_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1391_);
                    crate::leanh::lean_dec(v_declHint_1387_);
                    v___x_1448_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1448_, 0, v_msg_1386_);
                    return v___x_1448_;
                }
            }
            1 => {
                v___x_1416_ = crate::leanh::lean_box(0);
                v___x_1417_ = l_Lean_Environment_header(v_env_1391_);
                crate::leanh::lean_dec_ref(v_env_1391_);
                v___x_1418_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1417_);
                v_mod_1419_ = lean_array_get(v___x_1416_, v___x_1418_, v_val_1412_);
                crate::leanh::lean_dec(v_val_1412_);
                crate::leanh::lean_dec_ref(v___x_1418_);
                v___x_1420_ = l_Lean_isPrivateName(v_declHint_1387_);
                crate::leanh::lean_dec(v_declHint_1387_);
                if v___x_1420_ == 0 {
                    v___x_1421_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_1422_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1422_, 0, v___x_1421_);
                    crate::leanh::lean_ctor_set(v___x_1422_, 1, v_c_1403_);
                    v___x_1423_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_1424_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1424_, 0, v___x_1422_);
                    crate::leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
                    v___x_1425_ = l_Lean_MessageData_ofName(v_mod_1419_);
                    v___x_1426_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1424_);
                    crate::leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                    v___x_1427_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_1428_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1428_, 0, v___x_1426_);
                    crate::leanh::lean_ctor_set(v___x_1428_, 1, v___x_1427_);
                    v___x_1429_ = l_Lean_MessageData_note(v___x_1428_);
                    v___x_1430_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1430_, 0, v_msg_1386_);
                    crate::leanh::lean_ctor_set(v___x_1430_, 1, v___x_1429_);
                    if v_isShared_1415_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1414_, 0);
                        crate::leanh::lean_ctor_set(v___x_1414_, 0, v___x_1430_);
                        v___x_1432_ = v___x_1414_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
                        v___x_1432_ = v_reuseFailAlloc_1433_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1434_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_1435_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
                    crate::leanh::lean_ctor_set(v___x_1435_, 1, v_c_1403_);
                    v___x_1436_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_1437_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1437_, 0, v___x_1435_);
                    crate::leanh::lean_ctor_set(v___x_1437_, 1, v___x_1436_);
                    v___x_1438_ = l_Lean_MessageData_ofName(v_mod_1419_);
                    v___x_1439_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1437_);
                    crate::leanh::lean_ctor_set(v___x_1439_, 1, v___x_1438_);
                    v___x_1440_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_1441_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1441_, 0, v___x_1439_);
                    crate::leanh::lean_ctor_set(v___x_1441_, 1, v___x_1440_);
                    v___x_1442_ = l_Lean_MessageData_note(v___x_1441_);
                    v___x_1443_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1443_, 0, v_msg_1386_);
                    crate::leanh::lean_ctor_set(v___x_1443_, 1, v___x_1442_);
                    if v_isShared_1415_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1414_, 0);
                        crate::leanh::lean_ctor_set(v___x_1414_, 0, v___x_1443_);
                        v___x_1445_ = v___x_1414_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
                        v___x_1445_ = v_reuseFailAlloc_1446_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1432_;
            }
            3 => {
                return v___x_1445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_msg_1449_: *mut crate::leanh::LeanObject,
    mut v_declHint_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1449_, v_declHint_1450_, v___y_1451_);
    crate::leanh::lean_dec(v___y_1451_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_msg_1454_: *mut crate::leanh::LeanObject,
    mut v_declHint_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1461_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1454_, v_declHint_1455_, v___y_1459_);
                v_a_1462_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                v_isSharedCheck_1471_ = (!crate::leanh::lean_is_exclusive(v___x_1461_)) as u8;
                if v_isSharedCheck_1471_ == 0 {
                    v___x_1464_ = v___x_1461_;
                    v_isShared_1465_ = v_isSharedCheck_1471_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1462_);
                    crate::leanh::lean_dec(v___x_1461_);
                    v___x_1464_ = crate::leanh::lean_box(0);
                    v_isShared_1465_ = v_isSharedCheck_1471_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1466_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1467_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
                crate::leanh::lean_ctor_set(v___x_1467_, 1, v_a_1462_);
                if v_isShared_1465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1464_, 0, v___x_1467_);
                    v___x_1469_ = v___x_1464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
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
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1472_: *mut crate::leanh::LeanObject,
    mut v_declHint_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1479_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1472_, v_declHint_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
    crate::leanh::lean_dec(v___y_1477_);
    crate::leanh::lean_dec_ref(v___y_1476_);
    crate::leanh::lean_dec(v___y_1475_);
    crate::leanh::lean_dec_ref(v___y_1474_);
    return v_res_1479_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(
    mut v_msgData_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = lean_st_ref_get(v___y_1484_);
    v_env_1487_ = crate::leanh::lean_ctor_get(v___x_1486_, 0);
    crate::leanh::lean_inc_ref(v_env_1487_);
    crate::leanh::lean_dec(v___x_1486_);
    v___x_1488_ = lean_st_ref_get(v___y_1482_);
    v_mctx_1489_ = crate::leanh::lean_ctor_get(v___x_1488_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1489_);
    crate::leanh::lean_dec(v___x_1488_);
    v_lctx_1490_ = crate::leanh::lean_ctor_get(v___y_1481_, 2);
    v_options_1491_ = crate::leanh::lean_ctor_get(v___y_1483_, 2);
    crate::leanh::lean_inc_ref(v_options_1491_);
    crate::leanh::lean_inc_ref(v_lctx_1490_);
    v___x_1492_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1492_, 0, v_env_1487_);
    crate::leanh::lean_ctor_set(v___x_1492_, 1, v_mctx_1489_);
    crate::leanh::lean_ctor_set(v___x_1492_, 2, v_lctx_1490_);
    crate::leanh::lean_ctor_set(v___x_1492_, 3, v_options_1491_);
    v___x_1493_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1493_, 0, v___x_1492_);
    crate::leanh::lean_ctor_set(v___x_1493_, 1, v_msgData_1480_);
    v___x_1494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1494_, 0, v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(
    mut v_msgData_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v___y_1497_);
    crate::leanh::lean_dec_ref(v___y_1496_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_msg_1502_: *mut crate::leanh::LeanObject,
    mut v___y_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1508_ = crate::leanh::lean_ctor_get(v___y_1505_, 5);
                v___x_1509_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
                v_a_1510_ = crate::leanh::lean_ctor_get(v___x_1509_, 0);
                v_isSharedCheck_1518_ = (!crate::leanh::lean_is_exclusive(v___x_1509_)) as u8;
                if v_isSharedCheck_1518_ == 0 {
                    v___x_1512_ = v___x_1509_;
                    v_isShared_1513_ = v_isSharedCheck_1518_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1510_);
                    crate::leanh::lean_dec(v___x_1509_);
                    v___x_1512_ = crate::leanh::lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1508_);
                v___x_1514_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1514_, 0, v_ref_1508_);
                crate::leanh::lean_ctor_set(v___x_1514_, 1, v_a_1510_);
                if v_isShared_1513_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1512_, 1);
                    crate::leanh::lean_ctor_set(v___x_1512_, 0, v___x_1514_);
                    v___x_1516_ = v___x_1512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1517_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
                    v___x_1516_ = v_reuseFailAlloc_1517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_msg_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
    crate::leanh::lean_dec(v___y_1523_);
    crate::leanh::lean_dec_ref(v___y_1522_);
    crate::leanh::lean_dec(v___y_1521_);
    crate::leanh::lean_dec_ref(v___y_1520_);
    return v_res_1525_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_ref_1526_: *mut crate::leanh::LeanObject,
    mut v_msg_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1545_: u8 = 0;
    let mut v_cancelTk_x3f_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1547_: u8 = 0;
    let mut v_inheritedTraceOptions_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1533_ = crate::leanh::lean_ctor_get(v___y_1530_, 0);
    v_fileMap_1534_ = crate::leanh::lean_ctor_get(v___y_1530_, 1);
    v_options_1535_ = crate::leanh::lean_ctor_get(v___y_1530_, 2);
    v_currRecDepth_1536_ = crate::leanh::lean_ctor_get(v___y_1530_, 3);
    v_maxRecDepth_1537_ = crate::leanh::lean_ctor_get(v___y_1530_, 4);
    v_ref_1538_ = crate::leanh::lean_ctor_get(v___y_1530_, 5);
    v_currNamespace_1539_ = crate::leanh::lean_ctor_get(v___y_1530_, 6);
    v_openDecls_1540_ = crate::leanh::lean_ctor_get(v___y_1530_, 7);
    v_initHeartbeats_1541_ = crate::leanh::lean_ctor_get(v___y_1530_, 8);
    v_maxHeartbeats_1542_ = crate::leanh::lean_ctor_get(v___y_1530_, 9);
    v_quotContext_1543_ = crate::leanh::lean_ctor_get(v___y_1530_, 10);
    v_currMacroScope_1544_ = crate::leanh::lean_ctor_get(v___y_1530_, 11);
    v_diag_1545_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1530_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1546_ = crate::leanh::lean_ctor_get(v___y_1530_, 12);
    v_suppressElabErrors_1547_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1530_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1548_ = crate::leanh::lean_ctor_get(v___y_1530_, 13);
    v_ref_1549_ = l_Lean_replaceRef(v_ref_1526_, v_ref_1538_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1548_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1546_);
    crate::leanh::lean_inc(v_currMacroScope_1544_);
    crate::leanh::lean_inc(v_quotContext_1543_);
    crate::leanh::lean_inc(v_maxHeartbeats_1542_);
    crate::leanh::lean_inc(v_initHeartbeats_1541_);
    crate::leanh::lean_inc(v_openDecls_1540_);
    crate::leanh::lean_inc(v_currNamespace_1539_);
    crate::leanh::lean_inc(v_maxRecDepth_1537_);
    crate::leanh::lean_inc(v_currRecDepth_1536_);
    crate::leanh::lean_inc_ref(v_options_1535_);
    crate::leanh::lean_inc_ref(v_fileMap_1534_);
    crate::leanh::lean_inc_ref(v_fileName_1533_);
    v___x_1550_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1550_, 0, v_fileName_1533_);
    crate::leanh::lean_ctor_set(v___x_1550_, 1, v_fileMap_1534_);
    crate::leanh::lean_ctor_set(v___x_1550_, 2, v_options_1535_);
    crate::leanh::lean_ctor_set(v___x_1550_, 3, v_currRecDepth_1536_);
    crate::leanh::lean_ctor_set(v___x_1550_, 4, v_maxRecDepth_1537_);
    crate::leanh::lean_ctor_set(v___x_1550_, 5, v_ref_1549_);
    crate::leanh::lean_ctor_set(v___x_1550_, 6, v_currNamespace_1539_);
    crate::leanh::lean_ctor_set(v___x_1550_, 7, v_openDecls_1540_);
    crate::leanh::lean_ctor_set(v___x_1550_, 8, v_initHeartbeats_1541_);
    crate::leanh::lean_ctor_set(v___x_1550_, 9, v_maxHeartbeats_1542_);
    crate::leanh::lean_ctor_set(v___x_1550_, 10, v_quotContext_1543_);
    crate::leanh::lean_ctor_set(v___x_1550_, 11, v_currMacroScope_1544_);
    crate::leanh::lean_ctor_set(v___x_1550_, 12, v_cancelTk_x3f_1546_);
    crate::leanh::lean_ctor_set(v___x_1550_, 13, v_inheritedTraceOptions_1548_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1545_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1547_,
    );
    v___x_1551_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1527_, v___y_1528_, v___y_1529_, v___x_1550_, v___y_1531_);
    crate::leanh::lean_dec_ref_known(v___x_1550_, 14);
    return v___x_1551_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_1552_: *mut crate::leanh::LeanObject,
    mut v_msg_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1552_, v_msg_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
    crate::leanh::lean_dec(v___y_1557_);
    crate::leanh::lean_dec_ref(v___y_1556_);
    crate::leanh::lean_dec(v___y_1555_);
    crate::leanh::lean_dec_ref(v___y_1554_);
    crate::leanh::lean_dec(v_ref_1552_);
    return v_res_1559_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_ref_1560_: *mut crate::leanh::LeanObject,
    mut v_msg_1561_: *mut crate::leanh::LeanObject,
    mut v_declHint_1562_: *mut crate::leanh::LeanObject,
    mut v___y_1563_: *mut crate::leanh::LeanObject,
    mut v___y_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1561_, v_declHint_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
    v_a_1569_ = crate::leanh::lean_ctor_get(v___x_1568_, 0);
    crate::leanh::lean_inc(v_a_1569_);
    crate::leanh::lean_dec_ref(v___x_1568_);
    v___x_1570_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1560_, v_a_1569_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_ref_1571_: *mut crate::leanh::LeanObject,
    mut v_msg_1572_: *mut crate::leanh::LeanObject,
    mut v_declHint_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
    mut v___y_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1579_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1571_, v_msg_1572_, v_declHint_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
    crate::leanh::lean_dec(v___y_1577_);
    crate::leanh::lean_dec_ref(v___y_1576_);
    crate::leanh::lean_dec(v___y_1575_);
    crate::leanh::lean_dec_ref(v___y_1574_);
    crate::leanh::lean_dec(v_ref_1571_);
    return v_res_1579_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
    return v___x_1585_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_ref_1586_: *mut crate::leanh::LeanObject,
    mut v_constName_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_1594_ = 0;
    crate::leanh::lean_inc(v_constName_1587_);
    v___x_1595_ = l_Lean_MessageData_ofConstName(v_constName_1587_, v___x_1594_);
    v___x_1596_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1596_, 0, v___x_1593_);
    crate::leanh::lean_ctor_set(v___x_1596_, 1, v___x_1595_);
    v___x_1597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_1598_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1598_, 0, v___x_1596_);
    crate::leanh::lean_ctor_set(v___x_1598_, 1, v___x_1597_);
    v___x_1599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1586_, v___x_1598_, v_constName_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
    return v___x_1599_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_1600_: *mut crate::leanh::LeanObject,
    mut v_constName_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1600_, v_constName_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
    crate::leanh::lean_dec(v___y_1605_);
    crate::leanh::lean_dec_ref(v___y_1604_);
    crate::leanh::lean_dec(v___y_1603_);
    crate::leanh::lean_dec_ref(v___y_1602_);
    crate::leanh::lean_dec(v_ref_1600_);
    return v_res_1607_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(
    mut v_constName_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1614_ = crate::leanh::lean_ctor_get(v___y_1611_, 5);
    v___x_1615_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1614_, v_constName_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
    return v___x_1615_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(v_constName_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
    crate::leanh::lean_dec(v___y_1620_);
    crate::leanh::lean_dec_ref(v___y_1619_);
    crate::leanh::lean_dec(v___y_1618_);
    crate::leanh::lean_dec_ref(v___y_1617_);
    return v_res_1622_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0(
    mut v_constName_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1629_ = lean_st_ref_get(v___y_1627_);
                v_env_1630_ = crate::leanh::lean_ctor_get(v___x_1629_, 0);
                crate::leanh::lean_inc_ref(v_env_1630_);
                crate::leanh::lean_dec(v___x_1629_);
                v___x_1631_ = 0;
                crate::leanh::lean_inc(v_constName_1623_);
                v___x_1632_ =
                    l_Lean_Environment_find_x3f(v_env_1630_, v_constName_1623_, v___x_1631_);
                if crate::leanh::lean_obj_tag(v___x_1632_) == 0 {
                    v___x_1633_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(v_constName_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
                    return v___x_1633_;
                } else {
                    crate::leanh::lean_dec(v_constName_1623_);
                    v_val_1634_ = crate::leanh::lean_ctor_get(v___x_1632_, 0);
                    v_isSharedCheck_1641_ = (!crate::leanh::lean_is_exclusive(v___x_1632_)) as u8;
                    if v_isSharedCheck_1641_ == 0 {
                        v___x_1636_ = v___x_1632_;
                        v_isShared_1637_ = v_isSharedCheck_1641_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1634_);
                        crate::leanh::lean_dec(v___x_1632_);
                        v___x_1636_ = crate::leanh::lean_box(0);
                        v_isShared_1637_ = v_isSharedCheck_1641_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1637_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1636_, 0);
                    v___x_1639_ = v___x_1636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_val_1634_);
                    v___x_1639_ = v_reuseFailAlloc_1640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0___boxed(
    mut v_constName_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0(
        v_constName_1642_,
        v___y_1643_,
        v___y_1644_,
        v___y_1645_,
        v___y_1646_,
    );
    crate::leanh::lean_dec(v___y_1646_);
    crate::leanh::lean_dec_ref(v___y_1645_);
    crate::leanh::lean_dec(v___y_1644_);
    crate::leanh::lean_dec_ref(v___y_1643_);
    return v_res_1648_;
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f(
    mut v_declName_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut v_a_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1675_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1656_ =
                    l_Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0(
                        v_declName_1650_,
                        v_a_1651_,
                        v_a_1652_,
                        v_a_1653_,
                        v_a_1654_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1656_) == 0 {
                    v_a_1657_ = crate::leanh::lean_ctor_get(v___x_1656_, 0);
                    crate::leanh::lean_inc(v_a_1657_);
                    crate::leanh::lean_dec_ref_known(v___x_1656_, 1);
                    v___x_1658_ = l_Lean_ConstantInfo_type(v_a_1657_);
                    crate::leanh::lean_dec(v_a_1657_);
                    v___x_1659_ = l_Lean_Meta_Sym_preprocessType(
                        v___x_1658_,
                        v_a_1651_,
                        v_a_1652_,
                        v_a_1653_,
                        v_a_1654_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1659_) == 0 {
                        v_a_1660_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
                        crate::leanh::lean_inc(v_a_1660_);
                        crate::leanh::lean_dec_ref_known(v___x_1659_, 1);
                        v___f_1661_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f___closed__0;
                        v___x_1662_ = 0;
                        v___x_1663_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__1___redArg(v_a_1660_, v___f_1661_, v___x_1662_, v___x_1662_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
                        return v___x_1663_;
                    } else {
                        v_a_1664_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
                        v_isSharedCheck_1671_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1659_)) as u8;
                        if v_isSharedCheck_1671_ == 0 {
                            v___x_1666_ = v___x_1659_;
                            v_isShared_1667_ = v_isSharedCheck_1671_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1664_);
                            crate::leanh::lean_dec(v___x_1659_);
                            v___x_1666_ = crate::leanh::lean_box(0);
                            v_isShared_1667_ = v_isSharedCheck_1671_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_1672_ = crate::leanh::lean_ctor_get(v___x_1656_, 0);
                    v_isSharedCheck_1679_ = (!crate::leanh::lean_is_exclusive(v___x_1656_)) as u8;
                    if v_isSharedCheck_1679_ == 0 {
                        v___x_1674_ = v___x_1656_;
                        v_isShared_1675_ = v_isSharedCheck_1679_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1672_);
                        crate::leanh::lean_dec(v___x_1656_);
                        v___x_1674_ = crate::leanh::lean_box(0);
                        v_isShared_1675_ = v_isSharedCheck_1679_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1667_ == 0 {
                    v___x_1669_ = v___x_1666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
                    v___x_1669_ = v_reuseFailAlloc_1670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1669_;
            }
            3 => {
                if v_isShared_1675_ == 0 {
                    v___x_1677_ = v___x_1674_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
                    v___x_1677_ = v_reuseFailAlloc_1678_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkProofInstInfo_x3f___boxed(
    mut v_declName_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
    mut v_a_1683_: *mut crate::leanh::LeanObject,
    mut v_a_1684_: *mut crate::leanh::LeanObject,
    mut v_a_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f(
        v_declName_1680_,
        v_a_1681_,
        v_a_1682_,
        v_a_1683_,
        v_a_1684_,
    );
    crate::leanh::lean_dec(v_a_1684_);
    crate::leanh::lean_dec_ref(v_a_1683_);
    crate::leanh::lean_dec(v_a_1682_);
    crate::leanh::lean_dec_ref(v_a_1681_);
    return v_res_1686_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0(
    mut v_00_u03b1_1687_: *mut crate::leanh::LeanObject,
    mut v_constName_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___redArg(v_constName_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
    return v___x_1694_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_1695_: *mut crate::leanh::LeanObject,
    mut v_constName_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0(v_00_u03b1_1695_, v_constName_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
    crate::leanh::lean_dec(v___y_1700_);
    crate::leanh::lean_dec_ref(v___y_1699_);
    crate::leanh::lean_dec(v___y_1698_);
    crate::leanh::lean_dec_ref(v___y_1697_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b1_1703_: *mut crate::leanh::LeanObject,
    mut v_ref_1704_: *mut crate::leanh::LeanObject,
    mut v_constName_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1704_, v_constName_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
    return v___x_1711_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_1712_: *mut crate::leanh::LeanObject,
    mut v_ref_1713_: *mut crate::leanh::LeanObject,
    mut v_constName_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2(v_00_u03b1_1712_, v_ref_1713_, v_constName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
    crate::leanh::lean_dec(v___y_1718_);
    crate::leanh::lean_dec_ref(v___y_1717_);
    crate::leanh::lean_dec(v___y_1716_);
    crate::leanh::lean_dec_ref(v___y_1715_);
    crate::leanh::lean_dec(v_ref_1713_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b1_1721_: *mut crate::leanh::LeanObject,
    mut v_ref_1722_: *mut crate::leanh::LeanObject,
    mut v_msg_1723_: *mut crate::leanh::LeanObject,
    mut v_declHint_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1722_, v_msg_1723_, v_declHint_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
    return v___x_1730_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_00_u03b1_1731_: *mut crate::leanh::LeanObject,
    mut v_ref_1732_: *mut crate::leanh::LeanObject,
    mut v_msg_1733_: *mut crate::leanh::LeanObject,
    mut v_declHint_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1740_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1731_, v_ref_1732_, v_msg_1733_, v_declHint_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
    crate::leanh::lean_dec(v___y_1738_);
    crate::leanh::lean_dec_ref(v___y_1737_);
    crate::leanh::lean_dec(v___y_1736_);
    crate::leanh::lean_dec_ref(v___y_1735_);
    crate::leanh::lean_dec(v_ref_1732_);
    return v_res_1740_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(
    mut v_msg_1741_: *mut crate::leanh::LeanObject,
    mut v_declHint_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1741_, v_declHint_1742_, v___y_1746_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_msg_1749_: *mut crate::leanh::LeanObject,
    mut v_declHint_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
    mut v___y_1755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1756_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1749_, v_declHint_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
    crate::leanh::lean_dec(v___y_1754_);
    crate::leanh::lean_dec_ref(v___y_1753_);
    crate::leanh::lean_dec(v___y_1752_);
    crate::leanh::lean_dec_ref(v___y_1751_);
    return v_res_1756_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b1_1757_: *mut crate::leanh::LeanObject,
    mut v_ref_1758_: *mut crate::leanh::LeanObject,
    mut v_msg_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1758_, v_msg_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
    return v___x_1765_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_1766_: *mut crate::leanh::LeanObject,
    mut v_ref_1767_: *mut crate::leanh::LeanObject,
    mut v_msg_1768_: *mut crate::leanh::LeanObject,
    mut v___y_1769_: *mut crate::leanh::LeanObject,
    mut v___y_1770_: *mut crate::leanh::LeanObject,
    mut v___y_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1766_, v_ref_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
    crate::leanh::lean_dec(v___y_1772_);
    crate::leanh::lean_dec_ref(v___y_1771_);
    crate::leanh::lean_dec(v___y_1770_);
    crate::leanh::lean_dec_ref(v___y_1769_);
    crate::leanh::lean_dec(v_ref_1767_);
    return v_res_1774_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_1775_: *mut crate::leanh::LeanObject,
    mut v_msg_1776_: *mut crate::leanh::LeanObject,
    mut v___y_1777_: *mut crate::leanh::LeanObject,
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
    return v___x_1782_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_1783_: *mut crate::leanh::LeanObject,
    mut v_msg_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1790_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Sym_mkProofInstInfo_x3f_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1783_, v_msg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
    crate::leanh::lean_dec(v___y_1788_);
    crate::leanh::lean_dec_ref(v___y_1787_);
    crate::leanh::lean_dec(v___y_1786_);
    crate::leanh::lean_dec_ref(v___y_1785_);
    return v_res_1790_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1791_: *mut crate::leanh::LeanObject,
    mut v_vals_1792_: *mut crate::leanh::LeanObject,
    mut v_i_1793_: *mut crate::leanh::LeanObject,
    mut v_k_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1795_ = lean_array_get_size(v_keys_1791_);
                v___x_1796_ = lean_nat_dec_lt(v_i_1793_, v___x_1795_);
                if v___x_1796_ == 0 {
                    crate::leanh::lean_dec(v_i_1793_);
                    v___x_1797_ = crate::leanh::lean_box(0);
                    return v___x_1797_;
                } else {
                    v_k_x27_1798_ = lean_array_fget_borrowed(v_keys_1791_, v_i_1793_);
                    v___x_1799_ = lean_name_eq(v_k_1794_, v_k_x27_1798_);
                    if v___x_1799_ == 0 {
                        v___x_1800_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1801_ = lean_nat_add(v_i_1793_, v___x_1800_);
                        crate::leanh::lean_dec(v_i_1793_);
                        v_i_1793_ = v___x_1801_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1803_ = lean_array_fget_borrowed(v_vals_1792_, v_i_1793_);
                        crate::leanh::lean_dec(v_i_1793_);
                        crate::leanh::lean_inc(v___x_1803_);
                        v___x_1804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
                        return v___x_1804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1805_: *mut crate::leanh::LeanObject,
    mut v_vals_1806_: *mut crate::leanh::LeanObject,
    mut v_i_1807_: *mut crate::leanh::LeanObject,
    mut v_k_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1809_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1805_, v_vals_1806_, v_i_1807_, v_k_1808_);
    crate::leanh::lean_dec(v_k_1808_);
    crate::leanh::lean_dec_ref(v_vals_1806_);
    crate::leanh::lean_dec_ref(v_keys_1805_);
    return v_res_1809_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1810_: usize = 0;
    let mut v___x_1811_: usize = 0;
    let mut v___x_1812_: usize = 0;
    v___x_1810_ = 5usize;
    v___x_1811_ = 1usize;
    v___x_1812_ = lean_usize_shift_left(v___x_1811_, v___x_1810_);
    return v___x_1812_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1813_: usize = 0;
    let mut v___x_1814_: usize = 0;
    let mut v___x_1815_: usize = 0;
    v___x_1813_ = 1usize;
    v___x_1814_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_1815_ = lean_usize_sub(v___x_1814_, v___x_1813_);
    return v___x_1815_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(
    mut v_x_1816_: *mut crate::leanh::LeanObject,
    mut v_x_1817_: usize,
    mut v_x_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: usize = 0;
    let mut v___x_1822_: usize = 0;
    let mut v___x_1823_: usize = 0;
    let mut v_j_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: usize = 0;
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1816_) == 0 {
                    v_es_1819_ = crate::leanh::lean_ctor_get(v_x_1816_, 0);
                    v___x_1820_ = crate::leanh::lean_box(2);
                    v___x_1821_ = 5usize;
                    v___x_1822_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1823_ = lean_usize_land(v_x_1817_, v___x_1822_);
                    v_j_1824_ = lean_usize_to_nat(v___x_1823_);
                    v___x_1825_ = lean_array_get_borrowed(v___x_1820_, v_es_1819_, v_j_1824_);
                    crate::leanh::lean_dec(v_j_1824_);
                    match crate::leanh::lean_obj_tag(v___x_1825_) {
                        0 => {
                            v_key_1826_ = crate::leanh::lean_ctor_get(v___x_1825_, 0);
                            v_val_1827_ = crate::leanh::lean_ctor_get(v___x_1825_, 1);
                            v___x_1828_ = lean_name_eq(v_x_1818_, v_key_1826_);
                            if v___x_1828_ == 0 {
                                v___x_1829_ = crate::leanh::lean_box(0);
                                return v___x_1829_;
                            } else {
                                crate::leanh::lean_inc(v_val_1827_);
                                v___x_1830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1830_, 0, v_val_1827_);
                                return v___x_1830_;
                            }
                        }
                        1 => {
                            v_node_1831_ = crate::leanh::lean_ctor_get(v___x_1825_, 0);
                            v___x_1832_ = lean_usize_shift_right(v_x_1817_, v___x_1821_);
                            v_x_1816_ = v_node_1831_;
                            v_x_1817_ = v___x_1832_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1834_ = crate::leanh::lean_box(0);
                            return v___x_1834_;
                        }
                    }
                } else {
                    v_ks_1835_ = crate::leanh::lean_ctor_get(v_x_1816_, 0);
                    v_vs_1836_ = crate::leanh::lean_ctor_get(v_x_1816_, 1);
                    v___x_1837_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1838_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1835_, v_vs_1836_, v___x_1837_, v_x_1818_);
                    return v___x_1838_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_1839_: *mut crate::leanh::LeanObject,
    mut v_x_1840_: *mut crate::leanh::LeanObject,
    mut v_x_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2415__boxed_1842_: usize = 0;
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2415__boxed_1842_ = crate::leanh::lean_unbox_usize(v_x_1840_);
    crate::leanh::lean_dec(v_x_1840_);
    v_res_1843_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(v_x_1839_, v_x_2415__boxed_1842_, v_x_1841_);
    crate::leanh::lean_dec(v_x_1841_);
    crate::leanh::lean_dec_ref(v_x_1839_);
    return v_res_1843_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u64 = 0;
    v___x_1844_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1845_ = lean_uint64_of_nat(v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(
    mut v_x_1846_: *mut crate::leanh::LeanObject,
    mut v_x_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1849_: u64 = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u64 = 0;
    let mut v_hash_1853_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1847_) == 0 {
                    v___x_1852_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0);
                    v___y_1849_ = v___x_1852_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1853_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_1847_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1849_ = v_hash_1853_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1850_ = lean_uint64_to_usize(v___y_1849_);
                v___x_1851_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(v_x_1846_, v___x_1850_, v_x_1847_);
                return v___x_1851_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___boxed(
    mut v_x_1854_: *mut crate::leanh::LeanObject,
    mut v_x_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(v_x_1854_, v_x_1855_);
    crate::leanh::lean_dec(v_x_1855_);
    crate::leanh::lean_dec_ref(v_x_1854_);
    return v_res_1856_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_1857_: *mut crate::leanh::LeanObject,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
    mut v_x_1859_: *mut crate::leanh::LeanObject,
    mut v_x_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1861_ = crate::leanh::lean_ctor_get(v_x_1857_, 0);
                v_vs_1862_ = crate::leanh::lean_ctor_get(v_x_1857_, 1);
                v_isSharedCheck_1886_ = (!crate::leanh::lean_is_exclusive(v_x_1857_)) as u8;
                if v_isSharedCheck_1886_ == 0 {
                    v___x_1864_ = v_x_1857_;
                    v_isShared_1865_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1862_);
                    crate::leanh::lean_inc(v_ks_1861_);
                    crate::leanh::lean_dec(v_x_1857_);
                    v___x_1864_ = crate::leanh::lean_box(0);
                    v_isShared_1865_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1866_ = lean_array_get_size(v_ks_1861_);
                v___x_1867_ = lean_nat_dec_lt(v_x_1858_, v___x_1866_);
                if v___x_1867_ == 0 {
                    crate::leanh::lean_dec(v_x_1858_);
                    v___x_1868_ = lean_array_push(v_ks_1861_, v_x_1859_);
                    v___x_1869_ = lean_array_push(v_vs_1862_, v_x_1860_);
                    if v_isShared_1865_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1869_);
                        crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1868_);
                        v___x_1871_ = v___x_1864_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1868_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1869_);
                        v___x_1871_ = v_reuseFailAlloc_1872_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1873_ = lean_array_fget_borrowed(v_ks_1861_, v_x_1858_);
                    v___x_1874_ = lean_name_eq(v_x_1859_, v_k_x27_1873_);
                    if v___x_1874_ == 0 {
                        if v_isShared_1865_ == 0 {
                            v___x_1876_ = v___x_1864_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1880_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_ks_1861_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_vs_1862_);
                            v___x_1876_ = v_reuseFailAlloc_1880_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1881_ = lean_array_fset(v_ks_1861_, v_x_1858_, v_x_1859_);
                        v___x_1882_ = lean_array_fset(v_vs_1862_, v_x_1858_, v_x_1860_);
                        crate::leanh::lean_dec(v_x_1858_);
                        if v_isShared_1865_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1882_);
                            crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1881_);
                            v___x_1884_ = v___x_1864_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1885_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1881_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1882_);
                            v___x_1884_ = v_reuseFailAlloc_1885_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1871_;
            }
            3 => {
                v___x_1877_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1878_ = lean_nat_add(v_x_1858_, v___x_1877_);
                crate::leanh::lean_dec(v_x_1858_);
                v_x_1857_ = v___x_1876_;
                v_x_1858_ = v___x_1878_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_n_1887_: *mut crate::leanh::LeanObject,
    mut v_k_1888_: *mut crate::leanh::LeanObject,
    mut v_v_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1890_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1891_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1887_, v___x_1890_, v_k_1888_, v_v_1889_);
    return v___x_1891_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1892_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(
    mut v_x_1893_: *mut crate::leanh::LeanObject,
    mut v_x_1894_: usize,
    mut v_x_1895_: usize,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: usize = 0;
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut v_j_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v_v_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut v_node_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1934_: usize = 0;
    let mut v___x_1935_: usize = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_unused_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1953_: u8 = 0;
    let mut v_ks_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1893_) == 0 {
                    v_es_1898_ = crate::leanh::lean_ctor_get(v_x_1893_, 0);
                    v___x_1899_ = 5usize;
                    v___x_1900_ = 1usize;
                    v___x_1901_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1902_ = lean_usize_land(v_x_1894_, v___x_1901_);
                    v_j_1903_ = lean_usize_to_nat(v___x_1902_);
                    v___x_1904_ = lean_array_get_size(v_es_1898_);
                    v___x_1905_ = lean_nat_dec_lt(v_j_1903_, v___x_1904_);
                    if v___x_1905_ == 0 {
                        crate::leanh::lean_dec(v_j_1903_);
                        crate::leanh::lean_dec(v_x_1897_);
                        crate::leanh::lean_dec(v_x_1896_);
                        return v_x_1893_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1898_);
                        v_isSharedCheck_1942_ = (!crate::leanh::lean_is_exclusive(v_x_1893_)) as u8;
                        if v_isSharedCheck_1942_ == 0 {
                            v_unused_1943_ = crate::leanh::lean_ctor_get(v_x_1893_, 0);
                            crate::leanh::lean_dec(v_unused_1943_);
                            v___x_1907_ = v_x_1893_;
                            v_isShared_1908_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1893_);
                            v___x_1907_ = crate::leanh::lean_box(0);
                            v_isShared_1908_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1944_ = crate::leanh::lean_ctor_get(v_x_1893_, 0);
                    v_vs_1945_ = crate::leanh::lean_ctor_get(v_x_1893_, 1);
                    v_isSharedCheck_1965_ = (!crate::leanh::lean_is_exclusive(v_x_1893_)) as u8;
                    if v_isSharedCheck_1965_ == 0 {
                        v___x_1947_ = v_x_1893_;
                        v_isShared_1948_ = v_isSharedCheck_1965_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1945_);
                        crate::leanh::lean_inc(v_ks_1944_);
                        crate::leanh::lean_dec(v_x_1893_);
                        v___x_1947_ = crate::leanh::lean_box(0);
                        v_isShared_1948_ = v_isSharedCheck_1965_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1909_ = lean_array_fget(v_es_1898_, v_j_1903_);
                v___x_1910_ = crate::leanh::lean_box(0);
                v_xs_x27_1911_ = lean_array_fset(v_es_1898_, v_j_1903_, v___x_1910_);
                match crate::leanh::lean_obj_tag(v_v_1909_) {
                    0 => {
                        v_key_1918_ = crate::leanh::lean_ctor_get(v_v_1909_, 0);
                        v_val_1919_ = crate::leanh::lean_ctor_get(v_v_1909_, 1);
                        v_isSharedCheck_1929_ = (!crate::leanh::lean_is_exclusive(v_v_1909_)) as u8;
                        if v_isSharedCheck_1929_ == 0 {
                            v___x_1921_ = v_v_1909_;
                            v_isShared_1922_ = v_isSharedCheck_1929_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1919_);
                            crate::leanh::lean_inc(v_key_1918_);
                            crate::leanh::lean_dec(v_v_1909_);
                            v___x_1921_ = crate::leanh::lean_box(0);
                            v_isShared_1922_ = v_isSharedCheck_1929_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1930_ = crate::leanh::lean_ctor_get(v_v_1909_, 0);
                        v_isSharedCheck_1940_ = (!crate::leanh::lean_is_exclusive(v_v_1909_)) as u8;
                        if v_isSharedCheck_1940_ == 0 {
                            v___x_1932_ = v_v_1909_;
                            v_isShared_1933_ = v_isSharedCheck_1940_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1930_);
                            crate::leanh::lean_dec(v_v_1909_);
                            v___x_1932_ = crate::leanh::lean_box(0);
                            v_isShared_1933_ = v_isSharedCheck_1940_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1941_, 0, v_x_1896_);
                        crate::leanh::lean_ctor_set(v___x_1941_, 1, v_x_1897_);
                        v___y_1913_ = v___x_1941_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1914_ = lean_array_fset(v_xs_x27_1911_, v_j_1903_, v___y_1913_);
                crate::leanh::lean_dec(v_j_1903_);
                if v_isShared_1908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1907_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1916_;
            }
            4 => {
                v___x_1923_ = lean_name_eq(v_x_1896_, v_key_1918_);
                if v___x_1923_ == 0 {
                    crate::leanh::lean_del_object(v___x_1921_);
                    v___x_1924_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1918_,
                        v_val_1919_,
                        v_x_1896_,
                        v_x_1897_,
                    );
                    v___x_1925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
                    v___y_1913_ = v___x_1925_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1919_);
                    crate::leanh::lean_dec(v_key_1918_);
                    if v_isShared_1922_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1921_, 1, v_x_1897_);
                        crate::leanh::lean_ctor_set(v___x_1921_, 0, v_x_1896_);
                        v___x_1927_ = v___x_1921_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_x_1896_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_x_1897_);
                        v___x_1927_ = v_reuseFailAlloc_1928_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1913_ = v___x_1927_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1934_ = lean_usize_shift_right(v_x_1894_, v___x_1899_);
                v___x_1935_ = lean_usize_add(v_x_1895_, v___x_1900_);
                v___x_1936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_node_1930_, v___x_1934_, v___x_1935_, v_x_1896_, v_x_1897_);
                if v_isShared_1933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1932_, 0, v___x_1936_);
                    v___x_1938_ = v___x_1932_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1913_ = v___x_1938_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_ks_1944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_vs_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1964_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1951_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4___redArg(v___x_1950_, v_x_1896_, v_x_1897_);
                v___x_1959_ = 7usize;
                v___x_1960_ = lean_usize_dec_le(v___x_1959_, v_x_1895_);
                if v___x_1960_ == 0 {
                    v___x_1961_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1951_);
                    v___x_1962_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1963_ = lean_nat_dec_lt(v___x_1961_, v___x_1962_);
                    crate::leanh::lean_dec(v___x_1961_);
                    v___y_1953_ = v___x_1963_;
                    state = 10;
                    continue;
                } else {
                    v___y_1953_ = v___x_1960_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1953_ == 0 {
                    v_ks_1954_ = crate::leanh::lean_ctor_get(v_newNode_1951_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1954_);
                    v_vs_1955_ = crate::leanh::lean_ctor_get(v_newNode_1951_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1955_);
                    crate::leanh::lean_dec_ref(v_newNode_1951_);
                    v___x_1956_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___closed__0);
                    v___x_1958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(v_x_1895_, v_ks_1954_, v_vs_1955_, v___x_1956_, v___x_1957_);
                    crate::leanh::lean_dec_ref(v_vs_1955_);
                    crate::leanh::lean_dec_ref(v_ks_1954_);
                    return v___x_1958_;
                } else {
                    return v_newNode_1951_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_depth_1966_: usize,
    mut v_keys_1967_: *mut crate::leanh::LeanObject,
    mut v_vals_1968_: *mut crate::leanh::LeanObject,
    mut v_i_1969_: *mut crate::leanh::LeanObject,
    mut v_entries_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    let mut v_k_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: u64 = 0;
    let mut v_h_1977_: usize = 0;
    let mut v___x_1978_: usize = 0;
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: usize = 0;
    let mut v___x_1981_: usize = 0;
    let mut v___x_1982_: usize = 0;
    let mut v_h_1983_: usize = 0;
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u64 = 0;
    let mut v_hash_1988_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1971_ = lean_array_get_size(v_keys_1967_);
                v___x_1972_ = lean_nat_dec_lt(v_i_1969_, v___x_1971_);
                if v___x_1972_ == 0 {
                    crate::leanh::lean_dec(v_i_1969_);
                    return v_entries_1970_;
                } else {
                    v_k_1973_ = lean_array_fget_borrowed(v_keys_1967_, v_i_1969_);
                    v_v_1974_ = lean_array_fget_borrowed(v_vals_1968_, v_i_1969_);
                    if crate::leanh::lean_obj_tag(v_k_1973_) == 0 {
                        v___x_1987_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0);
                        v___y_1976_ = v___x_1987_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1988_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_1973_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1976_ = v_hash_1988_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_1977_ = lean_uint64_to_usize(v___y_1976_);
                v___x_1978_ = 5usize;
                v___x_1979_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1980_ = 1usize;
                v___x_1981_ = lean_usize_sub(v_depth_1966_, v___x_1980_);
                v___x_1982_ = lean_usize_mul(v___x_1978_, v___x_1981_);
                v_h_1983_ = lean_usize_shift_right(v_h_1977_, v___x_1982_);
                v___x_1984_ = lean_nat_add(v_i_1969_, v___x_1979_);
                crate::leanh::lean_dec(v_i_1969_);
                crate::leanh::lean_inc(v_v_1974_);
                crate::leanh::lean_inc(v_k_1973_);
                v___x_1985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_entries_1970_, v_h_1983_, v_depth_1966_, v_k_1973_, v_v_1974_);
                v_i_1969_ = v___x_1984_;
                v_entries_1970_ = v___x_1985_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_1989_: *mut crate::leanh::LeanObject,
    mut v_keys_1990_: *mut crate::leanh::LeanObject,
    mut v_vals_1991_: *mut crate::leanh::LeanObject,
    mut v_i_1992_: *mut crate::leanh::LeanObject,
    mut v_entries_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1994_: usize = 0;
    let mut v_res_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1994_ = crate::leanh::lean_unbox_usize(v_depth_1989_);
    crate::leanh::lean_dec(v_depth_1989_);
    v_res_1995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1994_, v_keys_1990_, v_vals_1991_, v_i_1992_, v_entries_1993_);
    crate::leanh::lean_dec_ref(v_vals_1991_);
    crate::leanh::lean_dec_ref(v_keys_1990_);
    return v_res_1995_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_1996_: *mut crate::leanh::LeanObject,
    mut v_x_1997_: *mut crate::leanh::LeanObject,
    mut v_x_1998_: *mut crate::leanh::LeanObject,
    mut v_x_1999_: *mut crate::leanh::LeanObject,
    mut v_x_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2577__boxed_2001_: usize = 0;
    let mut v_x_2578__boxed_2002_: usize = 0;
    let mut v_res_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2577__boxed_2001_ = crate::leanh::lean_unbox_usize(v_x_1997_);
    crate::leanh::lean_dec(v_x_1997_);
    v_x_2578__boxed_2002_ = crate::leanh::lean_unbox_usize(v_x_1998_);
    crate::leanh::lean_dec(v_x_1998_);
    v_res_2003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_x_1996_, v_x_2577__boxed_2001_, v_x_2578__boxed_2002_, v_x_1999_, v_x_2000_);
    return v_res_2003_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1___redArg(
    mut v_x_2004_: *mut crate::leanh::LeanObject,
    mut v_x_2005_: *mut crate::leanh::LeanObject,
    mut v_x_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2008_: u64 = 0;
    let mut v___x_2009_: usize = 0;
    let mut v___x_2010_: usize = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u64 = 0;
    let mut v_hash_2013_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2005_) == 0 {
                    v___x_2012_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg___closed__0);
                    v___y_2008_ = v___x_2012_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2013_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2005_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2008_ = v_hash_2013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2009_ = lean_uint64_to_usize(v___y_2008_);
                v___x_2010_ = 1usize;
                v___x_2011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_x_2004_, v___x_2009_, v___x_2010_, v_x_2005_, v_x_2006_);
                return v___x_2011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
    mut v_declName_2014_: *mut crate::leanh::LeanObject,
    mut v_a_2015_: *mut crate::leanh::LeanObject,
    mut v_a_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2048_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2060_: u8 = 0;
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2021_ = lean_st_ref_get(v_a_2015_);
                v_proofInstInfo_2022_ = crate::leanh::lean_ctor_get(v___x_2021_, 2);
                crate::leanh::lean_inc_ref(v_proofInstInfo_2022_);
                crate::leanh::lean_dec(v___x_2021_);
                v___x_2023_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(v_proofInstInfo_2022_, v_declName_2014_);
                crate::leanh::lean_dec_ref(v_proofInstInfo_2022_);
                if crate::leanh::lean_obj_tag(v___x_2023_) == 1 {
                    crate::leanh::lean_dec(v_declName_2014_);
                    v_val_2024_ = crate::leanh::lean_ctor_get(v___x_2023_, 0);
                    v_isSharedCheck_2031_ = (!crate::leanh::lean_is_exclusive(v___x_2023_)) as u8;
                    if v_isSharedCheck_2031_ == 0 {
                        v___x_2026_ = v___x_2023_;
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2024_);
                        crate::leanh::lean_dec(v___x_2023_);
                        v___x_2026_ = crate::leanh::lean_box(0);
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2023_);
                    crate::leanh::lean_inc(v_declName_2014_);
                    v___x_2032_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f(
                        v_declName_2014_,
                        v_a_2016_,
                        v_a_2017_,
                        v_a_2018_,
                        v_a_2019_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2032_) == 0 {
                        v_a_2033_ = crate::leanh::lean_ctor_get(v___x_2032_, 0);
                        v_isSharedCheck_2061_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2032_)) as u8;
                        if v_isSharedCheck_2061_ == 0 {
                            v___x_2035_ = v___x_2032_;
                            v_isShared_2036_ = v_isSharedCheck_2061_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2033_);
                            crate::leanh::lean_dec(v___x_2032_);
                            v___x_2035_ = crate::leanh::lean_box(0);
                            v_isShared_2036_ = v_isSharedCheck_2061_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_2014_);
                        return v___x_2032_;
                    }
                }
            }
            1 => {
                if v_isShared_2027_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2026_, 0);
                    v___x_2029_ = v___x_2026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_val_2024_);
                    v___x_2029_ = v_reuseFailAlloc_2030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2029_;
            }
            3 => {
                v___x_2037_ = lean_st_ref_take(v_a_2015_);
                v_share_2038_ = crate::leanh::lean_ctor_get(v___x_2037_, 0);
                v_maxFVar_2039_ = crate::leanh::lean_ctor_get(v___x_2037_, 1);
                v_proofInstInfo_2040_ = crate::leanh::lean_ctor_get(v___x_2037_, 2);
                v_inferType_2041_ = crate::leanh::lean_ctor_get(v___x_2037_, 3);
                v_getLevel_2042_ = crate::leanh::lean_ctor_get(v___x_2037_, 4);
                v_congrInfo_2043_ = crate::leanh::lean_ctor_get(v___x_2037_, 5);
                v_defEqI_2044_ = crate::leanh::lean_ctor_get(v___x_2037_, 6);
                v_extensions_2045_ = crate::leanh::lean_ctor_get(v___x_2037_, 7);
                v_issues_2046_ = crate::leanh::lean_ctor_get(v___x_2037_, 8);
                v_canon_2047_ = crate::leanh::lean_ctor_get(v___x_2037_, 9);
                v_debug_2048_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2037_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2060_ = (!crate::leanh::lean_is_exclusive(v___x_2037_)) as u8;
                if v_isSharedCheck_2060_ == 0 {
                    v___x_2050_ = v___x_2037_;
                    v_isShared_2051_ = v_isSharedCheck_2060_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_2047_);
                    crate::leanh::lean_inc(v_issues_2046_);
                    crate::leanh::lean_inc(v_extensions_2045_);
                    crate::leanh::lean_inc(v_defEqI_2044_);
                    crate::leanh::lean_inc(v_congrInfo_2043_);
                    crate::leanh::lean_inc(v_getLevel_2042_);
                    crate::leanh::lean_inc(v_inferType_2041_);
                    crate::leanh::lean_inc(v_proofInstInfo_2040_);
                    crate::leanh::lean_inc(v_maxFVar_2039_);
                    crate::leanh::lean_inc(v_share_2038_);
                    crate::leanh::lean_dec(v___x_2037_);
                    v___x_2050_ = crate::leanh::lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_2033_);
                v___x_2052_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1___redArg(v_proofInstInfo_2040_, v_declName_2014_, v_a_2033_);
                if v_isShared_2051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2050_, 2, v___x_2052_);
                    v___x_2054_ = v___x_2050_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2059_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_share_2038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_maxFVar_2039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 2, v___x_2052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_inferType_2041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_getLevel_2042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 5, v_congrInfo_2043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 6, v_defEqI_2044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 7, v_extensions_2045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 8, v_issues_2046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 9, v_canon_2047_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2059_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_2048_,
                    );
                    v___x_2054_ = v_reuseFailAlloc_2059_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2055_ = lean_st_ref_set(v_a_2015_, v___x_2054_);
                if v_isShared_2036_ == 0 {
                    v___x_2057_ = v___x_2035_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2033_);
                    v___x_2057_ = v_reuseFailAlloc_2058_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg___boxed(
    mut v_declName_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
        v_declName_2062_,
        v_a_2063_,
        v_a_2064_,
        v_a_2065_,
        v_a_2066_,
        v_a_2067_,
    );
    crate::leanh::lean_dec(v_a_2067_);
    crate::leanh::lean_dec_ref(v_a_2066_);
    crate::leanh::lean_dec(v_a_2065_);
    crate::leanh::lean_dec_ref(v_a_2064_);
    crate::leanh::lean_dec(v_a_2063_);
    return v_res_2069_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f(
    mut v_declName_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2078_ = l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
        v_declName_2070_,
        v_a_2072_,
        v_a_2073_,
        v_a_2074_,
        v_a_2075_,
        v_a_2076_,
    );
    return v___x_2078_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfo_x3f___boxed(
    mut v_declName_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_Lean_Meta_Sym_getProofInstInfo_x3f(
        v_declName_2079_,
        v_a_2080_,
        v_a_2081_,
        v_a_2082_,
        v_a_2083_,
        v_a_2084_,
        v_a_2085_,
    );
    crate::leanh::lean_dec(v_a_2085_);
    crate::leanh::lean_dec_ref(v_a_2084_);
    crate::leanh::lean_dec(v_a_2083_);
    crate::leanh::lean_dec_ref(v_a_2082_);
    crate::leanh::lean_dec(v_a_2081_);
    crate::leanh::lean_dec_ref(v_a_2080_);
    return v_res_2087_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0(
    mut v_00_u03b2_2088_: *mut crate::leanh::LeanObject,
    mut v_x_2089_: *mut crate::leanh::LeanObject,
    mut v_x_2090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2091_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___redArg(v_x_2089_, v_x_2090_);
    return v___x_2091_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0___boxed(
    mut v_00_u03b2_2092_: *mut crate::leanh::LeanObject,
    mut v_x_2093_: *mut crate::leanh::LeanObject,
    mut v_x_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2095_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0(
            v_00_u03b2_2092_,
            v_x_2093_,
            v_x_2094_,
        );
    crate::leanh::lean_dec(v_x_2094_);
    crate::leanh::lean_dec_ref(v_x_2093_);
    return v_res_2095_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1(
    mut v_00_u03b2_2096_: *mut crate::leanh::LeanObject,
    mut v_x_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
    mut v_x_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2100_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1___redArg(v_x_2097_, v_x_2098_, v_x_2099_);
    return v___x_2100_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0(
    mut v_00_u03b2_2101_: *mut crate::leanh::LeanObject,
    mut v_x_2102_: *mut crate::leanh::LeanObject,
    mut v_x_2103_: usize,
    mut v_x_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___redArg(v_x_2102_, v_x_2103_, v_x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
    mut v_x_2108_: *mut crate::leanh::LeanObject,
    mut v_x_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2839__boxed_2110_: usize = 0;
    let mut v_res_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2839__boxed_2110_ = crate::leanh::lean_unbox_usize(v_x_2108_);
    crate::leanh::lean_dec(v_x_2108_);
    v_res_2111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0(v_00_u03b2_2106_, v_x_2107_, v_x_2839__boxed_2110_, v_x_2109_);
    crate::leanh::lean_dec(v_x_2109_);
    crate::leanh::lean_dec_ref(v_x_2107_);
    return v_res_2111_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2(
    mut v_00_u03b2_2112_: *mut crate::leanh::LeanObject,
    mut v_x_2113_: *mut crate::leanh::LeanObject,
    mut v_x_2114_: usize,
    mut v_x_2115_: usize,
    mut v_x_2116_: *mut crate::leanh::LeanObject,
    mut v_x_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___redArg(v_x_2113_, v_x_2114_, v_x_2115_, v_x_2116_, v_x_2117_);
    return v___x_2118_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_2119_: *mut crate::leanh::LeanObject,
    mut v_x_2120_: *mut crate::leanh::LeanObject,
    mut v_x_2121_: *mut crate::leanh::LeanObject,
    mut v_x_2122_: *mut crate::leanh::LeanObject,
    mut v_x_2123_: *mut crate::leanh::LeanObject,
    mut v_x_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2850__boxed_2125_: usize = 0;
    let mut v_x_2851__boxed_2126_: usize = 0;
    let mut v_res_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2850__boxed_2125_ = crate::leanh::lean_unbox_usize(v_x_2121_);
    crate::leanh::lean_dec(v_x_2121_);
    v_x_2851__boxed_2126_ = crate::leanh::lean_unbox_usize(v_x_2122_);
    crate::leanh::lean_dec(v_x_2122_);
    v_res_2127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2(v_00_u03b2_2119_, v_x_2120_, v_x_2850__boxed_2125_, v_x_2851__boxed_2126_, v_x_2123_, v_x_2124_);
    return v_res_2127_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2128_: *mut crate::leanh::LeanObject,
    mut v_keys_2129_: *mut crate::leanh::LeanObject,
    mut v_vals_2130_: *mut crate::leanh::LeanObject,
    mut v_heq_2131_: *mut crate::leanh::LeanObject,
    mut v_i_2132_: *mut crate::leanh::LeanObject,
    mut v_k_2133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2129_, v_vals_2130_, v_i_2132_, v_k_2133_);
    return v___x_2134_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2135_: *mut crate::leanh::LeanObject,
    mut v_keys_2136_: *mut crate::leanh::LeanObject,
    mut v_vals_2137_: *mut crate::leanh::LeanObject,
    mut v_heq_2138_: *mut crate::leanh::LeanObject,
    mut v_i_2139_: *mut crate::leanh::LeanObject,
    mut v_k_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2135_, v_keys_2136_, v_vals_2137_, v_heq_2138_, v_i_2139_, v_k_2140_);
    crate::leanh::lean_dec(v_k_2140_);
    crate::leanh::lean_dec_ref(v_vals_2137_);
    crate::leanh::lean_dec_ref(v_keys_2136_);
    return v_res_2141_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2142_: *mut crate::leanh::LeanObject,
    mut v_n_2143_: *mut crate::leanh::LeanObject,
    mut v_k_2144_: *mut crate::leanh::LeanObject,
    mut v_v_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4___redArg(v_n_2143_, v_k_2144_, v_v_2145_);
    return v___x_2146_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2147_: *mut crate::leanh::LeanObject,
    mut v_depth_2148_: usize,
    mut v_keys_2149_: *mut crate::leanh::LeanObject,
    mut v_vals_2150_: *mut crate::leanh::LeanObject,
    mut v_heq_2151_: *mut crate::leanh::LeanObject,
    mut v_i_2152_: *mut crate::leanh::LeanObject,
    mut v_entries_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___redArg(v_depth_2148_, v_keys_2149_, v_vals_2150_, v_i_2152_, v_entries_2153_);
    return v___x_2154_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2155_: *mut crate::leanh::LeanObject,
    mut v_depth_2156_: *mut crate::leanh::LeanObject,
    mut v_keys_2157_: *mut crate::leanh::LeanObject,
    mut v_vals_2158_: *mut crate::leanh::LeanObject,
    mut v_heq_2159_: *mut crate::leanh::LeanObject,
    mut v_i_2160_: *mut crate::leanh::LeanObject,
    mut v_entries_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2162_: usize = 0;
    let mut v_res_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2162_ = crate::leanh::lean_unbox_usize(v_depth_2156_);
    crate::leanh::lean_dec(v_depth_2156_);
    v_res_2163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__5(v_00_u03b2_2155_, v_depth_boxed_2162_, v_keys_2157_, v_vals_2158_, v_heq_2159_, v_i_2160_, v_entries_2161_);
    crate::leanh::lean_dec_ref(v_vals_2158_);
    crate::leanh::lean_dec_ref(v_keys_2157_);
    return v_res_2163_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2164_: *mut crate::leanh::LeanObject,
    mut v_x_2165_: *mut crate::leanh::LeanObject,
    mut v_x_2166_: *mut crate::leanh::LeanObject,
    mut v_x_2167_: *mut crate::leanh::LeanObject,
    mut v_x_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2169_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getProofInstInfo_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2165_, v_x_2166_, v_x_2167_, v_x_2168_);
    return v___x_2169_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(
    mut v_e_2170_: *mut crate::leanh::LeanObject,
    mut v_a_2171_: *mut crate::leanh::LeanObject,
    mut v_a_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
    mut v_a_2174_: *mut crate::leanh::LeanObject,
    mut v_a_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_2170_) == 4 {
        let mut v_declName_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_2177_ = crate::leanh::lean_ctor_get(v_e_2170_, 0);
        crate::leanh::lean_inc(v_declName_2177_);
        crate::leanh::lean_dec_ref_known(v_e_2170_, 2);
        v___x_2178_ = l_Lean_Meta_Sym_getProofInstInfo_x3f___redArg(
            v_declName_2177_,
            v_a_2171_,
            v_a_2172_,
            v_a_2173_,
            v_a_2174_,
            v_a_2175_,
        );
        return v___x_2178_;
    } else {
        let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_2170_);
        v___x_2179_ = crate::leanh::lean_box(0);
        v___x_2180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2179_);
        return v___x_2180_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg___boxed(
    mut v_e_2181_: *mut crate::leanh::LeanObject,
    mut v_a_2182_: *mut crate::leanh::LeanObject,
    mut v_a_2183_: *mut crate::leanh::LeanObject,
    mut v_a_2184_: *mut crate::leanh::LeanObject,
    mut v_a_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
    mut v_a_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(
        v_e_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_,
    );
    crate::leanh::lean_dec(v_a_2186_);
    crate::leanh::lean_dec_ref(v_a_2185_);
    crate::leanh::lean_dec(v_a_2184_);
    crate::leanh::lean_dec_ref(v_a_2183_);
    crate::leanh::lean_dec(v_a_2182_);
    return v_res_2188_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f(
    mut v_e_2189_: *mut crate::leanh::LeanObject,
    mut v_a_2190_: *mut crate::leanh::LeanObject,
    mut v_a_2191_: *mut crate::leanh::LeanObject,
    mut v_a_2192_: *mut crate::leanh::LeanObject,
    mut v_a_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
    mut v_a_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(
        v_e_2189_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_,
    );
    return v___x_2197_;
}
pub unsafe fn l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___boxed(
    mut v_e_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_a_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
    mut v_a_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f(
        v_e_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_,
    );
    crate::leanh::lean_dec(v_a_2204_);
    crate::leanh::lean_dec_ref(v_a_2203_);
    crate::leanh::lean_dec(v_a_2202_);
    crate::leanh::lean_dec_ref(v_a_2201_);
    crate::leanh::lean_dec(v_a_2200_);
    crate::leanh::lean_dec_ref(v_a_2199_);
    return v_res_2206_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_ProofInstInfo(
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
    res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_ProofInstInfo(
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
pub unsafe fn initialize_Lean_Meta_Sym_ProofInstInfo(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Meta_Sym_IsClass(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
}

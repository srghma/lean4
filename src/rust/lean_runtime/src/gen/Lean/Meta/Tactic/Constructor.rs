// Lean compiler output
// Module: Lean.Meta.Tactic.Constructor
// Imports: Lean.Meta.Tactic.Apply
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_replaceRef};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_sort___override, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_forallMetaTelescopeReducing,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_checkApp;
use crate::r#gen::Lean::Meta::Tactic::Apply::{
    initialize_Lean_Meta_Tactic_Apply, l_Lean_MVarId_apply,
    runtime_initialize_Lean_Meta_Tactic_Apply,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getType_x27, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_MVarId_constructor___lam__0___closed__0_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105,
            110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_MVarId_constructor___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_constructor___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_constructor___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_constructor___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_constructor___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_constructor___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_MVarId_constructor___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_constructor___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_constructor___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_constructor___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_constructor___lam__0___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_constructor___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_constructor___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_MVarId_constructor___lam__0___closed__5_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            110, 111, 32, 97, 112, 112, 108, 105, 99, 97, 98, 108, 101, 32, 99, 111, 110, 115, 116,
            114, 117, 99, 116, 111, 114, 32, 102, 111, 117, 110, 100, 0,
        ],
    };
static mut l_Lean_MVarId_constructor___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_constructor___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_MVarId_constructor___lam__0___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_constructor___lam__0___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_constructor___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_constructor___lam__0___closed__6_value) as *mut LeanObject;
static mut l_Lean_MVarId_constructor___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_constructor___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_constructor___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_constructor___lam__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_constructor___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0],
};
static mut l_Lean_MVarId_constructor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_constructor___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_constructor___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_constructor___closed__0_value) as *mut LeanObject,
        9638999676518745041 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_constructor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_constructor___closed__1_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_existsIntro___lam__0___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32,
            111, 102, 32, 115, 117, 98, 103, 111, 97, 108, 115, 0,
        ],
    };
static mut l_Lean_MVarId_existsIntro___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_existsIntro___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_existsIntro___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_MVarId_existsIntro___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_existsIntro___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_existsIntro___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_existsIntro___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_existsIntro___lam__0___closed__4_value: LeanStringObject<57> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 57,
        m_capacity: 57,
        m_length: 56,
        m_data: [
            116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105,
            110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 32,
            119, 105, 116, 104, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
            111, 114, 0,
        ],
    };
static mut l_Lean_MVarId_existsIntro___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_MVarId_existsIntro___lam__0___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_existsIntro___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__5_value) as *mut LeanObject;
static mut l_Lean_MVarId_existsIntro___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_existsIntro___lam__0___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_existsIntro___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_existsIntro___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_existsIntro___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_existsIntro___lam__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_existsIntro___lam__0___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [16777472 as *mut LeanObject],
    };
static mut l_Lean_MVarId_existsIntro___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__9_value) as *mut LeanObject;
pub static l_Lean_MVarId_existsIntro___lam__0___closed__10_value: LeanStringObject<42> =
    LeanStringObject {
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
            99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 109, 117, 115, 116, 32, 104,
            97, 118, 101, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 116, 119, 111, 32, 102, 105,
            101, 108, 100, 115, 0,
        ],
    };
static mut l_Lean_MVarId_existsIntro___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__10_value) as *mut LeanObject;
pub static l_Lean_MVarId_existsIntro___lam__0___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_existsIntro___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___lam__0___closed__11_value) as *mut LeanObject;
static mut l_Lean_MVarId_existsIntro___lam__0___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_existsIntro___lam__0___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_existsIntro___lam__0___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_existsIntro___lam__0___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_existsIntro___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 120, 105, 115, 116, 115, 0],
};
static mut l_Lean_MVarId_existsIntro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_existsIntro___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_existsIntro___closed__0_value) as *mut LeanObject,
        9471123498885785066 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_existsIntro___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_existsIntro___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1___redArg(
    mut v_mvarId_868_: *mut LeanObject,
    mut v_x_869_: *mut LeanObject,
    mut v___y_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_879_: u8 = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_883_: u8 = 0;
    let mut v_a_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_875_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_868_,
                    v_x_869_,
                    v___y_870_,
                    v___y_871_,
                    v___y_872_,
                    v___y_873_,
                );
                if lean_obj_tag(v___x_875_) == 0 {
                    v_a_876_ = lean_ctor_get(v___x_875_, 0);
                    v_isSharedCheck_883_ = (!lean_is_exclusive(v___x_875_)) as u8;
                    if v_isSharedCheck_883_ == 0 {
                        v___x_878_ = v___x_875_;
                        v_isShared_879_ = v_isSharedCheck_883_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_876_);
                        lean_dec(v___x_875_);
                        v___x_878_ = lean_box(0);
                        v_isShared_879_ = v_isSharedCheck_883_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_884_ = lean_ctor_get(v___x_875_, 0);
                    v_isSharedCheck_891_ = (!lean_is_exclusive(v___x_875_)) as u8;
                    if v_isSharedCheck_891_ == 0 {
                        v___x_886_ = v___x_875_;
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_884_);
                        lean_dec(v___x_875_);
                        v___x_886_ = lean_box(0);
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_879_ == 0 {
                    v___x_881_ = v___x_878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
                    v___x_881_ = v_reuseFailAlloc_882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_881_;
            }
            3 => {
                if v_isShared_887_ == 0 {
                    v___x_889_ = v___x_886_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1___redArg___boxed(
    mut v_mvarId_892_: *mut LeanObject,
    mut v_x_893_: *mut LeanObject,
    mut v___y_894_: *mut LeanObject,
    mut v___y_895_: *mut LeanObject,
    mut v___y_896_: *mut LeanObject,
    mut v___y_897_: *mut LeanObject,
    mut v___y_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_899_: *mut LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1___redArg(
        v_mvarId_892_,
        v_x_893_,
        v___y_894_,
        v___y_895_,
        v___y_896_,
        v___y_897_,
    );
    lean_dec(v___y_897_);
    lean_dec_ref(v___y_896_);
    lean_dec(v___y_895_);
    lean_dec_ref(v___y_894_);
    return v_res_899_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1(
    mut v_00_u03b1_900_: *mut LeanObject,
    mut v_mvarId_901_: *mut LeanObject,
    mut v_x_902_: *mut LeanObject,
    mut v___y_903_: *mut LeanObject,
    mut v___y_904_: *mut LeanObject,
    mut v___y_905_: *mut LeanObject,
    mut v___y_906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    v___x_908_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1___redArg(
        v_mvarId_901_,
        v_x_902_,
        v___y_903_,
        v___y_904_,
        v___y_905_,
        v___y_906_,
    );
    return v___x_908_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1___boxed(
    mut v_00_u03b1_909_: *mut LeanObject,
    mut v_mvarId_910_: *mut LeanObject,
    mut v_x_911_: *mut LeanObject,
    mut v___y_912_: *mut LeanObject,
    mut v___y_913_: *mut LeanObject,
    mut v___y_914_: *mut LeanObject,
    mut v___y_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_917_: *mut LeanObject = core::ptr::null_mut();
    v_res_917_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1(
        v_00_u03b1_909_,
        v_mvarId_910_,
        v_x_911_,
        v___y_912_,
        v___y_913_,
        v___y_914_,
        v___y_915_,
    );
    lean_dec(v___y_915_);
    lean_dec_ref(v___y_914_);
    lean_dec(v___y_913_);
    lean_dec_ref(v___y_912_);
    return v_res_917_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg(
    mut v_us_921_: *mut LeanObject,
    mut v_mvarId_922_: *mut LeanObject,
    mut v_cfg_923_: *mut LeanObject,
    mut v_as_x27_924_: *mut LeanObject,
    mut v_b_925_: *mut LeanObject,
    mut v___y_926_: *mut LeanObject,
    mut v___y_927_: *mut LeanObject,
    mut v___y_928_: *mut LeanObject,
    mut v___y_929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_941_: u8 = 0;
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_947_: u8 = 0;
    let mut v_a_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_951_: u8 = 0;
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_954_: u8 = 0;
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: u8 = 0;
    let mut v_isSharedCheck_961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_924_) == 0 {
                    lean_dec_ref(v_cfg_923_);
                    lean_dec(v_mvarId_922_);
                    lean_dec(v_us_921_);
                    v___x_931_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_931_, 0, v_b_925_);
                    return v___x_931_;
                } else {
                    lean_dec_ref(v_b_925_);
                    v_head_932_ = lean_ctor_get(v_as_x27_924_, 0);
                    v_tail_933_ = lean_ctor_get(v_as_x27_924_, 1);
                    v___x_934_ = lean_box(0);
                    lean_inc(v_us_921_);
                    lean_inc(v_head_932_);
                    v___x_935_ = l_Lean_mkConst(v_head_932_, v_us_921_);
                    v___x_936_ = lean_box(0);
                    lean_inc_ref(v_cfg_923_);
                    lean_inc(v_mvarId_922_);
                    v___x_937_ = l_Lean_MVarId_apply(
                        v_mvarId_922_,
                        v___x_935_,
                        v_cfg_923_,
                        v___x_936_,
                        v___y_926_,
                        v___y_927_,
                        v___y_928_,
                        v___y_929_,
                    );
                    if lean_obj_tag(v___x_937_) == 0 {
                        lean_dec_ref(v_cfg_923_);
                        lean_dec(v_mvarId_922_);
                        lean_dec(v_us_921_);
                        v_a_938_ = lean_ctor_get(v___x_937_, 0);
                        v_isSharedCheck_947_ = (!lean_is_exclusive(v___x_937_)) as u8;
                        if v_isSharedCheck_947_ == 0 {
                            v___x_940_ = v___x_937_;
                            v_isShared_941_ = v_isSharedCheck_947_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_938_);
                            lean_dec(v___x_937_);
                            v___x_940_ = lean_box(0);
                            v_isShared_941_ = v_isSharedCheck_947_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_948_ = lean_ctor_get(v___x_937_, 0);
                        v_isSharedCheck_961_ = (!lean_is_exclusive(v___x_937_)) as u8;
                        if v_isSharedCheck_961_ == 0 {
                            v___x_950_ = v___x_937_;
                            v_isShared_951_ = v_isSharedCheck_961_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_948_);
                            lean_dec(v___x_937_);
                            v___x_950_ = lean_box(0);
                            v_isShared_951_ = v_isSharedCheck_961_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_942_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_942_, 0, v_a_938_);
                v___x_943_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_943_, 0, v___x_942_);
                lean_ctor_set(v___x_943_, 1, v___x_934_);
                if v_isShared_941_ == 0 {
                    lean_ctor_set(v___x_940_, 0, v___x_943_);
                    v___x_945_ = v___x_940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
                    v___x_945_ = v_reuseFailAlloc_946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_945_;
            }
            3 => {
                v___x_952_ = l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg___closed__0;
                v___x_959_ = l_Lean_Exception_isInterrupt(v_a_948_);
                if v___x_959_ == 0 {
                    lean_inc(v_a_948_);
                    v___x_960_ = l_Lean_Exception_isRuntime(v_a_948_);
                    v___y_954_ = v___x_960_;
                    state = 4;
                    continue;
                } else {
                    v___y_954_ = v___x_959_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_954_ == 0 {
                    lean_del_object(v___x_950_);
                    lean_dec(v_a_948_);
                    v_as_x27_924_ = v_tail_933_;
                    v_b_925_ = v___x_952_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_cfg_923_);
                    lean_dec(v_mvarId_922_);
                    lean_dec(v_us_921_);
                    if v_isShared_951_ == 0 {
                        v___x_957_ = v___x_950_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_948_);
                        v___x_957_ = v_reuseFailAlloc_958_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg___boxed(
    mut v_us_962_: *mut LeanObject,
    mut v_mvarId_963_: *mut LeanObject,
    mut v_cfg_964_: *mut LeanObject,
    mut v_as_x27_965_: *mut LeanObject,
    mut v_b_966_: *mut LeanObject,
    mut v___y_967_: *mut LeanObject,
    mut v___y_968_: *mut LeanObject,
    mut v___y_969_: *mut LeanObject,
    mut v___y_970_: *mut LeanObject,
    mut v___y_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_972_: *mut LeanObject = core::ptr::null_mut();
    v_res_972_ = l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg(
        v_us_962_,
        v_mvarId_963_,
        v_cfg_964_,
        v_as_x27_965_,
        v_b_966_,
        v___y_967_,
        v___y_968_,
        v___y_969_,
        v___y_970_,
    );
    lean_dec(v___y_970_);
    lean_dec_ref(v___y_969_);
    lean_dec(v___y_968_);
    lean_dec_ref(v___y_967_);
    lean_dec(v_as_x27_965_);
    return v_res_972_;
}
pub unsafe fn _init_l_Lean_MVarId_constructor___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Lean_MVarId_constructor___lam__0___closed__1;
    v___x_977_ = l_Lean_MessageData_ofFormat(v___x_976_);
    return v___x_977_;
}
pub unsafe fn _init_l_Lean_MVarId_constructor___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    v___x_978_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_constructor___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_constructor___lam__0___closed__2_once),
        _init_l_Lean_MVarId_constructor___lam__0___closed__2,
    );
    v___x_979_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_979_, 0, v___x_978_);
    return v___x_979_;
}
pub unsafe fn _init_l_Lean_MVarId_constructor___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v___x_986_ = l_Lean_MVarId_constructor___lam__0___closed__6;
    v___x_987_ = l_Lean_MessageData_ofFormat(v___x_986_);
    return v___x_987_;
}
pub unsafe fn _init_l_Lean_MVarId_constructor___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    v___x_988_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_constructor___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_MVarId_constructor___lam__0___closed__7_once),
        _init_l_Lean_MVarId_constructor___lam__0___closed__7,
    );
    v___x_989_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_989_, 0, v___x_988_);
    return v___x_989_;
}
pub unsafe fn l_Lean_MVarId_constructor___lam__0(
    mut v_mvarId_990_: *mut LeanObject,
    mut v___x_991_: *mut LeanObject,
    mut v_cfg_992_: *mut LeanObject,
    mut v___y_993_: *mut LeanObject,
    mut v___y_994_: *mut LeanObject,
    mut v___y_995_: *mut LeanObject,
    mut v___y_996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u8 = 0;
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1023_: u8 = 0;
    let mut v_fst_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut v_a_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1035_: u8 = 0;
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1039_: u8 = 0;
    let mut v_a_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1047_: u8 = 0;
    let mut v_a_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_991_);
                lean_inc(v_mvarId_990_);
                v___x_1005_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_990_,
                    v___x_991_,
                    v___y_993_,
                    v___y_994_,
                    v___y_995_,
                    v___y_996_,
                );
                if lean_obj_tag(v___x_1005_) == 0 {
                    lean_dec_ref_known(v___x_1005_, 1);
                    lean_inc(v_mvarId_990_);
                    v___x_1006_ = l_Lean_MVarId_getType_x27(
                        v_mvarId_990_,
                        v___y_993_,
                        v___y_994_,
                        v___y_995_,
                        v___y_996_,
                    );
                    if lean_obj_tag(v___x_1006_) == 0 {
                        v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
                        lean_inc(v_a_1007_);
                        lean_dec_ref_known(v___x_1006_, 1);
                        v___x_1008_ = l_Lean_Expr_getAppFn(v_a_1007_);
                        lean_dec(v_a_1007_);
                        if lean_obj_tag(v___x_1008_) == 4 {
                            v_declName_1009_ = lean_ctor_get(v___x_1008_, 0);
                            lean_inc(v_declName_1009_);
                            v_us_1010_ = lean_ctor_get(v___x_1008_, 1);
                            lean_inc(v_us_1010_);
                            lean_dec_ref_known(v___x_1008_, 2);
                            v___x_1011_ = lean_st_ref_get(v___y_996_);
                            v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
                            lean_inc_ref(v_env_1012_);
                            lean_dec(v___x_1011_);
                            v___x_1013_ = 0;
                            v___x_1014_ = l_Lean_Environment_find_x3f(
                                v_env_1012_,
                                v_declName_1009_,
                                v___x_1013_,
                            );
                            if lean_obj_tag(v___x_1014_) == 0 {
                                lean_dec(v_us_1010_);
                                lean_dec_ref(v_cfg_992_);
                                v___y_999_ = v___y_993_;
                                v___y_1000_ = v___y_994_;
                                v___y_1001_ = v___y_995_;
                                v___y_1002_ = v___y_996_;
                                state = 1;
                                continue;
                            } else {
                                v_val_1015_ = lean_ctor_get(v___x_1014_, 0);
                                lean_inc(v_val_1015_);
                                lean_dec_ref_known(v___x_1014_, 1);
                                if lean_obj_tag(v_val_1015_) == 5 {
                                    v_val_1016_ = lean_ctor_get(v_val_1015_, 0);
                                    lean_inc_ref(v_val_1016_);
                                    lean_dec_ref_known(v_val_1015_, 1);
                                    v_ctors_1017_ = lean_ctor_get(v_val_1016_, 4);
                                    lean_inc(v_ctors_1017_);
                                    lean_dec_ref(v_val_1016_);
                                    v___x_1018_ = l_Lean_MVarId_constructor___lam__0___closed__4;
                                    lean_inc(v_mvarId_990_);
                                    v___x_1019_ = l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg(v_us_1010_, v_mvarId_990_, v_cfg_992_, v_ctors_1017_, v___x_1018_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
                                    lean_dec(v_ctors_1017_);
                                    if lean_obj_tag(v___x_1019_) == 0 {
                                        v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
                                        v_isSharedCheck_1031_ =
                                            (!lean_is_exclusive(v___x_1019_)) as u8;
                                        if v_isSharedCheck_1031_ == 0 {
                                            v___x_1022_ = v___x_1019_;
                                            v_isShared_1023_ = v_isSharedCheck_1031_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1020_);
                                            lean_dec(v___x_1019_);
                                            v___x_1022_ = lean_box(0);
                                            v_isShared_1023_ = v_isSharedCheck_1031_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_991_);
                                        lean_dec(v_mvarId_990_);
                                        v_a_1032_ = lean_ctor_get(v___x_1019_, 0);
                                        v_isSharedCheck_1039_ =
                                            (!lean_is_exclusive(v___x_1019_)) as u8;
                                        if v_isSharedCheck_1039_ == 0 {
                                            v___x_1034_ = v___x_1019_;
                                            v_isShared_1035_ = v_isSharedCheck_1039_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1032_);
                                            lean_dec(v___x_1019_);
                                            v___x_1034_ = lean_box(0);
                                            v_isShared_1035_ = v_isSharedCheck_1039_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_val_1015_);
                                    lean_dec(v_us_1010_);
                                    lean_dec_ref(v_cfg_992_);
                                    v___y_999_ = v___y_993_;
                                    v___y_1000_ = v___y_994_;
                                    v___y_1001_ = v___y_995_;
                                    v___y_1002_ = v___y_996_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1008_);
                            lean_dec_ref(v_cfg_992_);
                            v___y_999_ = v___y_993_;
                            v___y_1000_ = v___y_994_;
                            v___y_1001_ = v___y_995_;
                            v___y_1002_ = v___y_996_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_cfg_992_);
                        lean_dec(v___x_991_);
                        lean_dec(v_mvarId_990_);
                        v_a_1040_ = lean_ctor_get(v___x_1006_, 0);
                        v_isSharedCheck_1047_ = (!lean_is_exclusive(v___x_1006_)) as u8;
                        if v_isSharedCheck_1047_ == 0 {
                            v___x_1042_ = v___x_1006_;
                            v_isShared_1043_ = v_isSharedCheck_1047_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1040_);
                            lean_dec(v___x_1006_);
                            v___x_1042_ = lean_box(0);
                            v_isShared_1043_ = v_isSharedCheck_1047_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_cfg_992_);
                    lean_dec(v___x_991_);
                    lean_dec(v_mvarId_990_);
                    v_a_1048_ = lean_ctor_get(v___x_1005_, 0);
                    v_isSharedCheck_1055_ = (!lean_is_exclusive(v___x_1005_)) as u8;
                    if v_isSharedCheck_1055_ == 0 {
                        v___x_1050_ = v___x_1005_;
                        v_isShared_1051_ = v_isSharedCheck_1055_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1048_);
                        lean_dec(v___x_1005_);
                        v___x_1050_ = lean_box(0);
                        v_isShared_1051_ = v_isSharedCheck_1055_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1003_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_constructor___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_constructor___lam__0___closed__3_once),
                    _init_l_Lean_MVarId_constructor___lam__0___closed__3,
                );
                v___x_1004_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_991_,
                    v_mvarId_990_,
                    v___x_1003_,
                    v___y_999_,
                    v___y_1000_,
                    v___y_1001_,
                    v___y_1002_,
                );
                return v___x_1004_;
            }
            2 => {
                v_fst_1024_ = lean_ctor_get(v_a_1020_, 0);
                lean_inc(v_fst_1024_);
                lean_dec(v_a_1020_);
                if lean_obj_tag(v_fst_1024_) == 0 {
                    lean_del_object(v___x_1022_);
                    v___x_1025_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_constructor___lam__0___closed__8),
                        core::ptr::addr_of_mut!(
                            l_Lean_MVarId_constructor___lam__0___closed__8_once
                        ),
                        _init_l_Lean_MVarId_constructor___lam__0___closed__8,
                    );
                    v___x_1026_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_991_,
                        v_mvarId_990_,
                        v___x_1025_,
                        v___y_993_,
                        v___y_994_,
                        v___y_995_,
                        v___y_996_,
                    );
                    return v___x_1026_;
                } else {
                    lean_dec(v___x_991_);
                    lean_dec(v_mvarId_990_);
                    v_val_1027_ = lean_ctor_get(v_fst_1024_, 0);
                    lean_inc(v_val_1027_);
                    lean_dec_ref_known(v_fst_1024_, 1);
                    if v_isShared_1023_ == 0 {
                        lean_ctor_set(v___x_1022_, 0, v_val_1027_);
                        v___x_1029_ = v___x_1022_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_val_1027_);
                        v___x_1029_ = v_reuseFailAlloc_1030_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1029_;
            }
            4 => {
                if v_isShared_1035_ == 0 {
                    v___x_1037_ = v___x_1034_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
                    v___x_1037_ = v_reuseFailAlloc_1038_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1037_;
            }
            6 => {
                if v_isShared_1043_ == 0 {
                    v___x_1045_ = v___x_1042_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
                    v___x_1045_ = v_reuseFailAlloc_1046_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1045_;
            }
            8 => {
                if v_isShared_1051_ == 0 {
                    v___x_1053_ = v___x_1050_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
                    v___x_1053_ = v_reuseFailAlloc_1054_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_constructor___lam__0___boxed(
    mut v_mvarId_1056_: *mut LeanObject,
    mut v___x_1057_: *mut LeanObject,
    mut v_cfg_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
    mut v___y_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lean_MVarId_constructor___lam__0(
        v_mvarId_1056_,
        v___x_1057_,
        v_cfg_1058_,
        v___y_1059_,
        v___y_1060_,
        v___y_1061_,
        v___y_1062_,
    );
    lean_dec(v___y_1062_);
    lean_dec_ref(v___y_1061_);
    lean_dec(v___y_1060_);
    lean_dec_ref(v___y_1059_);
    return v_res_1064_;
}
pub unsafe fn l_Lean_MVarId_constructor(
    mut v_mvarId_1068_: *mut LeanObject,
    mut v_cfg_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    v___x_1075_ = l_Lean_MVarId_constructor___closed__1;
    lean_inc(v_mvarId_1068_);
    v___f_1076_ = lean_alloc_closure(
        l_Lean_MVarId_constructor___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_1076_, 0, v_mvarId_1068_);
    lean_closure_set(v___f_1076_, 1, v___x_1075_);
    lean_closure_set(v___f_1076_, 2, v_cfg_1069_);
    v___x_1077_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1___redArg(
        v_mvarId_1068_,
        v___f_1076_,
        v_a_1070_,
        v_a_1071_,
        v_a_1072_,
        v_a_1073_,
    );
    return v___x_1077_;
}
pub unsafe fn l_Lean_MVarId_constructor___boxed(
    mut v_mvarId_1078_: *mut LeanObject,
    mut v_cfg_1079_: *mut LeanObject,
    mut v_a_1080_: *mut LeanObject,
    mut v_a_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
    mut v_a_1083_: *mut LeanObject,
    mut v_a_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1085_: *mut LeanObject = core::ptr::null_mut();
    v_res_1085_ = l_Lean_MVarId_constructor(
        v_mvarId_1078_,
        v_cfg_1079_,
        v_a_1080_,
        v_a_1081_,
        v_a_1082_,
        v_a_1083_,
    );
    lean_dec(v_a_1083_);
    lean_dec_ref(v_a_1082_);
    lean_dec(v_a_1081_);
    lean_dec_ref(v_a_1080_);
    return v_res_1085_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0(
    mut v_us_1086_: *mut LeanObject,
    mut v_mvarId_1087_: *mut LeanObject,
    mut v_cfg_1088_: *mut LeanObject,
    mut v_as_1089_: *mut LeanObject,
    mut v_as_x27_1090_: *mut LeanObject,
    mut v_b_1091_: *mut LeanObject,
    mut v_a_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
    mut v___y_1094_: *mut LeanObject,
    mut v___y_1095_: *mut LeanObject,
    mut v___y_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    v___x_1098_ = l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___redArg(
        v_us_1086_,
        v_mvarId_1087_,
        v_cfg_1088_,
        v_as_x27_1090_,
        v_b_1091_,
        v___y_1093_,
        v___y_1094_,
        v___y_1095_,
        v___y_1096_,
    );
    return v___x_1098_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0___boxed(
    mut v_us_1099_: *mut LeanObject,
    mut v_mvarId_1100_: *mut LeanObject,
    mut v_cfg_1101_: *mut LeanObject,
    mut v_as_1102_: *mut LeanObject,
    mut v_as_x27_1103_: *mut LeanObject,
    mut v_b_1104_: *mut LeanObject,
    mut v_a_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1111_: *mut LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_List_forIn_x27_loop___at___00Lean_MVarId_constructor_spec__0(
        v_us_1099_,
        v_mvarId_1100_,
        v_cfg_1101_,
        v_as_1102_,
        v_as_x27_1103_,
        v_b_1104_,
        v_a_1105_,
        v___y_1106_,
        v___y_1107_,
        v___y_1108_,
        v___y_1109_,
    );
    lean_dec(v___y_1109_);
    lean_dec_ref(v___y_1108_);
    lean_dec(v___y_1107_);
    lean_dec_ref(v___y_1106_);
    lean_dec(v_as_x27_1103_);
    lean_dec(v_as_1102_);
    return v_res_1111_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1112_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    v___x_1113_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_1114_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1114_, 0, v___x_1113_);
    return v___x_1114_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    v___x_1115_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1116_ = lean_unsigned_to_nat(0);
    v___x_1117_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1117_, 0, v___x_1116_);
    lean_ctor_set(v___x_1117_, 1, v___x_1116_);
    lean_ctor_set(v___x_1117_, 2, v___x_1116_);
    lean_ctor_set(v___x_1117_, 3, v___x_1116_);
    lean_ctor_set(v___x_1117_, 4, v___x_1115_);
    lean_ctor_set(v___x_1117_, 5, v___x_1115_);
    lean_ctor_set(v___x_1117_, 6, v___x_1115_);
    lean_ctor_set(v___x_1117_, 7, v___x_1115_);
    lean_ctor_set(v___x_1117_, 8, v___x_1115_);
    lean_ctor_set(v___x_1117_, 9, v___x_1115_);
    return v___x_1117_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1118_ = lean_unsigned_to_nat(32);
    v___x_1119_ = lean_mk_empty_array_with_capacity(v___x_1118_);
    v___x_1120_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1120_, 0, v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1121_: usize = 0;
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ = 5usize;
    v___x_1122_ = lean_unsigned_to_nat(0);
    v___x_1123_ = lean_unsigned_to_nat(32);
    v___x_1124_ = lean_mk_empty_array_with_capacity(v___x_1123_);
    v___x_1125_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_1126_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1126_, 0, v___x_1125_);
    lean_ctor_set(v___x_1126_, 1, v___x_1124_);
    lean_ctor_set(v___x_1126_, 2, v___x_1122_);
    lean_ctor_set(v___x_1126_, 3, v___x_1122_);
    lean_ctor_set_usize(v___x_1126_, 4, v___x_1121_);
    return v___x_1126_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1127_ = lean_box(1);
    v___x_1128_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_1129_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1130_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1130_, 0, v___x_1129_);
    lean_ctor_set(v___x_1130_, 1, v___x_1128_);
    lean_ctor_set(v___x_1130_, 2, v___x_1127_);
    return v___x_1130_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
    return v___x_1133_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
    return v___x_1136_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    v___x_1138_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    v___x_1141_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
    return v___x_1142_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    v___x_1144_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
    return v___x_1145_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    v___x_1147_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
    return v___x_1148_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    v___x_1150_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1152_: *mut LeanObject,
    mut v_declHint_1153_: *mut LeanObject,
    mut v___y_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: u8 = 0;
    let mut v_isExporting_1159_: u8 = 0;
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: u8 = 0;
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: u8 = 0;
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1156_ = lean_st_ref_get(v___y_1154_);
                v_env_1157_ = lean_ctor_get(v___x_1156_, 0);
                lean_inc_ref(v_env_1157_);
                lean_dec(v___x_1156_);
                v___x_1158_ = l_Lean_Name_isAnonymous(v_declHint_1153_);
                if v___x_1158_ == 0 {
                    v_isExporting_1159_ = lean_ctor_get_uint8(
                        v_env_1157_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1159_ == 0 {
                        lean_dec_ref(v_env_1157_);
                        lean_dec(v_declHint_1153_);
                        v___x_1160_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1160_, 0, v_msg_1152_);
                        return v___x_1160_;
                    } else {
                        lean_inc_ref(v_env_1157_);
                        v___x_1161_ = l_Lean_Environment_setExporting(v_env_1157_, v___x_1158_);
                        lean_inc(v_declHint_1153_);
                        lean_inc_ref(v___x_1161_);
                        v___x_1162_ = l_Lean_Environment_contains(
                            v___x_1161_,
                            v_declHint_1153_,
                            v_isExporting_1159_,
                        );
                        if v___x_1162_ == 0 {
                            lean_dec_ref(v___x_1161_);
                            lean_dec_ref(v_env_1157_);
                            lean_dec(v_declHint_1153_);
                            v___x_1163_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1163_, 0, v_msg_1152_);
                            return v___x_1163_;
                        } else {
                            v___x_1164_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_1165_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_1166_ = l_Lean_Options_empty;
                            v___x_1167_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1167_, 0, v___x_1161_);
                            lean_ctor_set(v___x_1167_, 1, v___x_1164_);
                            lean_ctor_set(v___x_1167_, 2, v___x_1165_);
                            lean_ctor_set(v___x_1167_, 3, v___x_1166_);
                            lean_inc(v_declHint_1153_);
                            v___x_1168_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1153_, v___x_1158_);
                            v_c_1169_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1169_, 0, v___x_1167_);
                            lean_ctor_set(v_c_1169_, 1, v___x_1168_);
                            v___x_1170_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1157_,
                                v_declHint_1153_,
                            );
                            if lean_obj_tag(v___x_1170_) == 0 {
                                lean_dec_ref(v_env_1157_);
                                lean_dec(v_declHint_1153_);
                                v___x_1171_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_1172_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1172_, 0, v___x_1171_);
                                lean_ctor_set(v___x_1172_, 1, v_c_1169_);
                                v___x_1173_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_1174_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1174_, 0, v___x_1172_);
                                lean_ctor_set(v___x_1174_, 1, v___x_1173_);
                                v___x_1175_ = l_Lean_MessageData_note(v___x_1174_);
                                v___x_1176_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1176_, 0, v_msg_1152_);
                                lean_ctor_set(v___x_1176_, 1, v___x_1175_);
                                v___x_1177_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1177_, 0, v___x_1176_);
                                return v___x_1177_;
                            } else {
                                v_val_1178_ = lean_ctor_get(v___x_1170_, 0);
                                v_isSharedCheck_1213_ = (!lean_is_exclusive(v___x_1170_)) as u8;
                                if v_isSharedCheck_1213_ == 0 {
                                    v___x_1180_ = v___x_1170_;
                                    v_isShared_1181_ = v_isSharedCheck_1213_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1178_);
                                    lean_dec(v___x_1170_);
                                    v___x_1180_ = lean_box(0);
                                    v_isShared_1181_ = v_isSharedCheck_1213_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1157_);
                    lean_dec(v_declHint_1153_);
                    v___x_1214_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1214_, 0, v_msg_1152_);
                    return v___x_1214_;
                }
            }
            1 => {
                v___x_1182_ = lean_box(0);
                v___x_1183_ = l_Lean_Environment_header(v_env_1157_);
                lean_dec_ref(v_env_1157_);
                v___x_1184_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1183_);
                v_mod_1185_ = lean_array_get(v___x_1182_, v___x_1184_, v_val_1178_);
                lean_dec(v_val_1178_);
                lean_dec_ref(v___x_1184_);
                v___x_1186_ = l_Lean_isPrivateName(v_declHint_1153_);
                lean_dec(v_declHint_1153_);
                if v___x_1186_ == 0 {
                    v___x_1187_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1188_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1188_, 0, v___x_1187_);
                    lean_ctor_set(v___x_1188_, 1, v_c_1169_);
                    v___x_1189_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1190_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1190_, 0, v___x_1188_);
                    lean_ctor_set(v___x_1190_, 1, v___x_1189_);
                    v___x_1191_ = l_Lean_MessageData_ofName(v_mod_1185_);
                    v___x_1192_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1192_, 0, v___x_1190_);
                    lean_ctor_set(v___x_1192_, 1, v___x_1191_);
                    v___x_1193_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_1194_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1194_, 0, v___x_1192_);
                    lean_ctor_set(v___x_1194_, 1, v___x_1193_);
                    v___x_1195_ = l_Lean_MessageData_note(v___x_1194_);
                    v___x_1196_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1196_, 0, v_msg_1152_);
                    lean_ctor_set(v___x_1196_, 1, v___x_1195_);
                    if v_isShared_1181_ == 0 {
                        lean_ctor_set_tag(v___x_1180_, 0);
                        lean_ctor_set(v___x_1180_, 0, v___x_1196_);
                        v___x_1198_ = v___x_1180_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
                        v___x_1198_ = v_reuseFailAlloc_1199_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1200_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1201_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1201_, 0, v___x_1200_);
                    lean_ctor_set(v___x_1201_, 1, v_c_1169_);
                    v___x_1202_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_1203_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1203_, 0, v___x_1201_);
                    lean_ctor_set(v___x_1203_, 1, v___x_1202_);
                    v___x_1204_ = l_Lean_MessageData_ofName(v_mod_1185_);
                    v___x_1205_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1205_, 0, v___x_1203_);
                    lean_ctor_set(v___x_1205_, 1, v___x_1204_);
                    v___x_1206_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_1207_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1207_, 0, v___x_1205_);
                    lean_ctor_set(v___x_1207_, 1, v___x_1206_);
                    v___x_1208_ = l_Lean_MessageData_note(v___x_1207_);
                    v___x_1209_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1209_, 0, v_msg_1152_);
                    lean_ctor_set(v___x_1209_, 1, v___x_1208_);
                    if v_isShared_1181_ == 0 {
                        lean_ctor_set_tag(v___x_1180_, 0);
                        lean_ctor_set(v___x_1180_, 0, v___x_1209_);
                        v___x_1211_ = v___x_1180_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
                        v___x_1211_ = v_reuseFailAlloc_1212_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1198_;
            }
            3 => {
                return v___x_1211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_1215_: *mut LeanObject,
    mut v_declHint_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
    mut v___y_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1219_: *mut LeanObject = core::ptr::null_mut();
    v_res_1219_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1215_, v_declHint_1216_, v___y_1217_);
    lean_dec(v___y_1217_);
    return v_res_1219_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1220_: *mut LeanObject,
    mut v_declHint_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
    mut v___y_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1220_, v_declHint_1221_, v___y_1225_);
                v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
                v_isSharedCheck_1237_ = (!lean_is_exclusive(v___x_1227_)) as u8;
                if v_isSharedCheck_1237_ == 0 {
                    v___x_1230_ = v___x_1227_;
                    v_isShared_1231_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1228_);
                    lean_dec(v___x_1227_);
                    v___x_1230_ = lean_box(0);
                    v_isShared_1231_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1232_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1233_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1233_, 0, v___x_1232_);
                lean_ctor_set(v___x_1233_, 1, v_a_1228_);
                if v_isShared_1231_ == 0 {
                    lean_ctor_set(v___x_1230_, 0, v___x_1233_);
                    v___x_1235_ = v___x_1230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
                    v___x_1235_ = v_reuseFailAlloc_1236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_1238_: *mut LeanObject,
    mut v_declHint_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1245_: *mut LeanObject = core::ptr::null_mut();
    v_res_1245_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1238_, v_declHint_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
    lean_dec(v___y_1243_);
    lean_dec_ref(v___y_1242_);
    lean_dec(v___y_1241_);
    lean_dec_ref(v___y_1240_);
    return v_res_1245_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = lean_st_ref_get(v___y_1250_);
    v_env_1253_ = lean_ctor_get(v___x_1252_, 0);
    lean_inc_ref(v_env_1253_);
    lean_dec(v___x_1252_);
    v___x_1254_ = lean_st_ref_get(v___y_1248_);
    v_mctx_1255_ = lean_ctor_get(v___x_1254_, 0);
    lean_inc_ref(v_mctx_1255_);
    lean_dec(v___x_1254_);
    v_lctx_1256_ = lean_ctor_get(v___y_1247_, 2);
    v_options_1257_ = lean_ctor_get(v___y_1249_, 2);
    lean_inc_ref(v_options_1257_);
    lean_inc_ref(v_lctx_1256_);
    v___x_1258_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1258_, 0, v_env_1253_);
    lean_ctor_set(v___x_1258_, 1, v_mctx_1255_);
    lean_ctor_set(v___x_1258_, 2, v_lctx_1256_);
    lean_ctor_set(v___x_1258_, 3, v_options_1257_);
    v___x_1259_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1259_, 0, v___x_1258_);
    lean_ctor_set(v___x_1259_, 1, v_msgData_1246_);
    v___x_1260_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1260_, 0, v___x_1259_);
    return v___x_1260_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1267_: *mut LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
    lean_dec(v___y_1265_);
    lean_dec_ref(v___y_1264_);
    lean_dec(v___y_1263_);
    lean_dec_ref(v___y_1262_);
    return v_res_1267_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1279_: u8 = 0;
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1274_ = lean_ctor_get(v___y_1271_, 5);
                v___x_1275_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
                v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
                v_isSharedCheck_1284_ = (!lean_is_exclusive(v___x_1275_)) as u8;
                if v_isSharedCheck_1284_ == 0 {
                    v___x_1278_ = v___x_1275_;
                    v_isShared_1279_ = v_isSharedCheck_1284_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1276_);
                    lean_dec(v___x_1275_);
                    v___x_1278_ = lean_box(0);
                    v_isShared_1279_ = v_isSharedCheck_1284_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1274_);
                v___x_1280_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1280_, 0, v_ref_1274_);
                lean_ctor_set(v___x_1280_, 1, v_a_1276_);
                if v_isShared_1279_ == 0 {
                    lean_ctor_set_tag(v___x_1278_, 1);
                    lean_ctor_set(v___x_1278_, 0, v___x_1280_);
                    v___x_1282_ = v___x_1278_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
                    v___x_1282_ = v_reuseFailAlloc_1283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
    mut v___y_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1291_: *mut LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
    lean_dec(v___y_1289_);
    lean_dec_ref(v___y_1288_);
    lean_dec(v___y_1287_);
    lean_dec_ref(v___y_1286_);
    return v_res_1291_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_1292_: *mut LeanObject,
    mut v_msg_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1311_: u8 = 0;
    let mut v_cancelTk_x3f_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1313_: u8 = 0;
    let mut v_inheritedTraceOptions_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1299_ = lean_ctor_get(v___y_1296_, 0);
    v_fileMap_1300_ = lean_ctor_get(v___y_1296_, 1);
    v_options_1301_ = lean_ctor_get(v___y_1296_, 2);
    v_currRecDepth_1302_ = lean_ctor_get(v___y_1296_, 3);
    v_maxRecDepth_1303_ = lean_ctor_get(v___y_1296_, 4);
    v_ref_1304_ = lean_ctor_get(v___y_1296_, 5);
    v_currNamespace_1305_ = lean_ctor_get(v___y_1296_, 6);
    v_openDecls_1306_ = lean_ctor_get(v___y_1296_, 7);
    v_initHeartbeats_1307_ = lean_ctor_get(v___y_1296_, 8);
    v_maxHeartbeats_1308_ = lean_ctor_get(v___y_1296_, 9);
    v_quotContext_1309_ = lean_ctor_get(v___y_1296_, 10);
    v_currMacroScope_1310_ = lean_ctor_get(v___y_1296_, 11);
    v_diag_1311_ = lean_ctor_get_uint8(
        v___y_1296_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1312_ = lean_ctor_get(v___y_1296_, 12);
    v_suppressElabErrors_1313_ = lean_ctor_get_uint8(
        v___y_1296_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1314_ = lean_ctor_get(v___y_1296_, 13);
    v_ref_1315_ = l_Lean_replaceRef(v_ref_1292_, v_ref_1304_);
    lean_inc_ref(v_inheritedTraceOptions_1314_);
    lean_inc(v_cancelTk_x3f_1312_);
    lean_inc(v_currMacroScope_1310_);
    lean_inc(v_quotContext_1309_);
    lean_inc(v_maxHeartbeats_1308_);
    lean_inc(v_initHeartbeats_1307_);
    lean_inc(v_openDecls_1306_);
    lean_inc(v_currNamespace_1305_);
    lean_inc(v_maxRecDepth_1303_);
    lean_inc(v_currRecDepth_1302_);
    lean_inc_ref(v_options_1301_);
    lean_inc_ref(v_fileMap_1300_);
    lean_inc_ref(v_fileName_1299_);
    v___x_1316_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1316_, 0, v_fileName_1299_);
    lean_ctor_set(v___x_1316_, 1, v_fileMap_1300_);
    lean_ctor_set(v___x_1316_, 2, v_options_1301_);
    lean_ctor_set(v___x_1316_, 3, v_currRecDepth_1302_);
    lean_ctor_set(v___x_1316_, 4, v_maxRecDepth_1303_);
    lean_ctor_set(v___x_1316_, 5, v_ref_1315_);
    lean_ctor_set(v___x_1316_, 6, v_currNamespace_1305_);
    lean_ctor_set(v___x_1316_, 7, v_openDecls_1306_);
    lean_ctor_set(v___x_1316_, 8, v_initHeartbeats_1307_);
    lean_ctor_set(v___x_1316_, 9, v_maxHeartbeats_1308_);
    lean_ctor_set(v___x_1316_, 10, v_quotContext_1309_);
    lean_ctor_set(v___x_1316_, 11, v_currMacroScope_1310_);
    lean_ctor_set(v___x_1316_, 12, v_cancelTk_x3f_1312_);
    lean_ctor_set(v___x_1316_, 13, v_inheritedTraceOptions_1314_);
    lean_ctor_set_uint8(
        v___x_1316_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1311_,
    );
    lean_ctor_set_uint8(
        v___x_1316_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1313_,
    );
    v___x_1317_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1293_, v___y_1294_, v___y_1295_, v___x_1316_, v___y_1297_);
    lean_dec_ref_known(v___x_1316_, 14);
    return v___x_1317_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_1318_: *mut LeanObject,
    mut v_msg_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1325_: *mut LeanObject = core::ptr::null_mut();
    v_res_1325_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1318_, v_msg_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
    lean_dec(v___y_1323_);
    lean_dec_ref(v___y_1322_);
    lean_dec(v___y_1321_);
    lean_dec_ref(v___y_1320_);
    lean_dec(v_ref_1318_);
    return v_res_1325_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1326_: *mut LeanObject,
    mut v_msg_1327_: *mut LeanObject,
    mut v_declHint_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
    mut v___y_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    v___x_1334_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1327_, v_declHint_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
    v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
    lean_inc(v_a_1335_);
    lean_dec_ref(v___x_1334_);
    v___x_1336_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1326_, v_a_1335_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
    return v___x_1336_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1337_: *mut LeanObject,
    mut v_msg_1338_: *mut LeanObject,
    mut v_declHint_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
    mut v___y_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1345_: *mut LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1337_, v_msg_1338_, v_declHint_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
    lean_dec(v___y_1343_);
    lean_dec_ref(v___y_1342_);
    lean_dec(v___y_1341_);
    lean_dec_ref(v___y_1340_);
    lean_dec(v_ref_1337_);
    return v_res_1345_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1350_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1351_ = l_Lean_stringToMessageData(v___x_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1352_: *mut LeanObject,
    mut v_constName_1353_: *mut LeanObject,
    mut v___y_1354_: *mut LeanObject,
    mut v___y_1355_: *mut LeanObject,
    mut v___y_1356_: *mut LeanObject,
    mut v___y_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    v___x_1359_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1360_ = 0;
    lean_inc(v_constName_1353_);
    v___x_1361_ = l_Lean_MessageData_ofConstName(v_constName_1353_, v___x_1360_);
    v___x_1362_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1362_, 0, v___x_1359_);
    lean_ctor_set(v___x_1362_, 1, v___x_1361_);
    v___x_1363_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1364_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1364_, 0, v___x_1362_);
    lean_ctor_set(v___x_1364_, 1, v___x_1363_);
    v___x_1365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1352_, v___x_1364_, v_constName_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
    return v___x_1365_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1366_: *mut LeanObject,
    mut v_constName_1367_: *mut LeanObject,
    mut v___y_1368_: *mut LeanObject,
    mut v___y_1369_: *mut LeanObject,
    mut v___y_1370_: *mut LeanObject,
    mut v___y_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1373_: *mut LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg(v_ref_1366_, v_constName_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
    lean_dec(v___y_1371_);
    lean_dec_ref(v___y_1370_);
    lean_dec(v___y_1369_);
    lean_dec_ref(v___y_1368_);
    lean_dec(v_ref_1366_);
    return v_res_1373_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0___redArg(
    mut v_constName_1374_: *mut LeanObject,
    mut v___y_1375_: *mut LeanObject,
    mut v___y_1376_: *mut LeanObject,
    mut v___y_1377_: *mut LeanObject,
    mut v___y_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1380_ = lean_ctor_get(v___y_1377_, 5);
    v___x_1381_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg(v_ref_1380_, v_constName_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
    return v___x_1381_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0___redArg___boxed(
    mut v_constName_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v___y_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1388_: *mut LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0___redArg(v_constName_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
    lean_dec(v___y_1386_);
    lean_dec_ref(v___y_1385_);
    lean_dec(v___y_1384_);
    lean_dec_ref(v___y_1383_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0(
    mut v_constName_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1403_: u8 = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1395_ = lean_st_ref_get(v___y_1393_);
                v_env_1396_ = lean_ctor_get(v___x_1395_, 0);
                lean_inc_ref(v_env_1396_);
                lean_dec(v___x_1395_);
                v___x_1397_ = 0;
                lean_inc(v_constName_1389_);
                v___x_1398_ =
                    l_Lean_Environment_find_x3f(v_env_1396_, v_constName_1389_, v___x_1397_);
                if lean_obj_tag(v___x_1398_) == 0 {
                    v___x_1399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0___redArg(v_constName_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
                    return v___x_1399_;
                } else {
                    lean_dec(v_constName_1389_);
                    v_val_1400_ = lean_ctor_get(v___x_1398_, 0);
                    v_isSharedCheck_1407_ = (!lean_is_exclusive(v___x_1398_)) as u8;
                    if v_isSharedCheck_1407_ == 0 {
                        v___x_1402_ = v___x_1398_;
                        v_isShared_1403_ = v_isSharedCheck_1407_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1400_);
                        lean_dec(v___x_1398_);
                        v___x_1402_ = lean_box(0);
                        v_isShared_1403_ = v_isSharedCheck_1407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1403_ == 0 {
                    lean_ctor_set_tag(v___x_1402_, 0);
                    v___x_1405_ = v___x_1402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_val_1400_);
                    v___x_1405_ = v_reuseFailAlloc_1406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0___boxed(
    mut v_constName_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
    mut v___y_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0(
        v_constName_1408_,
        v___y_1409_,
        v___y_1410_,
        v___y_1411_,
        v___y_1412_,
    );
    lean_dec(v___y_1412_);
    lean_dec_ref(v___y_1411_);
    lean_dec(v___y_1410_);
    lean_dec_ref(v___y_1409_);
    return v_res_1414_;
}
pub unsafe fn _init_l_Lean_MVarId_existsIntro___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    v___x_1418_ = l_Lean_MVarId_existsIntro___lam__0___closed__1;
    v___x_1419_ = l_Lean_MessageData_ofFormat(v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn _init_l_Lean_MVarId_existsIntro___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__2_once),
        _init_l_Lean_MVarId_existsIntro___lam__0___closed__2,
    );
    v___x_1421_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1421_, 0, v___x_1420_);
    return v___x_1421_;
}
pub unsafe fn _init_l_Lean_MVarId_existsIntro___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1425_ = l_Lean_MVarId_existsIntro___lam__0___closed__5;
    v___x_1426_ = l_Lean_MessageData_ofFormat(v___x_1425_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_MVarId_existsIntro___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__6_once),
        _init_l_Lean_MVarId_existsIntro___lam__0___closed__6,
    );
    v___x_1428_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1428_, 0, v___x_1427_);
    return v___x_1428_;
}
pub unsafe fn _init_l_Lean_MVarId_existsIntro___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1429_ = lean_box(0);
    v_dummy_1430_ = l_Lean_Expr_sort___override(v___x_1429_);
    return v_dummy_1430_;
}
pub unsafe fn _init_l_Lean_MVarId_existsIntro___lam__0___closed__12() -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = l_Lean_MVarId_existsIntro___lam__0___closed__11;
    v___x_1439_ = l_Lean_MessageData_ofFormat(v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn _init_l_Lean_MVarId_existsIntro___lam__0___closed__13() -> *mut LeanObject {
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    v___x_1440_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__12),
        core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__12_once),
        _init_l_Lean_MVarId_existsIntro___lam__0___closed__12,
    );
    v___x_1441_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1441_, 0, v___x_1440_);
    return v___x_1441_;
}
pub unsafe fn l_Lean_MVarId_existsIntro___lam__0(
    mut v_mvarId_1442_: *mut LeanObject,
    mut v___x_1443_: *mut LeanObject,
    mut v_w_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v_val_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v_tail_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1530_: u8 = 0;
    let mut v_a_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1534_: u8 = 0;
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut v_a_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_a_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v_reuseFailAlloc_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut v_a_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1583_: u8 = 0;
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut v_a_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut v_a_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_1443_);
                lean_inc(v_mvarId_1442_);
                v___x_1464_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1442_,
                    v___x_1443_,
                    v___y_1445_,
                    v___y_1446_,
                    v___y_1447_,
                    v___y_1448_,
                );
                if lean_obj_tag(v___x_1464_) == 0 {
                    lean_dec_ref_known(v___x_1464_, 1);
                    lean_inc(v_mvarId_1442_);
                    v___x_1465_ = l_Lean_MVarId_getType_x27(
                        v_mvarId_1442_,
                        v___y_1445_,
                        v___y_1446_,
                        v___y_1447_,
                        v___y_1448_,
                    );
                    if lean_obj_tag(v___x_1465_) == 0 {
                        v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
                        lean_inc(v_a_1466_);
                        lean_dec_ref_known(v___x_1465_, 1);
                        v___x_1467_ = l_Lean_Expr_getAppFn(v_a_1466_);
                        if lean_obj_tag(v___x_1467_) == 4 {
                            v_declName_1468_ = lean_ctor_get(v___x_1467_, 0);
                            lean_inc(v_declName_1468_);
                            v_us_1469_ = lean_ctor_get(v___x_1467_, 1);
                            lean_inc(v_us_1469_);
                            lean_dec_ref_known(v___x_1467_, 2);
                            v___x_1470_ = lean_st_ref_get(v___y_1448_);
                            v_env_1471_ = lean_ctor_get(v___x_1470_, 0);
                            lean_inc_ref(v_env_1471_);
                            lean_dec(v___x_1470_);
                            v___x_1472_ = 0;
                            v___x_1473_ = l_Lean_Environment_find_x3f(
                                v_env_1471_,
                                v_declName_1468_,
                                v___x_1472_,
                            );
                            if lean_obj_tag(v___x_1473_) == 0 {
                                lean_dec(v_us_1469_);
                                lean_dec(v_a_1466_);
                                lean_dec_ref(v_w_1444_);
                                v___y_1458_ = v___y_1445_;
                                v___y_1459_ = v___y_1446_;
                                v___y_1460_ = v___y_1447_;
                                v___y_1461_ = v___y_1448_;
                                state = 2;
                                continue;
                            } else {
                                v_val_1474_ = lean_ctor_get(v___x_1473_, 0);
                                v_isSharedCheck_1584_ = (!lean_is_exclusive(v___x_1473_)) as u8;
                                if v_isSharedCheck_1584_ == 0 {
                                    v___x_1476_ = v___x_1473_;
                                    v_isShared_1477_ = v_isSharedCheck_1584_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_val_1474_);
                                    lean_dec(v___x_1473_);
                                    v___x_1476_ = lean_box(0);
                                    v_isShared_1477_ = v_isSharedCheck_1584_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1467_);
                            lean_dec(v_a_1466_);
                            lean_dec_ref(v_w_1444_);
                            v___y_1458_ = v___y_1445_;
                            v___y_1459_ = v___y_1446_;
                            v___y_1460_ = v___y_1447_;
                            v___y_1461_ = v___y_1448_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___y_1448_);
                        lean_dec_ref(v___y_1447_);
                        lean_dec(v___y_1446_);
                        lean_dec_ref(v___y_1445_);
                        lean_dec_ref(v_w_1444_);
                        lean_dec(v___x_1443_);
                        lean_dec(v_mvarId_1442_);
                        v_a_1585_ = lean_ctor_get(v___x_1465_, 0);
                        v_isSharedCheck_1592_ = (!lean_is_exclusive(v___x_1465_)) as u8;
                        if v_isSharedCheck_1592_ == 0 {
                            v___x_1587_ = v___x_1465_;
                            v_isShared_1588_ = v_isSharedCheck_1592_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_1585_);
                            lean_dec(v___x_1465_);
                            v___x_1587_ = lean_box(0);
                            v_isShared_1588_ = v_isSharedCheck_1592_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1448_);
                    lean_dec_ref(v___y_1447_);
                    lean_dec(v___y_1446_);
                    lean_dec_ref(v___y_1445_);
                    lean_dec_ref(v_w_1444_);
                    lean_dec(v___x_1443_);
                    lean_dec(v_mvarId_1442_);
                    v_a_1593_ = lean_ctor_get(v___x_1464_, 0);
                    v_isSharedCheck_1600_ = (!lean_is_exclusive(v___x_1464_)) as u8;
                    if v_isSharedCheck_1600_ == 0 {
                        v___x_1595_ = v___x_1464_;
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_1593_);
                        lean_dec(v___x_1464_);
                        v___x_1595_ = lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1455_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__3_once),
                    _init_l_Lean_MVarId_existsIntro___lam__0___closed__3,
                );
                v___x_1456_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1443_,
                    v_mvarId_1442_,
                    v___x_1455_,
                    v___y_1451_,
                    v___y_1452_,
                    v___y_1453_,
                    v___y_1454_,
                );
                lean_dec(v___y_1454_);
                lean_dec_ref(v___y_1453_);
                lean_dec(v___y_1452_);
                lean_dec_ref(v___y_1451_);
                return v___x_1456_;
            }
            2 => {
                v___x_1462_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__7_once),
                    _init_l_Lean_MVarId_existsIntro___lam__0___closed__7,
                );
                v___x_1463_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1443_,
                    v_mvarId_1442_,
                    v___x_1462_,
                    v___y_1458_,
                    v___y_1459_,
                    v___y_1460_,
                    v___y_1461_,
                );
                lean_dec(v___y_1461_);
                lean_dec_ref(v___y_1460_);
                lean_dec(v___y_1459_);
                lean_dec_ref(v___y_1458_);
                return v___x_1463_;
            }
            3 => {
                if lean_obj_tag(v_val_1474_) == 5 {
                    v_val_1478_ = lean_ctor_get(v_val_1474_, 0);
                    lean_inc_ref(v_val_1478_);
                    lean_dec_ref_known(v_val_1474_, 1);
                    v_ctors_1479_ = lean_ctor_get(v_val_1478_, 4);
                    lean_inc(v_ctors_1479_);
                    lean_dec_ref(v_val_1478_);
                    if lean_obj_tag(v_ctors_1479_) == 1 {
                        v_tail_1480_ = lean_ctor_get(v_ctors_1479_, 1);
                        if lean_obj_tag(v_tail_1480_) == 0 {
                            v_head_1481_ = lean_ctor_get(v_ctors_1479_, 0);
                            lean_inc(v_head_1481_);
                            lean_dec_ref_known(v_ctors_1479_, 2);
                            v___x_1482_ =
                                l_Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0(
                                    v_head_1481_,
                                    v___y_1445_,
                                    v___y_1446_,
                                    v___y_1447_,
                                    v___y_1448_,
                                );
                            if lean_obj_tag(v___x_1482_) == 0 {
                                v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
                                lean_inc(v_a_1483_);
                                lean_dec_ref_known(v___x_1482_, 1);
                                if lean_obj_tag(v_a_1483_) == 6 {
                                    v_val_1484_ = lean_ctor_get(v_a_1483_, 0);
                                    lean_inc_ref(v_val_1484_);
                                    lean_dec_ref_known(v_a_1483_, 1);
                                    v_toConstantVal_1485_ = lean_ctor_get(v_val_1484_, 0);
                                    lean_inc_ref(v_toConstantVal_1485_);
                                    v_numParams_1486_ = lean_ctor_get(v_val_1484_, 3);
                                    lean_inc(v_numParams_1486_);
                                    v_numFields_1487_ = lean_ctor_get(v_val_1484_, 4);
                                    lean_inc(v_numFields_1487_);
                                    lean_dec_ref(v_val_1484_);
                                    v___x_1564_ = lean_unsigned_to_nat(2);
                                    v___x_1565_ = lean_nat_dec_lt(v_numFields_1487_, v___x_1564_);
                                    if v___x_1565_ == 0 {
                                        v___y_1489_ = v___y_1445_;
                                        v___y_1490_ = v___y_1446_;
                                        v___y_1491_ = v___y_1447_;
                                        v___y_1492_ = v___y_1448_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v___x_1566_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__13_once), _init_l_Lean_MVarId_existsIntro___lam__0___closed__13);
                                        lean_inc(v_mvarId_1442_);
                                        lean_inc(v___x_1443_);
                                        v___x_1567_ = l_Lean_Meta_throwTacticEx___redArg(
                                            v___x_1443_,
                                            v_mvarId_1442_,
                                            v___x_1566_,
                                            v___y_1445_,
                                            v___y_1446_,
                                            v___y_1447_,
                                            v___y_1448_,
                                        );
                                        if lean_obj_tag(v___x_1567_) == 0 {
                                            lean_dec_ref_known(v___x_1567_, 1);
                                            v___y_1489_ = v___y_1445_;
                                            v___y_1490_ = v___y_1446_;
                                            v___y_1491_ = v___y_1447_;
                                            v___y_1492_ = v___y_1448_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_dec(v_numFields_1487_);
                                            lean_dec(v_numParams_1486_);
                                            lean_dec_ref(v_toConstantVal_1485_);
                                            lean_del_object(v___x_1476_);
                                            lean_dec(v_us_1469_);
                                            lean_dec(v_a_1466_);
                                            lean_dec(v___y_1448_);
                                            lean_dec_ref(v___y_1447_);
                                            lean_dec(v___y_1446_);
                                            lean_dec_ref(v___y_1445_);
                                            lean_dec_ref(v_w_1444_);
                                            lean_dec(v___x_1443_);
                                            lean_dec(v_mvarId_1442_);
                                            v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
                                            v_isSharedCheck_1575_ =
                                                (!lean_is_exclusive(v___x_1567_)) as u8;
                                            if v_isSharedCheck_1575_ == 0 {
                                                v___x_1570_ = v___x_1567_;
                                                v_isShared_1571_ = v_isSharedCheck_1575_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1568_);
                                                lean_dec(v___x_1567_);
                                                v___x_1570_ = lean_box(0);
                                                v_isShared_1571_ = v_isSharedCheck_1575_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_1483_);
                                    lean_del_object(v___x_1476_);
                                    lean_dec(v_us_1469_);
                                    lean_dec(v_a_1466_);
                                    lean_dec_ref(v_w_1444_);
                                    v___y_1458_ = v___y_1445_;
                                    v___y_1459_ = v___y_1446_;
                                    v___y_1460_ = v___y_1447_;
                                    v___y_1461_ = v___y_1448_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_1476_);
                                lean_dec(v_us_1469_);
                                lean_dec(v_a_1466_);
                                lean_dec(v___y_1448_);
                                lean_dec_ref(v___y_1447_);
                                lean_dec(v___y_1446_);
                                lean_dec_ref(v___y_1445_);
                                lean_dec_ref(v_w_1444_);
                                lean_dec(v___x_1443_);
                                lean_dec(v_mvarId_1442_);
                                v_a_1576_ = lean_ctor_get(v___x_1482_, 0);
                                v_isSharedCheck_1583_ = (!lean_is_exclusive(v___x_1482_)) as u8;
                                if v_isSharedCheck_1583_ == 0 {
                                    v___x_1578_ = v___x_1482_;
                                    v_isShared_1579_ = v_isSharedCheck_1583_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_1576_);
                                    lean_dec(v___x_1482_);
                                    v___x_1578_ = lean_box(0);
                                    v_isShared_1579_ = v_isSharedCheck_1583_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_ctors_1479_, 2);
                            lean_del_object(v___x_1476_);
                            lean_dec(v_us_1469_);
                            lean_dec(v_a_1466_);
                            lean_dec_ref(v_w_1444_);
                            v___y_1458_ = v___y_1445_;
                            v___y_1459_ = v___y_1446_;
                            v___y_1460_ = v___y_1447_;
                            v___y_1461_ = v___y_1448_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_ctors_1479_);
                        lean_del_object(v___x_1476_);
                        lean_dec(v_us_1469_);
                        lean_dec(v_a_1466_);
                        lean_dec_ref(v_w_1444_);
                        v___y_1458_ = v___y_1445_;
                        v___y_1459_ = v___y_1446_;
                        v___y_1460_ = v___y_1447_;
                        v___y_1461_ = v___y_1448_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1476_);
                    lean_dec(v_val_1474_);
                    lean_dec(v_us_1469_);
                    lean_dec(v_a_1466_);
                    lean_dec_ref(v_w_1444_);
                    v___y_1458_ = v___y_1445_;
                    v___y_1459_ = v___y_1446_;
                    v___y_1460_ = v___y_1447_;
                    v___y_1461_ = v___y_1448_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_name_1493_ = lean_ctor_get(v_toConstantVal_1485_, 0);
                lean_inc(v_name_1493_);
                lean_dec_ref(v_toConstantVal_1485_);
                v___x_1494_ = l_Lean_mkConst(v_name_1493_, v_us_1469_);
                v_dummy_1495_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_existsIntro___lam__0___closed__8_once),
                    _init_l_Lean_MVarId_existsIntro___lam__0___closed__8,
                );
                v_nargs_1496_ = l_Lean_Expr_getAppNumArgs(v_a_1466_);
                lean_inc(v_nargs_1496_);
                v___x_1497_ = lean_mk_array(v_nargs_1496_, v_dummy_1495_);
                v___x_1498_ = lean_unsigned_to_nat(1);
                v___x_1499_ = lean_nat_sub(v_nargs_1496_, v___x_1498_);
                lean_dec(v_nargs_1496_);
                v___x_1500_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_1466_,
                    v___x_1497_,
                    v___x_1499_,
                );
                v___x_1501_ = lean_unsigned_to_nat(0);
                v___x_1502_ =
                    l_Array_toSubarray___redArg(v___x_1500_, v___x_1501_, v_numParams_1486_);
                v___x_1503_ = l_Subarray_copy___redArg(v___x_1502_);
                v___x_1504_ = l_Lean_mkAppN(v___x_1494_, v___x_1503_);
                lean_dec_ref(v___x_1503_);
                lean_inc(v___y_1492_);
                lean_inc_ref(v___y_1491_);
                lean_inc(v___y_1490_);
                lean_inc_ref(v___y_1489_);
                lean_inc_ref(v___x_1504_);
                v___x_1505_ = lean_infer_type(
                    v___x_1504_,
                    v___y_1489_,
                    v___y_1490_,
                    v___y_1491_,
                    v___y_1492_,
                );
                if lean_obj_tag(v___x_1505_) == 0 {
                    v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
                    lean_inc(v_a_1506_);
                    lean_dec_ref_known(v___x_1505_, 1);
                    v___x_1507_ = lean_unsigned_to_nat(2);
                    v___x_1508_ = lean_nat_sub(v_numFields_1487_, v___x_1507_);
                    lean_dec(v_numFields_1487_);
                    if v_isShared_1477_ == 0 {
                        lean_ctor_set(v___x_1476_, 0, v___x_1508_);
                        v___x_1510_ = v___x_1476_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1508_);
                        v___x_1510_ = v_reuseFailAlloc_1555_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1504_);
                    lean_dec(v___y_1492_);
                    lean_dec_ref(v___y_1491_);
                    lean_dec(v___y_1490_);
                    lean_dec_ref(v___y_1489_);
                    lean_dec(v_numFields_1487_);
                    lean_del_object(v___x_1476_);
                    lean_dec_ref(v_w_1444_);
                    lean_dec(v___x_1443_);
                    lean_dec(v_mvarId_1442_);
                    v_a_1556_ = lean_ctor_get(v___x_1505_, 0);
                    v_isSharedCheck_1563_ = (!lean_is_exclusive(v___x_1505_)) as u8;
                    if v_isSharedCheck_1563_ == 0 {
                        v___x_1558_ = v___x_1505_;
                        v_isShared_1559_ = v_isSharedCheck_1563_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_1556_);
                        lean_dec(v___x_1505_);
                        v___x_1558_ = lean_box(0);
                        v_isShared_1559_ = v_isSharedCheck_1563_;
                        state = 14;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1511_ = 0;
                v___x_1512_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_a_1506_,
                    v___x_1510_,
                    v___x_1511_,
                    v___y_1489_,
                    v___y_1490_,
                    v___y_1491_,
                    v___y_1492_,
                );
                if lean_obj_tag(v___x_1512_) == 0 {
                    v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
                    lean_inc(v_a_1513_);
                    lean_dec_ref_known(v___x_1512_, 1);
                    v_fst_1514_ = lean_ctor_get(v_a_1513_, 0);
                    lean_inc(v_fst_1514_);
                    lean_dec(v_a_1513_);
                    v___x_1515_ = l_Lean_mkAppN(v___x_1504_, v_fst_1514_);
                    lean_dec(v_fst_1514_);
                    lean_inc_ref(v_w_1444_);
                    lean_inc_ref(v___x_1515_);
                    v___x_1516_ = l_Lean_Meta_checkApp(
                        v___x_1515_,
                        v_w_1444_,
                        v___y_1489_,
                        v___y_1490_,
                        v___y_1491_,
                        v___y_1492_,
                    );
                    if lean_obj_tag(v___x_1516_) == 0 {
                        lean_dec_ref_known(v___x_1516_, 1);
                        v___x_1517_ = l_Lean_Expr_app___override(v___x_1515_, v_w_1444_);
                        v___x_1518_ = l_Lean_MVarId_existsIntro___lam__0___closed__9;
                        v___x_1519_ = lean_box(0);
                        lean_inc(v_mvarId_1442_);
                        v___x_1520_ = l_Lean_MVarId_apply(
                            v_mvarId_1442_,
                            v___x_1517_,
                            v___x_1518_,
                            v___x_1519_,
                            v___y_1489_,
                            v___y_1490_,
                            v___y_1491_,
                            v___y_1492_,
                        );
                        if lean_obj_tag(v___x_1520_) == 0 {
                            v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
                            v_isSharedCheck_1530_ = (!lean_is_exclusive(v___x_1520_)) as u8;
                            if v_isSharedCheck_1530_ == 0 {
                                v___x_1523_ = v___x_1520_;
                                v_isShared_1524_ = v_isSharedCheck_1530_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1521_);
                                lean_dec(v___x_1520_);
                                v___x_1523_ = lean_box(0);
                                v_isShared_1524_ = v_isSharedCheck_1530_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v___y_1492_);
                            lean_dec_ref(v___y_1491_);
                            lean_dec(v___y_1490_);
                            lean_dec_ref(v___y_1489_);
                            lean_dec(v___x_1443_);
                            lean_dec(v_mvarId_1442_);
                            v_a_1531_ = lean_ctor_get(v___x_1520_, 0);
                            v_isSharedCheck_1538_ = (!lean_is_exclusive(v___x_1520_)) as u8;
                            if v_isSharedCheck_1538_ == 0 {
                                v___x_1533_ = v___x_1520_;
                                v_isShared_1534_ = v_isSharedCheck_1538_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1531_);
                                lean_dec(v___x_1520_);
                                v___x_1533_ = lean_box(0);
                                v_isShared_1534_ = v_isSharedCheck_1538_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1515_);
                        lean_dec(v___y_1492_);
                        lean_dec_ref(v___y_1491_);
                        lean_dec(v___y_1490_);
                        lean_dec_ref(v___y_1489_);
                        lean_dec_ref(v_w_1444_);
                        lean_dec(v___x_1443_);
                        lean_dec(v_mvarId_1442_);
                        v_a_1539_ = lean_ctor_get(v___x_1516_, 0);
                        v_isSharedCheck_1546_ = (!lean_is_exclusive(v___x_1516_)) as u8;
                        if v_isSharedCheck_1546_ == 0 {
                            v___x_1541_ = v___x_1516_;
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1539_);
                            lean_dec(v___x_1516_);
                            v___x_1541_ = lean_box(0);
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1504_);
                    lean_dec(v___y_1492_);
                    lean_dec_ref(v___y_1491_);
                    lean_dec(v___y_1490_);
                    lean_dec_ref(v___y_1489_);
                    lean_dec_ref(v_w_1444_);
                    lean_dec(v___x_1443_);
                    lean_dec(v_mvarId_1442_);
                    v_a_1547_ = lean_ctor_get(v___x_1512_, 0);
                    v_isSharedCheck_1554_ = (!lean_is_exclusive(v___x_1512_)) as u8;
                    if v_isSharedCheck_1554_ == 0 {
                        v___x_1549_ = v___x_1512_;
                        v_isShared_1550_ = v_isSharedCheck_1554_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1547_);
                        lean_dec(v___x_1512_);
                        v___x_1549_ = lean_box(0);
                        v_isShared_1550_ = v_isSharedCheck_1554_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_1521_) == 1 {
                    v_tail_1525_ = lean_ctor_get(v_a_1521_, 1);
                    if lean_obj_tag(v_tail_1525_) == 0 {
                        lean_dec(v___y_1492_);
                        lean_dec_ref(v___y_1491_);
                        lean_dec(v___y_1490_);
                        lean_dec_ref(v___y_1489_);
                        lean_dec(v___x_1443_);
                        lean_dec(v_mvarId_1442_);
                        v_head_1526_ = lean_ctor_get(v_a_1521_, 0);
                        lean_inc(v_head_1526_);
                        lean_dec_ref_known(v_a_1521_, 2);
                        if v_isShared_1524_ == 0 {
                            lean_ctor_set(v___x_1523_, 0, v_head_1526_);
                            v___x_1528_ = v___x_1523_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_head_1526_);
                            v___x_1528_ = v_reuseFailAlloc_1529_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_1521_, 2);
                        lean_del_object(v___x_1523_);
                        v___y_1451_ = v___y_1489_;
                        v___y_1452_ = v___y_1490_;
                        v___y_1453_ = v___y_1491_;
                        v___y_1454_ = v___y_1492_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1523_);
                    lean_dec(v_a_1521_);
                    v___y_1451_ = v___y_1489_;
                    v___y_1452_ = v___y_1490_;
                    v___y_1453_ = v___y_1491_;
                    v___y_1454_ = v___y_1492_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                return v___x_1528_;
            }
            8 => {
                if v_isShared_1534_ == 0 {
                    v___x_1536_ = v___x_1533_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
                    v___x_1536_ = v_reuseFailAlloc_1537_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1536_;
            }
            10 => {
                if v_isShared_1542_ == 0 {
                    v___x_1544_ = v___x_1541_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
                    v___x_1544_ = v_reuseFailAlloc_1545_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1544_;
            }
            12 => {
                if v_isShared_1550_ == 0 {
                    v___x_1552_ = v___x_1549_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
                    v___x_1552_ = v_reuseFailAlloc_1553_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1552_;
            }
            14 => {
                if v_isShared_1559_ == 0 {
                    v___x_1561_ = v___x_1558_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
                    v___x_1561_ = v_reuseFailAlloc_1562_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1561_;
            }
            16 => {
                if v_isShared_1571_ == 0 {
                    v___x_1573_ = v___x_1570_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
                    v___x_1573_ = v_reuseFailAlloc_1574_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1573_;
            }
            18 => {
                if v_isShared_1579_ == 0 {
                    v___x_1581_ = v___x_1578_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
                    v___x_1581_ = v_reuseFailAlloc_1582_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1581_;
            }
            20 => {
                if v_isShared_1588_ == 0 {
                    v___x_1590_ = v___x_1587_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
                    v___x_1590_ = v_reuseFailAlloc_1591_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1590_;
            }
            22 => {
                if v_isShared_1596_ == 0 {
                    v___x_1598_ = v___x_1595_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
                    v___x_1598_ = v_reuseFailAlloc_1599_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_existsIntro___lam__0___boxed(
    mut v_mvarId_1601_: *mut LeanObject,
    mut v___x_1602_: *mut LeanObject,
    mut v_w_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
    mut v___y_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1609_: *mut LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lean_MVarId_existsIntro___lam__0(
        v_mvarId_1601_,
        v___x_1602_,
        v_w_1603_,
        v___y_1604_,
        v___y_1605_,
        v___y_1606_,
        v___y_1607_,
    );
    return v_res_1609_;
}
pub unsafe fn l_Lean_MVarId_existsIntro(
    mut v_mvarId_1613_: *mut LeanObject,
    mut v_w_1614_: *mut LeanObject,
    mut v_a_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
    mut v_a_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lean_MVarId_existsIntro___closed__1;
    lean_inc(v_mvarId_1613_);
    v___f_1621_ = lean_alloc_closure(
        l_Lean_MVarId_existsIntro___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_1621_, 0, v_mvarId_1613_);
    lean_closure_set(v___f_1621_, 1, v___x_1620_);
    lean_closure_set(v___f_1621_, 2, v_w_1614_);
    v___x_1622_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_constructor_spec__1___redArg(
        v_mvarId_1613_,
        v___f_1621_,
        v_a_1615_,
        v_a_1616_,
        v_a_1617_,
        v_a_1618_,
    );
    return v___x_1622_;
}
pub unsafe fn l_Lean_MVarId_existsIntro___boxed(
    mut v_mvarId_1623_: *mut LeanObject,
    mut v_w_1624_: *mut LeanObject,
    mut v_a_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
    mut v_a_1627_: *mut LeanObject,
    mut v_a_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1630_: *mut LeanObject = core::ptr::null_mut();
    v_res_1630_ = l_Lean_MVarId_existsIntro(
        v_mvarId_1623_,
        v_w_1624_,
        v_a_1625_,
        v_a_1626_,
        v_a_1627_,
        v_a_1628_,
    );
    lean_dec(v_a_1628_);
    lean_dec_ref(v_a_1627_);
    lean_dec(v_a_1626_);
    lean_dec_ref(v_a_1625_);
    return v_res_1630_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0(
    mut v_00_u03b1_1631_: *mut LeanObject,
    mut v_constName_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0___redArg(v_constName_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
    return v___x_1638_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0___boxed(
    mut v_00_u03b1_1639_: *mut LeanObject,
    mut v_constName_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1646_: *mut LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0(v_00_u03b1_1639_, v_constName_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
    lean_dec(v___y_1644_);
    lean_dec_ref(v___y_1643_);
    lean_dec(v___y_1642_);
    lean_dec_ref(v___y_1641_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1647_: *mut LeanObject,
    mut v_ref_1648_: *mut LeanObject,
    mut v_constName_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___redArg(v_ref_1648_, v_constName_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
    return v___x_1655_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1656_: *mut LeanObject,
    mut v_ref_1657_: *mut LeanObject,
    mut v_constName_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1664_: *mut LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1(v_00_u03b1_1656_, v_ref_1657_, v_constName_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
    lean_dec(v___y_1662_);
    lean_dec_ref(v___y_1661_);
    lean_dec(v___y_1660_);
    lean_dec_ref(v___y_1659_);
    lean_dec(v_ref_1657_);
    return v_res_1664_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_1665_: *mut LeanObject,
    mut v_ref_1666_: *mut LeanObject,
    mut v_msg_1667_: *mut LeanObject,
    mut v_declHint_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1666_, v_msg_1667_, v_declHint_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    return v___x_1674_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_1675_: *mut LeanObject,
    mut v_ref_1676_: *mut LeanObject,
    mut v_msg_1677_: *mut LeanObject,
    mut v_declHint_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1684_: *mut LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1675_, v_ref_1676_, v_msg_1677_, v_declHint_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
    lean_dec(v___y_1682_);
    lean_dec_ref(v___y_1681_);
    lean_dec(v___y_1680_);
    lean_dec_ref(v___y_1679_);
    lean_dec(v_ref_1676_);
    return v_res_1684_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_1685_: *mut LeanObject,
    mut v_declHint_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1685_, v_declHint_1686_, v___y_1690_);
    return v___x_1692_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1693_: *mut LeanObject,
    mut v_declHint_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1700_: *mut LeanObject = core::ptr::null_mut();
    v_res_1700_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1693_, v_declHint_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
    lean_dec(v___y_1698_);
    lean_dec_ref(v___y_1697_);
    lean_dec(v___y_1696_);
    lean_dec_ref(v___y_1695_);
    return v_res_1700_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_1701_: *mut LeanObject,
    mut v_ref_1702_: *mut LeanObject,
    mut v_msg_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    v___x_1709_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1702_, v_msg_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
    return v___x_1709_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_1710_: *mut LeanObject,
    mut v_ref_1711_: *mut LeanObject,
    mut v_msg_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1718_: *mut LeanObject = core::ptr::null_mut();
    v_res_1718_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1710_, v_ref_1711_, v_msg_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
    lean_dec(v___y_1716_);
    lean_dec_ref(v___y_1715_);
    lean_dec(v___y_1714_);
    lean_dec_ref(v___y_1713_);
    lean_dec(v_ref_1711_);
    return v_res_1718_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_1719_: *mut LeanObject,
    mut v_msg_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    v___x_1726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
    return v___x_1726_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_1727_: *mut LeanObject,
    mut v_msg_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
    mut v___y_1732_: *mut LeanObject,
    mut v___y_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1734_: *mut LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_MVarId_existsIntro_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1727_, v_msg_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
    lean_dec(v___y_1732_);
    lean_dec_ref(v___y_1731_);
    lean_dec(v___y_1730_);
    lean_dec_ref(v___y_1729_);
    return v_res_1734_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Constructor(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Constructor(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Constructor(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Constructor(builtin);
}

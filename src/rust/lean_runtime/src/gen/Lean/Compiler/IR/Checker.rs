// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: Lean.Compiler.IR.CompilerM
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::Compiler::IR::Basic::{
    l_Lean_IR_Alt_body, l_Lean_IR_CtorInfo_isRef, l_Lean_IR_Decl_name, l_Lean_IR_Decl_params,
    l_Lean_IR_IRType_isObj, l_Lean_IR_IRType_isScalar, l_Lean_IR_LocalContext_addJP,
    l_Lean_IR_LocalContext_addLocal, l_Lean_IR_LocalContext_addParam,
    l_Lean_IR_LocalContext_getType, l_Lean_IR_LocalContext_isJP, l_Lean_IR_LocalContext_isLocalVar,
    l_Lean_IR_LocalContext_isParam, l_Lean_IR_instBEqIRType_beq,
};
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, l_Lean_IR_findEnvDecl_x27,
    runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Compiler::IR::Format::l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Compiler::IR::Checker::{
    lean_get_max_ctor_fields, lean_get_max_ctor_scalars_size, lean_get_max_ctor_tag,
    lean_get_usize_size,
};
static mut l_Lean_IR_Checker_maxCtorFields___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_Checker_maxCtorFields___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_IR_Checker_maxCtorFields: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_Checker_maxCtorScalarsSize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_Checker_maxCtorScalarsSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_IR_Checker_maxCtorScalarsSize: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_Checker_maxCtorTag___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_Checker_maxCtorTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_IR_Checker_maxCtorTag: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_Checker_usizeSize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_Checker_usizeSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_IR_Checker_usizeSize: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value:
    crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 109, 112, 105, 108, 101, 32, 100,
        101, 102, 105, 110, 105, 116, 105, 111, 110, 44, 32, 99, 111, 109, 112, 105, 108, 101, 114,
        32, 73, 82, 32, 99, 104, 101, 99, 107, 32, 102, 97, 105, 108, 101, 100, 32, 97, 116, 32,
        96, 0,
    ],
};
static mut l_Lean_IR_Checker_throwCheckerError___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_Checker_throwCheckerError___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [96, 46, 32, 69, 114, 114, 111, 114, 58, 32, 0],
};
static mut l_Lean_IR_Checker_throwCheckerError___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_Checker_throwCheckerError___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_Checker_markIndex___closed__0_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            118, 97, 114, 105, 97, 98, 108, 101, 32, 47, 32, 106, 111, 105, 110, 32, 112, 111, 105,
            110, 116, 32, 105, 110, 100, 101, 120, 32, 0,
        ],
    };
static mut l_Lean_IR_Checker_markIndex___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_markIndex___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_markIndex___closed__1_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 117,
            115, 101, 100, 0,
        ],
    };
static mut l_Lean_IR_Checker_markIndex___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_markIndex___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_getDecl___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 100, 101, 99, 108, 97, 114, 97,
            116, 105, 111, 110, 32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_getDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_getDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_getDecl___closed__1_value: crate::leanh::LeanStringObject<80> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 80,
        m_capacity: 80,
        m_length: 79,
        m_data: [
            39, 44, 32, 119, 104, 105, 99, 104, 32, 104, 97, 115, 32, 110, 111, 32, 101, 120, 101,
            99, 117, 116, 97, 98, 108, 101, 32, 99, 111, 100, 101, 59, 32, 99, 111, 110, 115, 105,
            100, 101, 114, 32, 109, 97, 114, 107, 105, 110, 103, 32, 100, 101, 102, 105, 110, 105,
            116, 105, 111, 110, 32, 97, 115, 32, 39, 110, 111, 110, 99, 111, 109, 112, 117, 116,
            97, 98, 108, 101, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_getDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_getDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkVar___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkVar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkVar___closed__1_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [120, 95, 0],
    };
static mut l_Lean_IR_Checker_checkVar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkVar___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkVar___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [39, 0],
    };
static mut l_Lean_IR_Checker_checkVar___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkVar___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkJP___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 106, 111, 105, 110, 32, 112, 111, 105, 110, 116,
            32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkJP___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkJP___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkJP___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [98, 108, 111, 99, 107, 95, 0],
    };
static mut l_Lean_IR_Checker_checkJP___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkJP___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkEqTypes___closed__0_value: crate::leanh::LeanStringObject<39> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 34,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 39, 123,
            116, 121, 226, 130, 129, 125, 39, 32, 33, 61, 32, 39, 123, 116, 121, 226, 130, 130,
            125, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkEqTypes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkEqTypes___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkType___closed__0_value: crate::leanh::LeanStringObject<18> =
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
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkType___closed__1_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Lean_IR_Checker_checkType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkType___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkObjType___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            111, 98, 106, 101, 99, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkObjType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkObjType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkScalarType___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            115, 99, 97, 108, 97, 114, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkScalarType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkScalarType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkFullApp___closed__0_value: crate::leanh::LeanStringObject<35> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111,
            102, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 116, 111, 32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkFullApp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkFullApp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkFullApp___closed__1_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [39, 44, 32, 0],
    };
static mut l_Lean_IR_Checker_checkFullApp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkFullApp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkFullApp___closed__2_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [32, 112, 114, 111, 118, 105, 100, 101, 100, 44, 32, 0],
    };
static mut l_Lean_IR_Checker_checkFullApp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkFullApp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkFullApp___closed__3_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [32, 101, 120, 112, 101, 99, 116, 101, 100, 0],
    };
static mut l_Lean_IR_Checker_checkFullApp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkFullApp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkPartialApp___closed__0_value: crate::leanh::LeanStringObject<44> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            116, 111, 111, 32, 109, 97, 110, 121, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115,
            32, 116, 111, 32, 112, 97, 114, 116, 105, 97, 108, 32, 97, 112, 112, 108, 105, 99, 97,
            116, 105, 111, 110, 32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkPartialApp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkPartialApp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkPartialApp___closed__1_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            39, 44, 32, 110, 117, 109, 46, 32, 97, 114, 103, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkPartialApp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkPartialApp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkPartialApp___closed__2_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [44, 32, 97, 114, 105, 116, 121, 58, 32, 0],
    };
static mut l_Lean_IR_Checker_checkPartialApp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkPartialApp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkExpr___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkExpr___closed__1_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            39, 32, 104, 97, 115, 32, 116, 111, 111, 32, 109, 97, 110, 121, 32, 115, 99, 97, 108,
            97, 114, 32, 102, 105, 101, 108, 100, 115, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkExpr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkExpr___closed__2_value: crate::leanh::LeanStringObject<22> =
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
            39, 32, 104, 97, 115, 32, 116, 111, 111, 32, 109, 97, 110, 121, 32, 102, 105, 101, 108,
            100, 115, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkExpr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkExpr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkExpr___closed__3_value: crate::leanh::LeanStringObject<22> =
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
            116, 97, 103, 32, 102, 111, 114, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
            114, 32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkExpr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkExpr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkExpr___closed__4_value: crate::leanh::LeanStringObject<58> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 58,
        m_capacity: 58,
        m_length: 57,
        m_data: [
            39, 32, 105, 115, 32, 116, 111, 111, 32, 98, 105, 103, 44, 32, 116, 104, 105, 115, 32,
            105, 115, 32, 97, 32, 108, 105, 109, 105, 116, 97, 116, 105, 111, 110, 32, 111, 102,
            32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 114, 117, 110, 116, 105,
            109, 101, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkExpr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkExpr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkExpr___closed__5_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 112, 114, 111, 106, 32, 105, 110, 100, 101, 120,
            0,
        ],
    };
static mut l_Lean_IR_Checker_checkExpr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkExpr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_checkExpr___closed__6_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 73, 82, 32, 116, 121, 112, 101,
            32, 39, 0,
        ],
    };
static mut l_Lean_IR_Checker_checkExpr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_checkExpr___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_Checker_withParams___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_Checker_withParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_Checker_withParams___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_Checker_withParams___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_Checker_withParams___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_Checker_withParams___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_withParams___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_withParams___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_Checker_withParams___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_withParams___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Checker_withParams___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_Checker_withParams___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_Checker_withParams___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Checker_withParams___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_IR_Checker_getMaxCtorFields___boxed(
    mut v_a_00___x40___internal___hyg_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1777_ = lean_get_max_ctor_fields(v_a_00___x40___internal___hyg_1776_);
    return v_res_1777_;
}
pub unsafe fn _init_l_Lean_IR_Checker_maxCtorFields___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = crate::leanh::lean_box(0);
    v___x_1779_ = lean_get_max_ctor_fields(v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn _init_l_Lean_IR_Checker_maxCtorFields() -> *mut crate::leanh::LeanObject {
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_maxCtorFields___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_maxCtorFields___closed__0_once),
        _init_l_Lean_IR_Checker_maxCtorFields___closed__0,
    );
    return v___x_1780_;
}
pub unsafe fn l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(
    mut v_a_00___x40___internal___hyg_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = lean_get_max_ctor_scalars_size(v_a_00___x40___internal___hyg_1782_);
    return v_res_1783_;
}
pub unsafe fn _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = crate::leanh::lean_box(0);
    v___x_1785_ = lean_get_max_ctor_scalars_size(v___x_1784_);
    return v___x_1785_;
}
pub unsafe fn _init_l_Lean_IR_Checker_maxCtorScalarsSize() -> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_maxCtorScalarsSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_maxCtorScalarsSize___closed__0_once),
        _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0,
    );
    return v___x_1786_;
}
pub unsafe fn l_Lean_IR_Checker_getMaxCtorTag___boxed(
    mut v_a_00___x40___internal___hyg_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1789_ = lean_get_max_ctor_tag(v_a_00___x40___internal___hyg_1788_);
    return v_res_1789_;
}
pub unsafe fn _init_l_Lean_IR_Checker_maxCtorTag___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = crate::leanh::lean_box(0);
    v___x_1791_ = lean_get_max_ctor_tag(v___x_1790_);
    return v___x_1791_;
}
pub unsafe fn _init_l_Lean_IR_Checker_maxCtorTag() -> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_maxCtorTag___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_maxCtorTag___closed__0_once),
        _init_l_Lean_IR_Checker_maxCtorTag___closed__0,
    );
    return v___x_1792_;
}
pub unsafe fn l_Lean_IR_Checker_getUSizeSize___boxed(
    mut v_a_00___x40___internal___hyg_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = lean_get_usize_size(v_a_00___x40___internal___hyg_1794_);
    return v_res_1795_;
}
pub unsafe fn _init_l_Lean_IR_Checker_usizeSize___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = crate::leanh::lean_box(0);
    v___x_1797_ = lean_get_usize_size(v___x_1796_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lean_IR_Checker_usizeSize() -> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_usizeSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_usizeSize___closed__0_once),
        _init_l_Lean_IR_Checker_usizeSize___closed__0,
    );
    return v___x_1798_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1799_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0);
    v___x_1801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    return v___x_1801_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
    v___x_1803_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1804_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 2, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 3, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 4, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 5, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 6, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 7, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 8, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 9, v___x_1802_);
    return v___x_1804_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1806_ = lean_mk_empty_array_with_capacity(v___x_1805_);
    v___x_1807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1807_, 0, v___x_1806_);
    return v___x_1807_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1808_: usize = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1808_ = 5usize;
    v___x_1809_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1810_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
    v___x_1812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3);
    v___x_1813_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    crate::leanh::lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1813_, 2, v___x_1809_);
    crate::leanh::lean_ctor_set(v___x_1813_, 3, v___x_1809_);
    crate::leanh::lean_ctor_set_usize(v___x_1813_, 4, v___x_1808_);
    return v___x_1813_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = crate::leanh::lean_box(1);
    v___x_1815_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4);
    v___x_1816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
    v___x_1817_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1817_, 0, v___x_1816_);
    crate::leanh::lean_ctor_set(v___x_1817_, 1, v___x_1815_);
    crate::leanh::lean_ctor_set(v___x_1817_, 2, v___x_1814_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(
    mut v_msgData_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = lean_st_ref_get(v___y_1820_);
    v_env_1823_ = crate::leanh::lean_ctor_get(v___x_1822_, 0);
    crate::leanh::lean_inc_ref(v_env_1823_);
    crate::leanh::lean_dec(v___x_1822_);
    v_options_1824_ = crate::leanh::lean_ctor_get(v___y_1819_, 2);
    v___x_1825_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
    v___x_1826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_1824_);
    v___x_1827_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1827_, 0, v_env_1823_);
    crate::leanh::lean_ctor_set(v___x_1827_, 1, v___x_1825_);
    crate::leanh::lean_ctor_set(v___x_1827_, 2, v___x_1826_);
    crate::leanh::lean_ctor_set(v___x_1827_, 3, v_options_1824_);
    v___x_1828_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1828_, 0, v___x_1827_);
    crate::leanh::lean_ctor_set(v___x_1828_, 1, v_msgData_1818_);
    v___x_1829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1829_, 0, v___x_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(
    mut v_msgData_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msgData_1830_, v___y_1831_, v___y_1832_);
    crate::leanh::lean_dec(v___y_1832_);
    crate::leanh::lean_dec_ref(v___y_1831_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(
    mut v_msg_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1839_ = crate::leanh::lean_ctor_get(v___y_1836_, 5);
                v___x_1840_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msg_1835_, v___y_1836_, v___y_1837_);
                v_a_1841_ = crate::leanh::lean_ctor_get(v___x_1840_, 0);
                v_isSharedCheck_1849_ = (!crate::leanh::lean_is_exclusive(v___x_1840_)) as u8;
                if v_isSharedCheck_1849_ == 0 {
                    v___x_1843_ = v___x_1840_;
                    v_isShared_1844_ = v_isSharedCheck_1849_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1841_);
                    crate::leanh::lean_dec(v___x_1840_);
                    v___x_1843_ = crate::leanh::lean_box(0);
                    v_isShared_1844_ = v_isSharedCheck_1849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1839_);
                v___x_1845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1845_, 0, v_ref_1839_);
                crate::leanh::lean_ctor_set(v___x_1845_, 1, v_a_1841_);
                if v_isShared_1844_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1843_, 1);
                    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1845_);
                    v___x_1847_ = v___x_1843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
                    v___x_1847_ = v_reuseFailAlloc_1848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(
    mut v_msg_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1854_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(
        v_msg_1850_,
        v___y_1851_,
        v___y_1852_,
    );
    crate::leanh::lean_dec(v___y_1852_);
    crate::leanh::lean_dec_ref(v___y_1851_);
    return v_res_1854_;
}
pub unsafe fn _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = l_Lean_IR_Checker_throwCheckerError___redArg___closed__0;
    v___x_1857_ = l_Lean_stringToMessageData(v___x_1856_);
    return v___x_1857_;
}
pub unsafe fn _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Lean_IR_Checker_throwCheckerError___redArg___closed__2;
    v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_IR_Checker_throwCheckerError___redArg(
    mut v_msg_1861_: *mut crate::leanh::LeanObject,
    mut v_a_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
    mut v_a_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currentDecl_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_currentDecl_1867_ = crate::leanh::lean_ctor_get(v_a_1862_, 1);
    v___x_1868_ = l_Lean_IR_Decl_name(v_currentDecl_1867_);
    v___x_1869_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_throwCheckerError___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once),
        _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1,
    );
    v___x_1870_ = 0;
    v___x_1871_ = l_Lean_MessageData_ofConstName(v___x_1868_, v___x_1870_);
    v___x_1872_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1872_, 0, v___x_1869_);
    crate::leanh::lean_ctor_set(v___x_1872_, 1, v___x_1871_);
    v___x_1873_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_throwCheckerError___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once),
        _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3,
    );
    v___x_1874_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1874_, 0, v___x_1872_);
    crate::leanh::lean_ctor_set(v___x_1874_, 1, v___x_1873_);
    v___x_1875_ = l_Lean_stringToMessageData(v_msg_1861_);
    v___x_1876_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1876_, 0, v___x_1874_);
    crate::leanh::lean_ctor_set(v___x_1876_, 1, v___x_1875_);
    v___x_1877_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(
        v___x_1876_,
        v_a_1864_,
        v_a_1865_,
    );
    return v___x_1877_;
}
pub unsafe fn l_Lean_IR_Checker_throwCheckerError___redArg___boxed(
    mut v_msg_1878_: *mut crate::leanh::LeanObject,
    mut v_a_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l_Lean_IR_Checker_throwCheckerError___redArg(
        v_msg_1878_,
        v_a_1879_,
        v_a_1880_,
        v_a_1881_,
        v_a_1882_,
    );
    crate::leanh::lean_dec(v_a_1882_);
    crate::leanh::lean_dec_ref(v_a_1881_);
    crate::leanh::lean_dec(v_a_1880_);
    crate::leanh::lean_dec_ref(v_a_1879_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_IR_Checker_throwCheckerError(
    mut v_00_u03b1_1885_: *mut crate::leanh::LeanObject,
    mut v_msg_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Lean_IR_Checker_throwCheckerError___redArg(
        v_msg_1886_,
        v_a_1887_,
        v_a_1888_,
        v_a_1889_,
        v_a_1890_,
    );
    return v___x_1892_;
}
pub unsafe fn l_Lean_IR_Checker_throwCheckerError___boxed(
    mut v_00_u03b1_1893_: *mut crate::leanh::LeanObject,
    mut v_msg_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1900_ = l_Lean_IR_Checker_throwCheckerError(
        v_00_u03b1_1893_,
        v_msg_1894_,
        v_a_1895_,
        v_a_1896_,
        v_a_1897_,
        v_a_1898_,
    );
    crate::leanh::lean_dec(v_a_1898_);
    crate::leanh::lean_dec_ref(v_a_1897_);
    crate::leanh::lean_dec(v_a_1896_);
    crate::leanh::lean_dec_ref(v_a_1895_);
    return v_res_1900_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(
    mut v_00_u03b1_1901_: *mut crate::leanh::LeanObject,
    mut v_msg_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(
        v_msg_1902_,
        v___y_1905_,
        v___y_1906_,
    );
    return v___x_1908_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(
    mut v_00_u03b1_1909_: *mut crate::leanh::LeanObject,
    mut v_msg_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(
        v_00_u03b1_1909_,
        v_msg_1910_,
        v___y_1911_,
        v___y_1912_,
        v___y_1913_,
        v___y_1914_,
    );
    crate::leanh::lean_dec(v___y_1914_);
    crate::leanh::lean_dec_ref(v___y_1913_);
    crate::leanh::lean_dec(v___y_1912_);
    crate::leanh::lean_dec_ref(v___y_1911_);
    return v_res_1916_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(
    mut v_k_1917_: *mut crate::leanh::LeanObject,
    mut v_v_1918_: *mut crate::leanh::LeanObject,
    mut v_t_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v___x_1928_: u8 = 0;
    let mut v___x_1929_: u8 = 0;
    let mut v_impl_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v_size_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1960_: u8 = 0;
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1985_: u8 = 0;
    let mut v_unused_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_unused_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_unused_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v_k_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_unused_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut v_unused_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2049_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2057_: u8 = 0;
    let mut v_unused_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v_size_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_unused_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2138_: u8 = 0;
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2142_: u8 = 0;
    let mut v_unused_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut v_unused_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v_unused_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v_k_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_unused_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_unused_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2205_: u8 = 0;
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1919_) == 0 {
                    v_size_1920_ = crate::leanh::lean_ctor_get(v_t_1919_, 0);
                    v_k_1921_ = crate::leanh::lean_ctor_get(v_t_1919_, 1);
                    v_v_1922_ = crate::leanh::lean_ctor_get(v_t_1919_, 2);
                    v_l_1923_ = crate::leanh::lean_ctor_get(v_t_1919_, 3);
                    v_r_1924_ = crate::leanh::lean_ctor_get(v_t_1919_, 4);
                    v_isSharedCheck_2205_ = (!crate::leanh::lean_is_exclusive(v_t_1919_)) as u8;
                    if v_isSharedCheck_2205_ == 0 {
                        v___x_1926_ = v_t_1919_;
                        v_isShared_1927_ = v_isSharedCheck_2205_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1924_);
                        crate::leanh::lean_inc(v_l_1923_);
                        crate::leanh::lean_inc(v_v_1922_);
                        crate::leanh::lean_inc(v_k_1921_);
                        crate::leanh::lean_inc(v_size_1920_);
                        crate::leanh::lean_dec(v_t_1919_);
                        v___x_1926_ = crate::leanh::lean_box(0);
                        v_isShared_1927_ = v_isSharedCheck_2205_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2206_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2207_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2207_, 0, v___x_2206_);
                    crate::leanh::lean_ctor_set(v___x_2207_, 1, v_k_1917_);
                    crate::leanh::lean_ctor_set(v___x_2207_, 2, v_v_1918_);
                    crate::leanh::lean_ctor_set(v___x_2207_, 3, v_t_1919_);
                    crate::leanh::lean_ctor_set(v___x_2207_, 4, v_t_1919_);
                    return v___x_2207_;
                }
            }
            1 => {
                v___x_1928_ = lean_nat_dec_lt(v_k_1917_, v_k_1921_);
                if v___x_1928_ == 0 {
                    v___x_1929_ = lean_nat_dec_eq(v_k_1917_, v_k_1921_);
                    if v___x_1929_ == 0 {
                        crate::leanh::lean_dec(v_size_1920_);
                        v_impl_1930_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_1917_, v_v_1918_, v_r_1924_);
                        v___x_1931_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1923_) == 0 {
                            v_size_1932_ = crate::leanh::lean_ctor_get(v_l_1923_, 0);
                            v_size_1933_ = crate::leanh::lean_ctor_get(v_impl_1930_, 0);
                            crate::leanh::lean_inc(v_size_1933_);
                            v_k_1934_ = crate::leanh::lean_ctor_get(v_impl_1930_, 1);
                            crate::leanh::lean_inc(v_k_1934_);
                            v_v_1935_ = crate::leanh::lean_ctor_get(v_impl_1930_, 2);
                            crate::leanh::lean_inc(v_v_1935_);
                            v_l_1936_ = crate::leanh::lean_ctor_get(v_impl_1930_, 3);
                            crate::leanh::lean_inc(v_l_1936_);
                            v_r_1937_ = crate::leanh::lean_ctor_get(v_impl_1930_, 4);
                            crate::leanh::lean_inc(v_r_1937_);
                            v___x_1938_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1939_ = lean_nat_mul(v___x_1938_, v_size_1932_);
                            v___x_1940_ = lean_nat_dec_lt(v___x_1939_, v_size_1933_);
                            crate::leanh::lean_dec(v___x_1939_);
                            if v___x_1940_ == 0 {
                                crate::leanh::lean_dec(v_r_1937_);
                                crate::leanh::lean_dec(v_l_1936_);
                                crate::leanh::lean_dec(v_v_1935_);
                                crate::leanh::lean_dec(v_k_1934_);
                                v___x_1941_ = lean_nat_add(v___x_1931_, v_size_1932_);
                                v___x_1942_ = lean_nat_add(v___x_1941_, v_size_1933_);
                                crate::leanh::lean_dec(v_size_1933_);
                                crate::leanh::lean_dec(v___x_1941_);
                                if v_isShared_1927_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v_impl_1930_);
                                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_1942_);
                                    v___x_1944_ = v___x_1926_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1945_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1945_,
                                        0,
                                        v___x_1942_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1945_,
                                        1,
                                        v_k_1921_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1945_,
                                        2,
                                        v_v_1922_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1945_,
                                        3,
                                        v_l_1923_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1945_,
                                        4,
                                        v_impl_1930_,
                                    );
                                    v___x_1944_ = v_reuseFailAlloc_1945_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2009_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1930_)) as u8;
                                if v_isSharedCheck_2009_ == 0 {
                                    v_unused_2010_ = crate::leanh::lean_ctor_get(v_impl_1930_, 4);
                                    crate::leanh::lean_dec(v_unused_2010_);
                                    v_unused_2011_ = crate::leanh::lean_ctor_get(v_impl_1930_, 3);
                                    crate::leanh::lean_dec(v_unused_2011_);
                                    v_unused_2012_ = crate::leanh::lean_ctor_get(v_impl_1930_, 2);
                                    crate::leanh::lean_dec(v_unused_2012_);
                                    v_unused_2013_ = crate::leanh::lean_ctor_get(v_impl_1930_, 1);
                                    crate::leanh::lean_dec(v_unused_2013_);
                                    v_unused_2014_ = crate::leanh::lean_ctor_get(v_impl_1930_, 0);
                                    crate::leanh::lean_dec(v_unused_2014_);
                                    v___x_1947_ = v_impl_1930_;
                                    v_isShared_1948_ = v_isSharedCheck_2009_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1930_);
                                    v___x_1947_ = crate::leanh::lean_box(0);
                                    v_isShared_1948_ = v_isSharedCheck_2009_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2015_ = crate::leanh::lean_ctor_get(v_impl_1930_, 3);
                            crate::leanh::lean_inc(v_l_2015_);
                            if crate::leanh::lean_obj_tag(v_l_2015_) == 0 {
                                v_r_2016_ = crate::leanh::lean_ctor_get(v_impl_1930_, 4);
                                v_k_2017_ = crate::leanh::lean_ctor_get(v_impl_1930_, 1);
                                v_v_2018_ = crate::leanh::lean_ctor_get(v_impl_1930_, 2);
                                v_isSharedCheck_2041_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1930_)) as u8;
                                if v_isSharedCheck_2041_ == 0 {
                                    v_unused_2042_ = crate::leanh::lean_ctor_get(v_impl_1930_, 3);
                                    crate::leanh::lean_dec(v_unused_2042_);
                                    v_unused_2043_ = crate::leanh::lean_ctor_get(v_impl_1930_, 0);
                                    crate::leanh::lean_dec(v_unused_2043_);
                                    v___x_2020_ = v_impl_1930_;
                                    v_isShared_2021_ = v_isSharedCheck_2041_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2016_);
                                    crate::leanh::lean_inc(v_v_2018_);
                                    crate::leanh::lean_inc(v_k_2017_);
                                    crate::leanh::lean_dec(v_impl_1930_);
                                    v___x_2020_ = crate::leanh::lean_box(0);
                                    v_isShared_2021_ = v_isSharedCheck_2041_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2044_ = crate::leanh::lean_ctor_get(v_impl_1930_, 4);
                                crate::leanh::lean_inc(v_r_2044_);
                                if crate::leanh::lean_obj_tag(v_r_2044_) == 0 {
                                    v_k_2045_ = crate::leanh::lean_ctor_get(v_impl_1930_, 1);
                                    v_v_2046_ = crate::leanh::lean_ctor_get(v_impl_1930_, 2);
                                    v_isSharedCheck_2057_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1930_)) as u8;
                                    if v_isSharedCheck_2057_ == 0 {
                                        v_unused_2058_ =
                                            crate::leanh::lean_ctor_get(v_impl_1930_, 4);
                                        crate::leanh::lean_dec(v_unused_2058_);
                                        v_unused_2059_ =
                                            crate::leanh::lean_ctor_get(v_impl_1930_, 3);
                                        crate::leanh::lean_dec(v_unused_2059_);
                                        v_unused_2060_ =
                                            crate::leanh::lean_ctor_get(v_impl_1930_, 0);
                                        crate::leanh::lean_dec(v_unused_2060_);
                                        v___x_2048_ = v_impl_1930_;
                                        v_isShared_2049_ = v_isSharedCheck_2057_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2046_);
                                        crate::leanh::lean_inc(v_k_2045_);
                                        crate::leanh::lean_dec(v_impl_1930_);
                                        v___x_2048_ = crate::leanh::lean_box(0);
                                        v_isShared_2049_ = v_isSharedCheck_2057_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_2061_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1927_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1926_, 4, v_impl_1930_);
                                        crate::leanh::lean_ctor_set(v___x_1926_, 3, v_r_2044_);
                                        crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2061_);
                                        v___x_2063_ = v___x_1926_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2064_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2064_,
                                            0,
                                            v___x_2061_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2064_,
                                            1,
                                            v_k_1921_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2064_,
                                            2,
                                            v_v_1922_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2064_,
                                            3,
                                            v_r_2044_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2064_,
                                            4,
                                            v_impl_1930_,
                                        );
                                        v___x_2063_ = v_reuseFailAlloc_2064_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_v_1922_);
                        crate::leanh::lean_dec(v_k_1921_);
                        if v_isShared_1927_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1926_, 2, v_v_1918_);
                            crate::leanh::lean_ctor_set(v___x_1926_, 1, v_k_1917_);
                            v___x_2066_ = v___x_1926_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2067_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_size_1920_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_1917_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_1918_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 3, v_l_1923_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 4, v_r_1924_);
                            v___x_2066_ = v_reuseFailAlloc_2067_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_size_1920_);
                    v_impl_2068_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_1917_, v_v_1918_, v_l_1923_);
                    v___x_2069_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_r_1924_) == 0 {
                        v_size_2070_ = crate::leanh::lean_ctor_get(v_r_1924_, 0);
                        v_size_2071_ = crate::leanh::lean_ctor_get(v_impl_2068_, 0);
                        crate::leanh::lean_inc(v_size_2071_);
                        v_k_2072_ = crate::leanh::lean_ctor_get(v_impl_2068_, 1);
                        crate::leanh::lean_inc(v_k_2072_);
                        v_v_2073_ = crate::leanh::lean_ctor_get(v_impl_2068_, 2);
                        crate::leanh::lean_inc(v_v_2073_);
                        v_l_2074_ = crate::leanh::lean_ctor_get(v_impl_2068_, 3);
                        crate::leanh::lean_inc(v_l_2074_);
                        v_r_2075_ = crate::leanh::lean_ctor_get(v_impl_2068_, 4);
                        crate::leanh::lean_inc(v_r_2075_);
                        v___x_2076_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_2077_ = lean_nat_mul(v___x_2076_, v_size_2070_);
                        v___x_2078_ = lean_nat_dec_lt(v___x_2077_, v_size_2071_);
                        crate::leanh::lean_dec(v___x_2077_);
                        if v___x_2078_ == 0 {
                            crate::leanh::lean_dec(v_r_2075_);
                            crate::leanh::lean_dec(v_l_2074_);
                            crate::leanh::lean_dec(v_v_2073_);
                            crate::leanh::lean_dec(v_k_2072_);
                            v___x_2079_ = lean_nat_add(v___x_2069_, v_size_2071_);
                            crate::leanh::lean_dec(v_size_2071_);
                            v___x_2080_ = lean_nat_add(v___x_2079_, v_size_2070_);
                            crate::leanh::lean_dec(v___x_2079_);
                            if v_isShared_1927_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1926_, 3, v_impl_2068_);
                                crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2080_);
                                v___x_2082_ = v___x_1926_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_2083_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_k_1921_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_v_1922_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2083_,
                                    3,
                                    v_impl_2068_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 4, v_r_1924_);
                                v___x_2082_ = v_reuseFailAlloc_2083_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_2149_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_2068_)) as u8;
                            if v_isSharedCheck_2149_ == 0 {
                                v_unused_2150_ = crate::leanh::lean_ctor_get(v_impl_2068_, 4);
                                crate::leanh::lean_dec(v_unused_2150_);
                                v_unused_2151_ = crate::leanh::lean_ctor_get(v_impl_2068_, 3);
                                crate::leanh::lean_dec(v_unused_2151_);
                                v_unused_2152_ = crate::leanh::lean_ctor_get(v_impl_2068_, 2);
                                crate::leanh::lean_dec(v_unused_2152_);
                                v_unused_2153_ = crate::leanh::lean_ctor_get(v_impl_2068_, 1);
                                crate::leanh::lean_dec(v_unused_2153_);
                                v_unused_2154_ = crate::leanh::lean_ctor_get(v_impl_2068_, 0);
                                crate::leanh::lean_dec(v_unused_2154_);
                                v___x_2085_ = v_impl_2068_;
                                v_isShared_2086_ = v_isSharedCheck_2149_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_impl_2068_);
                                v___x_2085_ = crate::leanh::lean_box(0);
                                v_isShared_2086_ = v_isSharedCheck_2149_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_2155_ = crate::leanh::lean_ctor_get(v_impl_2068_, 3);
                        crate::leanh::lean_inc(v_l_2155_);
                        if crate::leanh::lean_obj_tag(v_l_2155_) == 0 {
                            v_r_2156_ = crate::leanh::lean_ctor_get(v_impl_2068_, 4);
                            v_k_2157_ = crate::leanh::lean_ctor_get(v_impl_2068_, 1);
                            v_v_2158_ = crate::leanh::lean_ctor_get(v_impl_2068_, 2);
                            v_isSharedCheck_2169_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_2068_)) as u8;
                            if v_isSharedCheck_2169_ == 0 {
                                v_unused_2170_ = crate::leanh::lean_ctor_get(v_impl_2068_, 3);
                                crate::leanh::lean_dec(v_unused_2170_);
                                v_unused_2171_ = crate::leanh::lean_ctor_get(v_impl_2068_, 0);
                                crate::leanh::lean_dec(v_unused_2171_);
                                v___x_2160_ = v_impl_2068_;
                                v_isShared_2161_ = v_isSharedCheck_2169_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_r_2156_);
                                crate::leanh::lean_inc(v_v_2158_);
                                crate::leanh::lean_inc(v_k_2157_);
                                crate::leanh::lean_dec(v_impl_2068_);
                                v___x_2160_ = crate::leanh::lean_box(0);
                                v_isShared_2161_ = v_isSharedCheck_2169_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_2172_ = crate::leanh::lean_ctor_get(v_impl_2068_, 4);
                            crate::leanh::lean_inc(v_r_2172_);
                            if crate::leanh::lean_obj_tag(v_r_2172_) == 0 {
                                v_k_2173_ = crate::leanh::lean_ctor_get(v_impl_2068_, 1);
                                v_v_2174_ = crate::leanh::lean_ctor_get(v_impl_2068_, 2);
                                v_isSharedCheck_2197_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2068_)) as u8;
                                if v_isSharedCheck_2197_ == 0 {
                                    v_unused_2198_ = crate::leanh::lean_ctor_get(v_impl_2068_, 4);
                                    crate::leanh::lean_dec(v_unused_2198_);
                                    v_unused_2199_ = crate::leanh::lean_ctor_get(v_impl_2068_, 3);
                                    crate::leanh::lean_dec(v_unused_2199_);
                                    v_unused_2200_ = crate::leanh::lean_ctor_get(v_impl_2068_, 0);
                                    crate::leanh::lean_dec(v_unused_2200_);
                                    v___x_2176_ = v_impl_2068_;
                                    v_isShared_2177_ = v_isSharedCheck_2197_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_2174_);
                                    crate::leanh::lean_inc(v_k_2173_);
                                    crate::leanh::lean_dec(v_impl_2068_);
                                    v___x_2176_ = crate::leanh::lean_box(0);
                                    v_isShared_2177_ = v_isSharedCheck_2197_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_2201_ = crate::leanh::lean_unsigned_to_nat(2);
                                if v_isShared_1927_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v_r_2172_);
                                    crate::leanh::lean_ctor_set(v___x_1926_, 3, v_impl_2068_);
                                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2201_);
                                    v___x_2203_ = v___x_1926_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2204_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2204_,
                                        0,
                                        v___x_2201_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2204_,
                                        1,
                                        v_k_1921_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2204_,
                                        2,
                                        v_v_1922_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2204_,
                                        3,
                                        v_impl_2068_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2204_,
                                        4,
                                        v_r_2172_,
                                    );
                                    v___x_2203_ = v_reuseFailAlloc_2204_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1944_;
            }
            3 => {
                v_size_1949_ = crate::leanh::lean_ctor_get(v_l_1936_, 0);
                v_k_1950_ = crate::leanh::lean_ctor_get(v_l_1936_, 1);
                v_v_1951_ = crate::leanh::lean_ctor_get(v_l_1936_, 2);
                v_l_1952_ = crate::leanh::lean_ctor_get(v_l_1936_, 3);
                v_r_1953_ = crate::leanh::lean_ctor_get(v_l_1936_, 4);
                v_size_1954_ = crate::leanh::lean_ctor_get(v_r_1937_, 0);
                v___x_1955_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1956_ = lean_nat_mul(v___x_1955_, v_size_1954_);
                v___x_1957_ = lean_nat_dec_lt(v_size_1949_, v___x_1956_);
                crate::leanh::lean_dec(v___x_1956_);
                if v___x_1957_ == 0 {
                    crate::leanh::lean_inc(v_r_1953_);
                    crate::leanh::lean_inc(v_l_1952_);
                    crate::leanh::lean_inc(v_v_1951_);
                    crate::leanh::lean_inc(v_k_1950_);
                    v_isSharedCheck_1985_ = (!crate::leanh::lean_is_exclusive(v_l_1936_)) as u8;
                    if v_isSharedCheck_1985_ == 0 {
                        v_unused_1986_ = crate::leanh::lean_ctor_get(v_l_1936_, 4);
                        crate::leanh::lean_dec(v_unused_1986_);
                        v_unused_1987_ = crate::leanh::lean_ctor_get(v_l_1936_, 3);
                        crate::leanh::lean_dec(v_unused_1987_);
                        v_unused_1988_ = crate::leanh::lean_ctor_get(v_l_1936_, 2);
                        crate::leanh::lean_dec(v_unused_1988_);
                        v_unused_1989_ = crate::leanh::lean_ctor_get(v_l_1936_, 1);
                        crate::leanh::lean_dec(v_unused_1989_);
                        v_unused_1990_ = crate::leanh::lean_ctor_get(v_l_1936_, 0);
                        crate::leanh::lean_dec(v_unused_1990_);
                        v___x_1959_ = v_l_1936_;
                        v_isShared_1960_ = v_isSharedCheck_1985_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1936_);
                        v___x_1959_ = crate::leanh::lean_box(0);
                        v_isShared_1960_ = v_isSharedCheck_1985_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1926_);
                    v___x_1991_ = lean_nat_add(v___x_1931_, v_size_1932_);
                    v___x_1992_ = lean_nat_add(v___x_1991_, v_size_1933_);
                    crate::leanh::lean_dec(v_size_1933_);
                    v___x_1993_ = lean_nat_add(v___x_1991_, v_size_1949_);
                    crate::leanh::lean_dec(v___x_1991_);
                    crate::leanh::lean_inc_ref(v_l_1923_);
                    if v_isShared_1948_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1947_, 4, v_l_1936_);
                        crate::leanh::lean_ctor_set(v___x_1947_, 3, v_l_1923_);
                        crate::leanh::lean_ctor_set(v___x_1947_, 2, v_v_1922_);
                        crate::leanh::lean_ctor_set(v___x_1947_, 1, v_k_1921_);
                        crate::leanh::lean_ctor_set(v___x_1947_, 0, v___x_1993_);
                        v___x_1995_ = v___x_1947_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1993_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_k_1921_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_v_1922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_l_1923_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_l_1936_);
                        v___x_1995_ = v_reuseFailAlloc_2008_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1961_ = lean_nat_add(v___x_1931_, v_size_1932_);
                v___x_1962_ = lean_nat_add(v___x_1961_, v_size_1933_);
                crate::leanh::lean_dec(v_size_1933_);
                if crate::leanh::lean_obj_tag(v_l_1952_) == 0 {
                    v_size_1983_ = crate::leanh::lean_ctor_get(v_l_1952_, 0);
                    crate::leanh::lean_inc(v_size_1983_);
                    v___y_1975_ = v_size_1983_;
                    state = 8;
                    continue;
                } else {
                    v___x_1984_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1975_ = v___x_1984_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1967_ = lean_nat_add(v___y_1964_, v___y_1966_);
                crate::leanh::lean_dec(v___y_1966_);
                crate::leanh::lean_dec(v___y_1964_);
                if v_isShared_1960_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1959_, 4, v_r_1937_);
                    crate::leanh::lean_ctor_set(v___x_1959_, 3, v_r_1953_);
                    crate::leanh::lean_ctor_set(v___x_1959_, 2, v_v_1935_);
                    crate::leanh::lean_ctor_set(v___x_1959_, 1, v_k_1934_);
                    crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1967_);
                    v___x_1969_ = v___x_1959_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_k_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_v_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_r_1953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_r_1937_);
                    v___x_1969_ = v_reuseFailAlloc_1973_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1947_, 4, v___x_1969_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 3, v___y_1965_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 2, v_v_1951_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 1, v_k_1950_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 0, v___x_1962_);
                    v___x_1971_ = v___x_1947_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_k_1950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_v_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 3, v___y_1965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 4, v___x_1969_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1971_;
            }
            8 => {
                v___x_1976_ = lean_nat_add(v___x_1961_, v___y_1975_);
                crate::leanh::lean_dec(v___y_1975_);
                crate::leanh::lean_dec(v___x_1961_);
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v_l_1952_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_1976_);
                    v___x_1978_ = v___x_1926_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_l_1923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 4, v_l_1952_);
                    v___x_1978_ = v_reuseFailAlloc_1982_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1979_ = lean_nat_add(v___x_1931_, v_size_1954_);
                if crate::leanh::lean_obj_tag(v_r_1953_) == 0 {
                    v_size_1980_ = crate::leanh::lean_ctor_get(v_r_1953_, 0);
                    crate::leanh::lean_inc(v_size_1980_);
                    v___y_1964_ = v___x_1979_;
                    v___y_1965_ = v___x_1978_;
                    v___y_1966_ = v_size_1980_;
                    state = 5;
                    continue;
                } else {
                    v___x_1981_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1964_ = v___x_1979_;
                    v___y_1965_ = v___x_1978_;
                    v___y_1966_ = v___x_1981_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2002_ = (!crate::leanh::lean_is_exclusive(v_l_1923_)) as u8;
                if v_isSharedCheck_2002_ == 0 {
                    v_unused_2003_ = crate::leanh::lean_ctor_get(v_l_1923_, 4);
                    crate::leanh::lean_dec(v_unused_2003_);
                    v_unused_2004_ = crate::leanh::lean_ctor_get(v_l_1923_, 3);
                    crate::leanh::lean_dec(v_unused_2004_);
                    v_unused_2005_ = crate::leanh::lean_ctor_get(v_l_1923_, 2);
                    crate::leanh::lean_dec(v_unused_2005_);
                    v_unused_2006_ = crate::leanh::lean_ctor_get(v_l_1923_, 1);
                    crate::leanh::lean_dec(v_unused_2006_);
                    v_unused_2007_ = crate::leanh::lean_ctor_get(v_l_1923_, 0);
                    crate::leanh::lean_dec(v_unused_2007_);
                    v___x_1997_ = v_l_1923_;
                    v_isShared_1998_ = v_isSharedCheck_2002_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1923_);
                    v___x_1997_ = crate::leanh::lean_box(0);
                    v_isShared_1998_ = v_isSharedCheck_2002_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1997_, 4, v_r_1937_);
                    crate::leanh::lean_ctor_set(v___x_1997_, 3, v___x_1995_);
                    crate::leanh::lean_ctor_set(v___x_1997_, 2, v_v_1935_);
                    crate::leanh::lean_ctor_set(v___x_1997_, 1, v_k_1934_);
                    crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_1992_);
                    v___x_2000_ = v___x_1997_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 3, v___x_1995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_r_1937_);
                    v___x_2000_ = v_reuseFailAlloc_2001_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2000_;
            }
            13 => {
                v_k_2022_ = crate::leanh::lean_ctor_get(v_l_2015_, 1);
                v_v_2023_ = crate::leanh::lean_ctor_get(v_l_2015_, 2);
                v_isSharedCheck_2037_ = (!crate::leanh::lean_is_exclusive(v_l_2015_)) as u8;
                if v_isSharedCheck_2037_ == 0 {
                    v_unused_2038_ = crate::leanh::lean_ctor_get(v_l_2015_, 4);
                    crate::leanh::lean_dec(v_unused_2038_);
                    v_unused_2039_ = crate::leanh::lean_ctor_get(v_l_2015_, 3);
                    crate::leanh::lean_dec(v_unused_2039_);
                    v_unused_2040_ = crate::leanh::lean_ctor_get(v_l_2015_, 0);
                    crate::leanh::lean_dec(v_unused_2040_);
                    v___x_2025_ = v_l_2015_;
                    v_isShared_2026_ = v_isSharedCheck_2037_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2023_);
                    crate::leanh::lean_inc(v_k_2022_);
                    crate::leanh::lean_dec(v_l_2015_);
                    v___x_2025_ = crate::leanh::lean_box(0);
                    v_isShared_2026_ = v_isSharedCheck_2037_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2027_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_2016_, 2);
                if v_isShared_2026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2025_, 4, v_r_2016_);
                    crate::leanh::lean_ctor_set(v___x_2025_, 3, v_r_2016_);
                    crate::leanh::lean_ctor_set(v___x_2025_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v___x_2025_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_1931_);
                    v___x_2029_ = v___x_2025_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2036_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_r_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_r_2016_);
                    v___x_2029_ = v_reuseFailAlloc_2036_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_r_2016_);
                if v_isShared_2021_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2020_, 3, v_r_2016_);
                    crate::leanh::lean_ctor_set(v___x_2020_, 0, v___x_1931_);
                    v___x_2031_ = v___x_2020_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_k_2017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_v_2018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_r_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 4, v_r_2016_);
                    v___x_2031_ = v_reuseFailAlloc_2035_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v___x_2031_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 3, v___x_2029_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 2, v_v_2023_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 1, v_k_2022_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2027_);
                    v___x_2033_ = v___x_1926_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_2022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_2023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 3, v___x_2029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 4, v___x_2031_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2033_;
            }
            18 => {
                v___x_2050_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2048_, 4, v_l_2015_);
                    crate::leanh::lean_ctor_set(v___x_2048_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v___x_2048_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v___x_2048_, 0, v___x_1931_);
                    v___x_2052_ = v___x_2048_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_l_2015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_l_2015_);
                    v___x_2052_ = v_reuseFailAlloc_2056_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v_r_2044_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 3, v___x_2052_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 2, v_v_2046_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 1, v_k_2045_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2050_);
                    v___x_2054_ = v___x_1926_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_k_2045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_v_2046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 3, v___x_2052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 4, v_r_2044_);
                    v___x_2054_ = v_reuseFailAlloc_2055_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2054_;
            }
            21 => {
                return v___x_2063_;
            }
            22 => {
                return v___x_2066_;
            }
            23 => {
                return v___x_2082_;
            }
            24 => {
                v_size_2087_ = crate::leanh::lean_ctor_get(v_l_2074_, 0);
                v_size_2088_ = crate::leanh::lean_ctor_get(v_r_2075_, 0);
                v_k_2089_ = crate::leanh::lean_ctor_get(v_r_2075_, 1);
                v_v_2090_ = crate::leanh::lean_ctor_get(v_r_2075_, 2);
                v_l_2091_ = crate::leanh::lean_ctor_get(v_r_2075_, 3);
                v_r_2092_ = crate::leanh::lean_ctor_get(v_r_2075_, 4);
                v___x_2093_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2094_ = lean_nat_mul(v___x_2093_, v_size_2087_);
                v___x_2095_ = lean_nat_dec_lt(v_size_2088_, v___x_2094_);
                crate::leanh::lean_dec(v___x_2094_);
                if v___x_2095_ == 0 {
                    crate::leanh::lean_inc(v_r_2092_);
                    crate::leanh::lean_inc(v_l_2091_);
                    crate::leanh::lean_inc(v_v_2090_);
                    crate::leanh::lean_inc(v_k_2089_);
                    v_isSharedCheck_2124_ = (!crate::leanh::lean_is_exclusive(v_r_2075_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v_unused_2125_ = crate::leanh::lean_ctor_get(v_r_2075_, 4);
                        crate::leanh::lean_dec(v_unused_2125_);
                        v_unused_2126_ = crate::leanh::lean_ctor_get(v_r_2075_, 3);
                        crate::leanh::lean_dec(v_unused_2126_);
                        v_unused_2127_ = crate::leanh::lean_ctor_get(v_r_2075_, 2);
                        crate::leanh::lean_dec(v_unused_2127_);
                        v_unused_2128_ = crate::leanh::lean_ctor_get(v_r_2075_, 1);
                        crate::leanh::lean_dec(v_unused_2128_);
                        v_unused_2129_ = crate::leanh::lean_ctor_get(v_r_2075_, 0);
                        crate::leanh::lean_dec(v_unused_2129_);
                        v___x_2097_ = v_r_2075_;
                        v_isShared_2098_ = v_isSharedCheck_2124_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2075_);
                        v___x_2097_ = crate::leanh::lean_box(0);
                        v_isShared_2098_ = v_isSharedCheck_2124_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1926_);
                    v___x_2130_ = lean_nat_add(v___x_2069_, v_size_2071_);
                    crate::leanh::lean_dec(v_size_2071_);
                    v___x_2131_ = lean_nat_add(v___x_2130_, v_size_2070_);
                    crate::leanh::lean_dec(v___x_2130_);
                    v___x_2132_ = lean_nat_add(v___x_2069_, v_size_2070_);
                    v___x_2133_ = lean_nat_add(v___x_2132_, v_size_2088_);
                    crate::leanh::lean_dec(v___x_2132_);
                    crate::leanh::lean_inc_ref(v_r_1924_);
                    if v_isShared_2086_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2085_, 4, v_r_1924_);
                        crate::leanh::lean_ctor_set(v___x_2085_, 3, v_r_2075_);
                        crate::leanh::lean_ctor_set(v___x_2085_, 2, v_v_1922_);
                        crate::leanh::lean_ctor_set(v___x_2085_, 1, v_k_1921_);
                        crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2133_);
                        v___x_2135_ = v___x_2085_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2148_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2133_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_1921_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_1922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_r_2075_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_r_1924_);
                        v___x_2135_ = v_reuseFailAlloc_2148_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2099_ = lean_nat_add(v___x_2069_, v_size_2071_);
                crate::leanh::lean_dec(v_size_2071_);
                v___x_2100_ = lean_nat_add(v___x_2099_, v_size_2070_);
                crate::leanh::lean_dec(v___x_2099_);
                v___x_2112_ = lean_nat_add(v___x_2069_, v_size_2087_);
                if crate::leanh::lean_obj_tag(v_l_2091_) == 0 {
                    v_size_2122_ = crate::leanh::lean_ctor_get(v_l_2091_, 0);
                    crate::leanh::lean_inc(v_size_2122_);
                    v___y_2114_ = v_size_2122_;
                    state = 29;
                    continue;
                } else {
                    v___x_2123_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2114_ = v___x_2123_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2105_ = lean_nat_add(v___y_2103_, v___y_2104_);
                crate::leanh::lean_dec(v___y_2104_);
                crate::leanh::lean_dec(v___y_2103_);
                if v_isShared_2098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2097_, 4, v_r_1924_);
                    crate::leanh::lean_ctor_set(v___x_2097_, 3, v_r_2092_);
                    crate::leanh::lean_ctor_set(v___x_2097_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v___x_2097_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v___x_2097_, 0, v___x_2105_);
                    v___x_2107_ = v___x_2097_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2111_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_r_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_r_1924_);
                    v___x_2107_ = v_reuseFailAlloc_2111_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2086_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2085_, 4, v___x_2107_);
                    crate::leanh::lean_ctor_set(v___x_2085_, 3, v___y_2102_);
                    crate::leanh::lean_ctor_set(v___x_2085_, 2, v_v_2090_);
                    crate::leanh::lean_ctor_set(v___x_2085_, 1, v_k_2089_);
                    crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2100_);
                    v___x_2109_ = v___x_2085_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_k_2089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_v_2090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 3, v___y_2102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 4, v___x_2107_);
                    v___x_2109_ = v_reuseFailAlloc_2110_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2109_;
            }
            29 => {
                v___x_2115_ = lean_nat_add(v___x_2112_, v___y_2114_);
                crate::leanh::lean_dec(v___y_2114_);
                crate::leanh::lean_dec(v___x_2112_);
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v_l_2091_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 3, v_l_2074_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 2, v_v_2073_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 1, v_k_2072_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2115_);
                    v___x_2117_ = v___x_1926_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2121_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_k_2072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_v_2073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 3, v_l_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 4, v_l_2091_);
                    v___x_2117_ = v_reuseFailAlloc_2121_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2118_ = lean_nat_add(v___x_2069_, v_size_2070_);
                if crate::leanh::lean_obj_tag(v_r_2092_) == 0 {
                    v_size_2119_ = crate::leanh::lean_ctor_get(v_r_2092_, 0);
                    crate::leanh::lean_inc(v_size_2119_);
                    v___y_2102_ = v___x_2117_;
                    v___y_2103_ = v___x_2118_;
                    v___y_2104_ = v_size_2119_;
                    state = 26;
                    continue;
                } else {
                    v___x_2120_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2102_ = v___x_2117_;
                    v___y_2103_ = v___x_2118_;
                    v___y_2104_ = v___x_2120_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2142_ = (!crate::leanh::lean_is_exclusive(v_r_1924_)) as u8;
                if v_isSharedCheck_2142_ == 0 {
                    v_unused_2143_ = crate::leanh::lean_ctor_get(v_r_1924_, 4);
                    crate::leanh::lean_dec(v_unused_2143_);
                    v_unused_2144_ = crate::leanh::lean_ctor_get(v_r_1924_, 3);
                    crate::leanh::lean_dec(v_unused_2144_);
                    v_unused_2145_ = crate::leanh::lean_ctor_get(v_r_1924_, 2);
                    crate::leanh::lean_dec(v_unused_2145_);
                    v_unused_2146_ = crate::leanh::lean_ctor_get(v_r_1924_, 1);
                    crate::leanh::lean_dec(v_unused_2146_);
                    v_unused_2147_ = crate::leanh::lean_ctor_get(v_r_1924_, 0);
                    crate::leanh::lean_dec(v_unused_2147_);
                    v___x_2137_ = v_r_1924_;
                    v_isShared_2138_ = v_isSharedCheck_2142_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1924_);
                    v___x_2137_ = crate::leanh::lean_box(0);
                    v_isShared_2138_ = v_isSharedCheck_2142_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2138_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2137_, 4, v___x_2135_);
                    crate::leanh::lean_ctor_set(v___x_2137_, 3, v_l_2074_);
                    crate::leanh::lean_ctor_set(v___x_2137_, 2, v_v_2073_);
                    crate::leanh::lean_ctor_set(v___x_2137_, 1, v_k_2072_);
                    crate::leanh::lean_ctor_set(v___x_2137_, 0, v___x_2131_);
                    v___x_2140_ = v___x_2137_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_k_2072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_v_2073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_l_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 4, v___x_2135_);
                    v___x_2140_ = v_reuseFailAlloc_2141_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2140_;
            }
            34 => {
                v___x_2162_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_2156_);
                if v_isShared_2161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2160_, 3, v_r_2156_);
                    crate::leanh::lean_ctor_set(v___x_2160_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v___x_2160_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v___x_2160_, 0, v___x_2069_);
                    v___x_2164_ = v___x_2160_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 3, v_r_2156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 4, v_r_2156_);
                    v___x_2164_ = v_reuseFailAlloc_2168_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v___x_2164_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 3, v_l_2155_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 2, v_v_2158_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 1, v_k_2157_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2162_);
                    v___x_2166_ = v___x_1926_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2167_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_k_2157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_v_2158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_l_2155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 4, v___x_2164_);
                    v___x_2166_ = v_reuseFailAlloc_2167_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2166_;
            }
            37 => {
                v_k_2178_ = crate::leanh::lean_ctor_get(v_r_2172_, 1);
                v_v_2179_ = crate::leanh::lean_ctor_get(v_r_2172_, 2);
                v_isSharedCheck_2193_ = (!crate::leanh::lean_is_exclusive(v_r_2172_)) as u8;
                if v_isSharedCheck_2193_ == 0 {
                    v_unused_2194_ = crate::leanh::lean_ctor_get(v_r_2172_, 4);
                    crate::leanh::lean_dec(v_unused_2194_);
                    v_unused_2195_ = crate::leanh::lean_ctor_get(v_r_2172_, 3);
                    crate::leanh::lean_dec(v_unused_2195_);
                    v_unused_2196_ = crate::leanh::lean_ctor_get(v_r_2172_, 0);
                    crate::leanh::lean_dec(v_unused_2196_);
                    v___x_2181_ = v_r_2172_;
                    v_isShared_2182_ = v_isSharedCheck_2193_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2179_);
                    crate::leanh::lean_inc(v_k_2178_);
                    crate::leanh::lean_dec(v_r_2172_);
                    v___x_2181_ = crate::leanh::lean_box(0);
                    v_isShared_2182_ = v_isSharedCheck_2193_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_2183_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2182_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2181_, 4, v_l_2155_);
                    crate::leanh::lean_ctor_set(v___x_2181_, 3, v_l_2155_);
                    crate::leanh::lean_ctor_set(v___x_2181_, 2, v_v_2174_);
                    crate::leanh::lean_ctor_set(v___x_2181_, 1, v_k_2173_);
                    crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2069_);
                    v___x_2185_ = v___x_2181_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2192_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_k_2173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_v_2174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_l_2155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 4, v_l_2155_);
                    v___x_2185_ = v_reuseFailAlloc_2192_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_2177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2176_, 4, v_l_2155_);
                    crate::leanh::lean_ctor_set(v___x_2176_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v___x_2176_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v___x_2176_, 0, v___x_2069_);
                    v___x_2187_ = v___x_2176_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_l_2155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_l_2155_);
                    v___x_2187_ = v_reuseFailAlloc_2191_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 4, v___x_2187_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 3, v___x_2185_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 2, v_v_2179_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 1, v_k_2178_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_2183_);
                    v___x_2189_ = v___x_1926_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_k_2178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_v_2179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 3, v___x_2185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 4, v___x_2187_);
                    v___x_2189_ = v_reuseFailAlloc_2190_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2189_;
            }
            42 => {
                return v___x_2203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(
    mut v_k_2208_: *mut crate::leanh::LeanObject,
    mut v_t_2209_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: u8 = 0;
    let mut v___x_2217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2209_) == 0 {
                    v_k_2210_ = crate::leanh::lean_ctor_get(v_t_2209_, 1);
                    v_l_2211_ = crate::leanh::lean_ctor_get(v_t_2209_, 3);
                    v_r_2212_ = crate::leanh::lean_ctor_get(v_t_2209_, 4);
                    v___x_2213_ = lean_nat_dec_lt(v_k_2208_, v_k_2210_);
                    if v___x_2213_ == 0 {
                        v___x_2214_ = lean_nat_dec_eq(v_k_2208_, v_k_2210_);
                        if v___x_2214_ == 0 {
                            v_t_2209_ = v_r_2212_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2214_;
                        }
                    } else {
                        v_t_2209_ = v_l_2211_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_2217_ = 0;
                    return v___x_2217_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(
    mut v_k_2218_: *mut crate::leanh::LeanObject,
    mut v_t_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2220_: u8 = 0;
    let mut v_r_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2220_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(
            v_k_2218_, v_t_2219_,
        );
    crate::leanh::lean_dec(v_t_2219_);
    crate::leanh::lean_dec(v_k_2218_);
    v_r_2221_ = crate::leanh::lean_box((v_res_2220_) as usize);
    return v_r_2221_;
}
pub unsafe fn l_Lean_IR_Checker_markIndex(
    mut v_i_2224_: *mut crate::leanh::LeanObject,
    mut v_a_2225_: *mut crate::leanh::LeanObject,
    mut v_a_2226_: *mut crate::leanh::LeanObject,
    mut v_a_2227_: *mut crate::leanh::LeanObject,
    mut v_a_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2242_ = lean_st_ref_get(v_a_2226_);
                v___x_2243_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_2224_, v___x_2242_);
                crate::leanh::lean_dec(v___x_2242_);
                if v___x_2243_ == 0 {
                    v___y_2237_ = v_a_2226_;
                    state = 2;
                    continue;
                } else {
                    v___x_2244_ = l_Lean_IR_Checker_markIndex___closed__0;
                    v___x_2245_ = l_Nat_reprFast(v_i_2224_);
                    v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
                    crate::leanh::lean_dec_ref(v___x_2245_);
                    v___x_2247_ = l_Lean_IR_Checker_markIndex___closed__1;
                    v___x_2248_ = lean_string_append(v___x_2246_, v___x_2247_);
                    v___x_2249_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2248_,
                        v_a_2225_,
                        v_a_2226_,
                        v_a_2227_,
                        v_a_2228_,
                    );
                    return v___x_2249_;
                }
            }
            1 => {
                v___x_2234_ = lean_st_ref_set(v___y_2232_, v___y_2233_);
                v___x_2235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2235_, 0, v___y_2231_);
                return v___x_2235_;
            }
            2 => {
                v___x_2238_ = lean_st_ref_take(v___y_2237_);
                v___x_2239_ = crate::leanh::lean_box(0);
                v___x_2240_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_2224_, v___x_2238_);
                if v___x_2240_ == 0 {
                    v___x_2241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_i_2224_, v___x_2239_, v___x_2238_);
                    v___y_2231_ = v___x_2239_;
                    v___y_2232_ = v___y_2237_;
                    v___y_2233_ = v___x_2241_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_i_2224_);
                    v___y_2231_ = v___x_2239_;
                    v___y_2232_ = v___y_2237_;
                    v___y_2233_ = v___x_2238_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_markIndex___boxed(
    mut v_i_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
    mut v_a_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ =
        l_Lean_IR_Checker_markIndex(v_i_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
    crate::leanh::lean_dec(v_a_2254_);
    crate::leanh::lean_dec_ref(v_a_2253_);
    crate::leanh::lean_dec(v_a_2252_);
    crate::leanh::lean_dec_ref(v_a_2251_);
    return v_res_2256_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(
    mut v_00_u03b2_2257_: *mut crate::leanh::LeanObject,
    mut v_k_2258_: *mut crate::leanh::LeanObject,
    mut v_t_2259_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2260_: u8 = 0;
    v___x_2260_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(
            v_k_2258_, v_t_2259_,
        );
    return v___x_2260_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(
    mut v_00_u03b2_2261_: *mut crate::leanh::LeanObject,
    mut v_k_2262_: *mut crate::leanh::LeanObject,
    mut v_t_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2264_: u8 = 0;
    let mut v_r_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(
        v_00_u03b2_2261_,
        v_k_2262_,
        v_t_2263_,
    );
    crate::leanh::lean_dec(v_t_2263_);
    crate::leanh::lean_dec(v_k_2262_);
    v_r_2265_ = crate::leanh::lean_box((v_res_2264_) as usize);
    return v_r_2265_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(
    mut v_00_u03b2_2266_: *mut crate::leanh::LeanObject,
    mut v_k_2267_: *mut crate::leanh::LeanObject,
    mut v_v_2268_: *mut crate::leanh::LeanObject,
    mut v_t_2269_: *mut crate::leanh::LeanObject,
    mut v_hl_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2271_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(
            v_k_2267_, v_v_2268_, v_t_2269_,
        );
    return v___x_2271_;
}
pub unsafe fn l_Lean_IR_Checker_markVar(
    mut v_x_2272_: *mut crate::leanh::LeanObject,
    mut v_a_2273_: *mut crate::leanh::LeanObject,
    mut v_a_2274_: *mut crate::leanh::LeanObject,
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2278_ =
        l_Lean_IR_Checker_markIndex(v_x_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
    return v___x_2278_;
}
pub unsafe fn l_Lean_IR_Checker_markVar___boxed(
    mut v_x_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2285_ = l_Lean_IR_Checker_markVar(v_x_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
    crate::leanh::lean_dec(v_a_2283_);
    crate::leanh::lean_dec_ref(v_a_2282_);
    crate::leanh::lean_dec(v_a_2281_);
    crate::leanh::lean_dec_ref(v_a_2280_);
    return v_res_2285_;
}
pub unsafe fn l_Lean_IR_Checker_markJP(
    mut v_j_2286_: *mut crate::leanh::LeanObject,
    mut v_a_2287_: *mut crate::leanh::LeanObject,
    mut v_a_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ =
        l_Lean_IR_Checker_markIndex(v_j_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
    return v___x_2292_;
}
pub unsafe fn l_Lean_IR_Checker_markJP___boxed(
    mut v_j_2293_: *mut crate::leanh::LeanObject,
    mut v_a_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2299_ = l_Lean_IR_Checker_markJP(v_j_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
    crate::leanh::lean_dec(v_a_2297_);
    crate::leanh::lean_dec_ref(v_a_2296_);
    crate::leanh::lean_dec(v_a_2295_);
    crate::leanh::lean_dec_ref(v_a_2294_);
    return v_res_2299_;
}
pub unsafe fn l_Lean_IR_Checker_getDecl(
    mut v_c_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
    mut v_a_2304_: *mut crate::leanh::LeanObject,
    mut v_a_2305_: *mut crate::leanh::LeanObject,
    mut v_a_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2308_ = lean_st_ref_get(v_a_2306_);
                v_env_2309_ = crate::leanh::lean_ctor_get(v___x_2308_, 0);
                crate::leanh::lean_inc_ref(v_env_2309_);
                crate::leanh::lean_dec(v___x_2308_);
                v_decls_2310_ = crate::leanh::lean_ctor_get(v_a_2303_, 2);
                crate::leanh::lean_inc(v_c_2302_);
                v___x_2311_ = l_Lean_IR_findEnvDecl_x27(v_env_2309_, v_c_2302_, v_decls_2310_);
                if crate::leanh::lean_obj_tag(v___x_2311_) == 0 {
                    v___x_2312_ = l_Lean_IR_Checker_getDecl___closed__0;
                    v___x_2313_ = 1;
                    v___x_2314_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_c_2302_,
                        v___x_2313_,
                    );
                    v___x_2315_ = lean_string_append(v___x_2312_, v___x_2314_);
                    crate::leanh::lean_dec_ref(v___x_2314_);
                    v___x_2316_ = l_Lean_IR_Checker_getDecl___closed__1;
                    v___x_2317_ = lean_string_append(v___x_2315_, v___x_2316_);
                    v___x_2318_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2317_,
                        v_a_2303_,
                        v_a_2304_,
                        v_a_2305_,
                        v_a_2306_,
                    );
                    return v___x_2318_;
                } else {
                    crate::leanh::lean_dec(v_c_2302_);
                    v_val_2319_ = crate::leanh::lean_ctor_get(v___x_2311_, 0);
                    v_isSharedCheck_2326_ = (!crate::leanh::lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2326_ == 0 {
                        v___x_2321_ = v___x_2311_;
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2319_);
                        crate::leanh::lean_dec(v___x_2311_);
                        v___x_2321_ = crate::leanh::lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2322_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2321_, 0);
                    v___x_2324_ = v___x_2321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_val_2319_);
                    v___x_2324_ = v_reuseFailAlloc_2325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_getDecl___boxed(
    mut v_c_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_a_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Lean_IR_Checker_getDecl(v_c_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
    crate::leanh::lean_dec(v_a_2331_);
    crate::leanh::lean_dec_ref(v_a_2330_);
    crate::leanh::lean_dec(v_a_2329_);
    crate::leanh::lean_dec_ref(v_a_2328_);
    return v_res_2333_;
}
pub unsafe fn l_Lean_IR_Checker_checkVar(
    mut v_x_2337_: *mut crate::leanh::LeanObject,
    mut v_a_2338_: *mut crate::leanh::LeanObject,
    mut v_a_2339_: *mut crate::leanh::LeanObject,
    mut v_a_2340_: *mut crate::leanh::LeanObject,
    mut v_a_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2344_: u8 = 0;
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localCtx_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_localCtx_2355_ = crate::leanh::lean_ctor_get(v_a_2338_, 0);
                v___x_2356_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_2355_, v_x_2337_);
                if v___x_2356_ == 0 {
                    v___x_2357_ = l_Lean_IR_LocalContext_isParam(v_localCtx_2355_, v_x_2337_);
                    v___y_2344_ = v___x_2357_;
                    state = 1;
                    continue;
                } else {
                    v___y_2344_ = v___x_2356_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2344_ == 0 {
                    v___x_2345_ = l_Lean_IR_Checker_checkVar___closed__0;
                    v___x_2346_ = l_Lean_IR_Checker_checkVar___closed__1;
                    v___x_2347_ = l_Nat_reprFast(v_x_2337_);
                    v___x_2348_ = lean_string_append(v___x_2346_, v___x_2347_);
                    crate::leanh::lean_dec_ref(v___x_2347_);
                    v___x_2349_ = lean_string_append(v___x_2345_, v___x_2348_);
                    crate::leanh::lean_dec_ref(v___x_2348_);
                    v___x_2350_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v___x_2351_ = lean_string_append(v___x_2349_, v___x_2350_);
                    v___x_2352_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2351_,
                        v_a_2338_,
                        v_a_2339_,
                        v_a_2340_,
                        v_a_2341_,
                    );
                    return v___x_2352_;
                } else {
                    crate::leanh::lean_dec(v_x_2337_);
                    v___x_2353_ = crate::leanh::lean_box(0);
                    v___x_2354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
                    return v___x_2354_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkVar___boxed(
    mut v_x_2358_: *mut crate::leanh::LeanObject,
    mut v_a_2359_: *mut crate::leanh::LeanObject,
    mut v_a_2360_: *mut crate::leanh::LeanObject,
    mut v_a_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_a_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2364_ = l_Lean_IR_Checker_checkVar(v_x_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
    crate::leanh::lean_dec(v_a_2362_);
    crate::leanh::lean_dec_ref(v_a_2361_);
    crate::leanh::lean_dec(v_a_2360_);
    crate::leanh::lean_dec_ref(v_a_2359_);
    return v_res_2364_;
}
pub unsafe fn l_Lean_IR_Checker_checkJP(
    mut v_j_2367_: *mut crate::leanh::LeanObject,
    mut v_a_2368_: *mut crate::leanh::LeanObject,
    mut v_a_2369_: *mut crate::leanh::LeanObject,
    mut v_a_2370_: *mut crate::leanh::LeanObject,
    mut v_a_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_localCtx_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    v_localCtx_2373_ = crate::leanh::lean_ctor_get(v_a_2368_, 0);
    v___x_2374_ = l_Lean_IR_LocalContext_isJP(v_localCtx_2373_, v_j_2367_);
    if v___x_2374_ == 0 {
        let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2375_ = l_Lean_IR_Checker_checkJP___closed__0;
        v___x_2376_ = l_Lean_IR_Checker_checkJP___closed__1;
        v___x_2377_ = l_Nat_reprFast(v_j_2367_);
        v___x_2378_ = lean_string_append(v___x_2376_, v___x_2377_);
        crate::leanh::lean_dec_ref(v___x_2377_);
        v___x_2379_ = lean_string_append(v___x_2375_, v___x_2378_);
        crate::leanh::lean_dec_ref(v___x_2378_);
        v___x_2380_ = l_Lean_IR_Checker_checkVar___closed__2;
        v___x_2381_ = lean_string_append(v___x_2379_, v___x_2380_);
        v___x_2382_ = l_Lean_IR_Checker_throwCheckerError___redArg(
            v___x_2381_,
            v_a_2368_,
            v_a_2369_,
            v_a_2370_,
            v_a_2371_,
        );
        return v___x_2382_;
    } else {
        let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_j_2367_);
        v___x_2383_ = crate::leanh::lean_box(0);
        v___x_2384_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2384_, 0, v___x_2383_);
        return v___x_2384_;
    }
}
pub unsafe fn l_Lean_IR_Checker_checkJP___boxed(
    mut v_j_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_a_2387_: *mut crate::leanh::LeanObject,
    mut v_a_2388_: *mut crate::leanh::LeanObject,
    mut v_a_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2391_ = l_Lean_IR_Checker_checkJP(v_j_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
    crate::leanh::lean_dec(v_a_2389_);
    crate::leanh::lean_dec_ref(v_a_2388_);
    crate::leanh::lean_dec(v_a_2387_);
    crate::leanh::lean_dec_ref(v_a_2386_);
    return v_res_2391_;
}
pub unsafe fn l_Lean_IR_Checker_checkArg(
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
    mut v_a_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_2392_) == 0 {
        let mut v_id_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_id_2398_ = crate::leanh::lean_ctor_get(v_a_2392_, 0);
        crate::leanh::lean_inc(v_id_2398_);
        crate::leanh::lean_dec_ref_known(v_a_2392_, 1);
        v___x_2399_ =
            l_Lean_IR_Checker_checkVar(v_id_2398_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
        return v___x_2399_;
    } else {
        let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2400_ = crate::leanh::lean_box(0);
        v___x_2401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2401_, 0, v___x_2400_);
        return v___x_2401_;
    }
}
pub unsafe fn l_Lean_IR_Checker_checkArg___boxed(
    mut v_a_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
    mut v_a_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l_Lean_IR_Checker_checkArg(v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
    crate::leanh::lean_dec(v_a_2406_);
    crate::leanh::lean_dec_ref(v_a_2405_);
    crate::leanh::lean_dec(v_a_2404_);
    crate::leanh::lean_dec_ref(v_a_2403_);
    return v_res_2408_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(
    mut v_as_2409_: *mut crate::leanh::LeanObject,
    mut v_i_2410_: usize,
    mut v_stop_2411_: usize,
    mut v_b_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
    mut v___y_2416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2418_: u8 = 0;
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: usize = 0;
    let mut v___x_2423_: usize = 0;
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2418_ = lean_usize_dec_eq(v_i_2410_, v_stop_2411_);
                if v___x_2418_ == 0 {
                    v___x_2419_ = lean_array_uget_borrowed(v_as_2409_, v_i_2410_);
                    crate::leanh::lean_inc(v___x_2419_);
                    v___x_2420_ = l_Lean_IR_Checker_checkArg(
                        v___x_2419_,
                        v___y_2413_,
                        v___y_2414_,
                        v___y_2415_,
                        v___y_2416_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2420_) == 0 {
                        v_a_2421_ = crate::leanh::lean_ctor_get(v___x_2420_, 0);
                        crate::leanh::lean_inc(v_a_2421_);
                        crate::leanh::lean_dec_ref_known(v___x_2420_, 1);
                        v___x_2422_ = 1usize;
                        v___x_2423_ = lean_usize_add(v_i_2410_, v___x_2422_);
                        v_i_2410_ = v___x_2423_;
                        v_b_2412_ = v_a_2421_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2420_;
                    }
                } else {
                    v___x_2425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2425_, 0, v_b_2412_);
                    return v___x_2425_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(
    mut v_as_2426_: *mut crate::leanh::LeanObject,
    mut v_i_2427_: *mut crate::leanh::LeanObject,
    mut v_stop_2428_: *mut crate::leanh::LeanObject,
    mut v_b_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2435_: usize = 0;
    let mut v_stop_boxed_2436_: usize = 0;
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2435_ = crate::leanh::lean_unbox_usize(v_i_2427_);
    crate::leanh::lean_dec(v_i_2427_);
    v_stop_boxed_2436_ = crate::leanh::lean_unbox_usize(v_stop_2428_);
    crate::leanh::lean_dec(v_stop_2428_);
    v_res_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_2426_, v_i_boxed_2435_, v_stop_boxed_2436_, v_b_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
    crate::leanh::lean_dec(v___y_2433_);
    crate::leanh::lean_dec_ref(v___y_2432_);
    crate::leanh::lean_dec(v___y_2431_);
    crate::leanh::lean_dec_ref(v___y_2430_);
    crate::leanh::lean_dec_ref(v_as_2426_);
    return v_res_2437_;
}
pub unsafe fn l_Lean_IR_Checker_checkArgs(
    mut v_as_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    v___x_2444_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2445_ = lean_array_get_size(v_as_2438_);
    v___x_2446_ = crate::leanh::lean_box(0);
    v___x_2447_ = lean_nat_dec_lt(v___x_2444_, v___x_2445_);
    if v___x_2447_ == 0 {
        let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2448_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2446_);
        return v___x_2448_;
    } else {
        let mut v___x_2449_: u8 = 0;
        v___x_2449_ = lean_nat_dec_le(v___x_2445_, v___x_2445_);
        if v___x_2449_ == 0 {
            if v___x_2447_ == 0 {
                let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2446_);
                return v___x_2450_;
            } else {
                let mut v___x_2451_: usize = 0;
                let mut v___x_2452_: usize = 0;
                let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2451_ = 0usize;
                v___x_2452_ = lean_usize_of_nat(v___x_2445_);
                v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_2438_, v___x_2451_, v___x_2452_, v___x_2446_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
                return v___x_2453_;
            }
        } else {
            let mut v___x_2454_: usize = 0;
            let mut v___x_2455_: usize = 0;
            let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2454_ = 0usize;
            v___x_2455_ = lean_usize_of_nat(v___x_2445_);
            v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_2438_, v___x_2454_, v___x_2455_, v___x_2446_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
            return v___x_2456_;
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkArgs___boxed(
    mut v_as_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2463_ =
        l_Lean_IR_Checker_checkArgs(v_as_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
    crate::leanh::lean_dec(v_a_2461_);
    crate::leanh::lean_dec_ref(v_a_2460_);
    crate::leanh::lean_dec(v_a_2459_);
    crate::leanh::lean_dec_ref(v_a_2458_);
    crate::leanh::lean_dec_ref(v_as_2457_);
    return v_res_2463_;
}
pub unsafe fn l_Lean_IR_Checker_checkEqTypes(
    mut v_ty_u2081_2465_: *mut crate::leanh::LeanObject,
    mut v_ty_u2082_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: u8 = 0;
    v___x_2472_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_2465_, v_ty_u2082_2466_);
    if v___x_2472_ == 0 {
        let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2473_ = l_Lean_IR_Checker_checkEqTypes___closed__0;
        v___x_2474_ = l_Lean_IR_Checker_throwCheckerError___redArg(
            v___x_2473_,
            v_a_2467_,
            v_a_2468_,
            v_a_2469_,
            v_a_2470_,
        );
        return v___x_2474_;
    } else {
        let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2475_ = crate::leanh::lean_box(0);
        v___x_2476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2476_, 0, v___x_2475_);
        return v___x_2476_;
    }
}
pub unsafe fn l_Lean_IR_Checker_checkEqTypes___boxed(
    mut v_ty_u2081_2477_: *mut crate::leanh::LeanObject,
    mut v_ty_u2082_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l_Lean_IR_Checker_checkEqTypes(
        v_ty_u2081_2477_,
        v_ty_u2082_2478_,
        v_a_2479_,
        v_a_2480_,
        v_a_2481_,
        v_a_2482_,
    );
    crate::leanh::lean_dec(v_a_2482_);
    crate::leanh::lean_dec_ref(v_a_2481_);
    crate::leanh::lean_dec(v_a_2480_);
    crate::leanh::lean_dec_ref(v_a_2479_);
    crate::leanh::lean_dec(v_ty_u2082_2478_);
    crate::leanh::lean_dec(v_ty_u2081_2477_);
    return v_res_2484_;
}
pub unsafe fn l_Lean_IR_Checker_checkType(
    mut v_ty_2487_: *mut crate::leanh::LeanObject,
    mut v_p_2488_: *mut crate::leanh::LeanObject,
    mut v_suffix_x3f_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
    mut v_a_2491_: *mut crate::leanh::LeanObject,
    mut v_a_2492_: *mut crate::leanh::LeanObject,
    mut v_a_2493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: u8 = 0;
    crate::leanh::lean_inc(v_ty_2487_);
    v___x_2495_ = crate::leanh::lean_apply_1(v_p_2488_, v_ty_2487_);
    v___x_2496_ = (crate::leanh::lean_unbox(v___x_2495_) as u8);
    if v___x_2496_ == 0 {
        let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_msg_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2497_ = l_Lean_IR_Checker_checkType___closed__0;
        v___x_2498_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2487_);
        v___x_2499_ = l_Std_Format_defWidth;
        v___x_2500_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2501_ = l_Std_Format_pretty(v___x_2498_, v___x_2499_, v___x_2500_, v___x_2500_);
        v___x_2502_ = lean_string_append(v___x_2497_, v___x_2501_);
        crate::leanh::lean_dec_ref(v___x_2501_);
        v___x_2503_ = l_Lean_IR_Checker_checkVar___closed__2;
        v_msg_2504_ = lean_string_append(v___x_2502_, v___x_2503_);
        if crate::leanh::lean_obj_tag(v_suffix_x3f_2489_) == 1 {
            let mut v_val_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_msg_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2505_ = crate::leanh::lean_ctor_get(v_suffix_x3f_2489_, 0);
            v___x_2506_ = l_Lean_IR_Checker_checkType___closed__1;
            v___x_2507_ = lean_string_append(v_msg_2504_, v___x_2506_);
            v_msg_2508_ = lean_string_append(v___x_2507_, v_val_2505_);
            v___x_2509_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                v_msg_2508_,
                v_a_2490_,
                v_a_2491_,
                v_a_2492_,
                v_a_2493_,
            );
            return v___x_2509_;
        } else {
            let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2510_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                v_msg_2504_,
                v_a_2490_,
                v_a_2491_,
                v_a_2492_,
                v_a_2493_,
            );
            return v___x_2510_;
        }
    } else {
        let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_ty_2487_);
        v___x_2511_ = crate::leanh::lean_box(0);
        v___x_2512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2512_, 0, v___x_2511_);
        return v___x_2512_;
    }
}
pub unsafe fn l_Lean_IR_Checker_checkType___boxed(
    mut v_ty_2513_: *mut crate::leanh::LeanObject,
    mut v_p_2514_: *mut crate::leanh::LeanObject,
    mut v_suffix_x3f_2515_: *mut crate::leanh::LeanObject,
    mut v_a_2516_: *mut crate::leanh::LeanObject,
    mut v_a_2517_: *mut crate::leanh::LeanObject,
    mut v_a_2518_: *mut crate::leanh::LeanObject,
    mut v_a_2519_: *mut crate::leanh::LeanObject,
    mut v_a_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_IR_Checker_checkType(
        v_ty_2513_,
        v_p_2514_,
        v_suffix_x3f_2515_,
        v_a_2516_,
        v_a_2517_,
        v_a_2518_,
        v_a_2519_,
    );
    crate::leanh::lean_dec(v_a_2519_);
    crate::leanh::lean_dec_ref(v_a_2518_);
    crate::leanh::lean_dec(v_a_2517_);
    crate::leanh::lean_dec_ref(v_a_2516_);
    crate::leanh::lean_dec(v_suffix_x3f_2515_);
    return v_res_2521_;
}
pub unsafe fn l_Lean_IR_Checker_checkObjType(
    mut v_ty_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
    mut v_a_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
    mut v_a_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2529_: u8 = 0;
    v___x_2529_ = l_Lean_IR_IRType_isObj(v_ty_2523_);
    if v___x_2529_ == 0 {
        let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_msg_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_msg_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2530_ = l_Lean_IR_Checker_checkObjType___closed__0;
        v___x_2531_ = l_Lean_IR_Checker_checkType___closed__0;
        v___x_2532_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2523_);
        v___x_2533_ = l_Std_Format_defWidth;
        v___x_2534_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2535_ = l_Std_Format_pretty(v___x_2532_, v___x_2533_, v___x_2534_, v___x_2534_);
        v___x_2536_ = lean_string_append(v___x_2531_, v___x_2535_);
        crate::leanh::lean_dec_ref(v___x_2535_);
        v___x_2537_ = l_Lean_IR_Checker_checkVar___closed__2;
        v_msg_2538_ = lean_string_append(v___x_2536_, v___x_2537_);
        v___x_2539_ = l_Lean_IR_Checker_checkType___closed__1;
        v___x_2540_ = lean_string_append(v_msg_2538_, v___x_2539_);
        v_msg_2541_ = lean_string_append(v___x_2540_, v___x_2530_);
        v___x_2542_ = l_Lean_IR_Checker_throwCheckerError___redArg(
            v_msg_2541_,
            v_a_2524_,
            v_a_2525_,
            v_a_2526_,
            v_a_2527_,
        );
        return v___x_2542_;
    } else {
        let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_ty_2523_);
        v___x_2543_ = crate::leanh::lean_box(0);
        v___x_2544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2544_, 0, v___x_2543_);
        return v___x_2544_;
    }
}
pub unsafe fn l_Lean_IR_Checker_checkObjType___boxed(
    mut v_ty_2545_: *mut crate::leanh::LeanObject,
    mut v_a_2546_: *mut crate::leanh::LeanObject,
    mut v_a_2547_: *mut crate::leanh::LeanObject,
    mut v_a_2548_: *mut crate::leanh::LeanObject,
    mut v_a_2549_: *mut crate::leanh::LeanObject,
    mut v_a_2550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ =
        l_Lean_IR_Checker_checkObjType(v_ty_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
    crate::leanh::lean_dec(v_a_2549_);
    crate::leanh::lean_dec_ref(v_a_2548_);
    crate::leanh::lean_dec(v_a_2547_);
    crate::leanh::lean_dec_ref(v_a_2546_);
    return v_res_2551_;
}
pub unsafe fn l_Lean_IR_Checker_checkScalarType(
    mut v_ty_2553_: *mut crate::leanh::LeanObject,
    mut v_a_2554_: *mut crate::leanh::LeanObject,
    mut v_a_2555_: *mut crate::leanh::LeanObject,
    mut v_a_2556_: *mut crate::leanh::LeanObject,
    mut v_a_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2559_: u8 = 0;
    v___x_2559_ = l_Lean_IR_IRType_isScalar(v_ty_2553_);
    if v___x_2559_ == 0 {
        let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_msg_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_msg_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2560_ = l_Lean_IR_Checker_checkScalarType___closed__0;
        v___x_2561_ = l_Lean_IR_Checker_checkType___closed__0;
        v___x_2562_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2553_);
        v___x_2563_ = l_Std_Format_defWidth;
        v___x_2564_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2565_ = l_Std_Format_pretty(v___x_2562_, v___x_2563_, v___x_2564_, v___x_2564_);
        v___x_2566_ = lean_string_append(v___x_2561_, v___x_2565_);
        crate::leanh::lean_dec_ref(v___x_2565_);
        v___x_2567_ = l_Lean_IR_Checker_checkVar___closed__2;
        v_msg_2568_ = lean_string_append(v___x_2566_, v___x_2567_);
        v___x_2569_ = l_Lean_IR_Checker_checkType___closed__1;
        v___x_2570_ = lean_string_append(v_msg_2568_, v___x_2569_);
        v_msg_2571_ = lean_string_append(v___x_2570_, v___x_2560_);
        v___x_2572_ = l_Lean_IR_Checker_throwCheckerError___redArg(
            v_msg_2571_,
            v_a_2554_,
            v_a_2555_,
            v_a_2556_,
            v_a_2557_,
        );
        return v___x_2572_;
    } else {
        let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_ty_2553_);
        v___x_2573_ = crate::leanh::lean_box(0);
        v___x_2574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2574_, 0, v___x_2573_);
        return v___x_2574_;
    }
}
pub unsafe fn l_Lean_IR_Checker_checkScalarType___boxed(
    mut v_ty_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
    mut v_a_2577_: *mut crate::leanh::LeanObject,
    mut v_a_2578_: *mut crate::leanh::LeanObject,
    mut v_a_2579_: *mut crate::leanh::LeanObject,
    mut v_a_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2581_ =
        l_Lean_IR_Checker_checkScalarType(v_ty_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
    crate::leanh::lean_dec(v_a_2579_);
    crate::leanh::lean_dec_ref(v_a_2578_);
    crate::leanh::lean_dec(v_a_2577_);
    crate::leanh::lean_dec_ref(v_a_2576_);
    return v_res_2581_;
}
pub unsafe fn l_Lean_IR_Checker_getType(
    mut v_x_2582_: *mut crate::leanh::LeanObject,
    mut v_a_2583_: *mut crate::leanh::LeanObject,
    mut v_a_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_localCtx_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_localCtx_2588_ = crate::leanh::lean_ctor_get(v_a_2583_, 0);
                v___x_2589_ = l_Lean_IR_LocalContext_getType(v_localCtx_2588_, v_x_2582_);
                if crate::leanh::lean_obj_tag(v___x_2589_) == 0 {
                    v___x_2590_ = l_Lean_IR_Checker_checkVar___closed__0;
                    v___x_2591_ = l_Lean_IR_Checker_checkVar___closed__1;
                    v___x_2592_ = l_Nat_reprFast(v_x_2582_);
                    v___x_2593_ = lean_string_append(v___x_2591_, v___x_2592_);
                    crate::leanh::lean_dec_ref(v___x_2592_);
                    v___x_2594_ = lean_string_append(v___x_2590_, v___x_2593_);
                    crate::leanh::lean_dec_ref(v___x_2593_);
                    v___x_2595_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v___x_2596_ = lean_string_append(v___x_2594_, v___x_2595_);
                    v___x_2597_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2596_,
                        v_a_2583_,
                        v_a_2584_,
                        v_a_2585_,
                        v_a_2586_,
                    );
                    return v___x_2597_;
                } else {
                    crate::leanh::lean_dec(v_x_2582_);
                    v_val_2598_ = crate::leanh::lean_ctor_get(v___x_2589_, 0);
                    v_isSharedCheck_2605_ = (!crate::leanh::lean_is_exclusive(v___x_2589_)) as u8;
                    if v_isSharedCheck_2605_ == 0 {
                        v___x_2600_ = v___x_2589_;
                        v_isShared_2601_ = v_isSharedCheck_2605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2598_);
                        crate::leanh::lean_dec(v___x_2589_);
                        v___x_2600_ = crate::leanh::lean_box(0);
                        v_isShared_2601_ = v_isSharedCheck_2605_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2601_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2600_, 0);
                    v___x_2603_ = v___x_2600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_val_2598_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_getType___boxed(
    mut v_x_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2612_ = l_Lean_IR_Checker_getType(v_x_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
    crate::leanh::lean_dec(v_a_2610_);
    crate::leanh::lean_dec_ref(v_a_2609_);
    crate::leanh::lean_dec(v_a_2608_);
    crate::leanh::lean_dec_ref(v_a_2607_);
    return v_res_2612_;
}
pub unsafe fn l_Lean_IR_Checker_checkVarType(
    mut v_x_2613_: *mut crate::leanh::LeanObject,
    mut v_p_2614_: *mut crate::leanh::LeanObject,
    mut v_suffix_x3f_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: u8 = 0;
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2646_: u8 = 0;
    let mut v_a_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2650_: u8 = 0;
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2621_ = l_Lean_IR_Checker_getType(
                    v_x_2613_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_,
                );
                if crate::leanh::lean_obj_tag(v___x_2621_) == 0 {
                    v_a_2622_ = crate::leanh::lean_ctor_get(v___x_2621_, 0);
                    v_isSharedCheck_2646_ = (!crate::leanh::lean_is_exclusive(v___x_2621_)) as u8;
                    if v_isSharedCheck_2646_ == 0 {
                        v___x_2624_ = v___x_2621_;
                        v_isShared_2625_ = v_isSharedCheck_2646_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2622_);
                        crate::leanh::lean_dec(v___x_2621_);
                        v___x_2624_ = crate::leanh::lean_box(0);
                        v_isShared_2625_ = v_isSharedCheck_2646_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_2614_);
                    v_a_2647_ = crate::leanh::lean_ctor_get(v___x_2621_, 0);
                    v_isSharedCheck_2654_ = (!crate::leanh::lean_is_exclusive(v___x_2621_)) as u8;
                    if v_isSharedCheck_2654_ == 0 {
                        v___x_2649_ = v___x_2621_;
                        v_isShared_2650_ = v_isSharedCheck_2654_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2647_);
                        crate::leanh::lean_dec(v___x_2621_);
                        v___x_2649_ = crate::leanh::lean_box(0);
                        v_isShared_2650_ = v_isSharedCheck_2654_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2622_);
                v___x_2626_ = crate::leanh::lean_apply_1(v_p_2614_, v_a_2622_);
                v___x_2627_ = (crate::leanh::lean_unbox(v___x_2626_) as u8);
                if v___x_2627_ == 0 {
                    crate::leanh::lean_del_object(v___x_2624_);
                    v___x_2628_ = l_Lean_IR_Checker_checkType___closed__0;
                    v___x_2629_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_2622_);
                    v___x_2630_ = l_Std_Format_defWidth;
                    v___x_2631_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2632_ =
                        l_Std_Format_pretty(v___x_2629_, v___x_2630_, v___x_2631_, v___x_2631_);
                    v___x_2633_ = lean_string_append(v___x_2628_, v___x_2632_);
                    crate::leanh::lean_dec_ref(v___x_2632_);
                    v___x_2634_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v_msg_2635_ = lean_string_append(v___x_2633_, v___x_2634_);
                    if crate::leanh::lean_obj_tag(v_suffix_x3f_2615_) == 1 {
                        v_val_2636_ = crate::leanh::lean_ctor_get(v_suffix_x3f_2615_, 0);
                        v___x_2637_ = l_Lean_IR_Checker_checkType___closed__1;
                        v___x_2638_ = lean_string_append(v_msg_2635_, v___x_2637_);
                        v_msg_2639_ = lean_string_append(v___x_2638_, v_val_2636_);
                        v___x_2640_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                            v_msg_2639_,
                            v_a_2616_,
                            v_a_2617_,
                            v_a_2618_,
                            v_a_2619_,
                        );
                        return v___x_2640_;
                    } else {
                        v___x_2641_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                            v_msg_2635_,
                            v_a_2616_,
                            v_a_2617_,
                            v_a_2618_,
                            v_a_2619_,
                        );
                        return v___x_2641_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2622_);
                    v___x_2642_ = crate::leanh::lean_box(0);
                    if v_isShared_2625_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2624_, 0, v___x_2642_);
                        v___x_2644_ = v___x_2624_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
                        v___x_2644_ = v_reuseFailAlloc_2645_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2644_;
            }
            3 => {
                if v_isShared_2650_ == 0 {
                    v___x_2652_ = v___x_2649_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
                    v___x_2652_ = v_reuseFailAlloc_2653_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkVarType___boxed(
    mut v_x_2655_: *mut crate::leanh::LeanObject,
    mut v_p_2656_: *mut crate::leanh::LeanObject,
    mut v_suffix_x3f_2657_: *mut crate::leanh::LeanObject,
    mut v_a_2658_: *mut crate::leanh::LeanObject,
    mut v_a_2659_: *mut crate::leanh::LeanObject,
    mut v_a_2660_: *mut crate::leanh::LeanObject,
    mut v_a_2661_: *mut crate::leanh::LeanObject,
    mut v_a_2662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2663_ = l_Lean_IR_Checker_checkVarType(
        v_x_2655_,
        v_p_2656_,
        v_suffix_x3f_2657_,
        v_a_2658_,
        v_a_2659_,
        v_a_2660_,
        v_a_2661_,
    );
    crate::leanh::lean_dec(v_a_2661_);
    crate::leanh::lean_dec_ref(v_a_2660_);
    crate::leanh::lean_dec(v_a_2659_);
    crate::leanh::lean_dec_ref(v_a_2658_);
    crate::leanh::lean_dec(v_suffix_x3f_2657_);
    return v_res_2663_;
}
pub unsafe fn l_Lean_IR_Checker_checkObjVar(
    mut v_x_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2675_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_a_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2670_ = l_Lean_IR_Checker_getType(
                    v_x_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_,
                );
                if crate::leanh::lean_obj_tag(v___x_2670_) == 0 {
                    v_a_2671_ = crate::leanh::lean_ctor_get(v___x_2670_, 0);
                    v_isSharedCheck_2693_ = (!crate::leanh::lean_is_exclusive(v___x_2670_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v___x_2673_ = v___x_2670_;
                        v_isShared_2674_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2671_);
                        crate::leanh::lean_dec(v___x_2670_);
                        v___x_2673_ = crate::leanh::lean_box(0);
                        v_isShared_2674_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2694_ = crate::leanh::lean_ctor_get(v___x_2670_, 0);
                    v_isSharedCheck_2701_ = (!crate::leanh::lean_is_exclusive(v___x_2670_)) as u8;
                    if v_isSharedCheck_2701_ == 0 {
                        v___x_2696_ = v___x_2670_;
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2694_);
                        crate::leanh::lean_dec(v___x_2670_);
                        v___x_2696_ = crate::leanh::lean_box(0);
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2675_ = l_Lean_IR_IRType_isObj(v_a_2671_);
                if v___x_2675_ == 0 {
                    crate::leanh::lean_del_object(v___x_2673_);
                    v___x_2676_ = l_Lean_IR_Checker_checkObjType___closed__0;
                    v___x_2677_ = l_Lean_IR_Checker_checkType___closed__0;
                    v___x_2678_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_2671_);
                    v___x_2679_ = l_Std_Format_defWidth;
                    v___x_2680_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2681_ =
                        l_Std_Format_pretty(v___x_2678_, v___x_2679_, v___x_2680_, v___x_2680_);
                    v___x_2682_ = lean_string_append(v___x_2677_, v___x_2681_);
                    crate::leanh::lean_dec_ref(v___x_2681_);
                    v___x_2683_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v_msg_2684_ = lean_string_append(v___x_2682_, v___x_2683_);
                    v___x_2685_ = l_Lean_IR_Checker_checkType___closed__1;
                    v___x_2686_ = lean_string_append(v_msg_2684_, v___x_2685_);
                    v_msg_2687_ = lean_string_append(v___x_2686_, v___x_2676_);
                    v___x_2688_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v_msg_2687_,
                        v_a_2665_,
                        v_a_2666_,
                        v_a_2667_,
                        v_a_2668_,
                    );
                    return v___x_2688_;
                } else {
                    crate::leanh::lean_dec(v_a_2671_);
                    v___x_2689_ = crate::leanh::lean_box(0);
                    if v_isShared_2674_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2673_, 0, v___x_2689_);
                        v___x_2691_ = v___x_2673_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
                        v___x_2691_ = v_reuseFailAlloc_2692_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2691_;
            }
            3 => {
                if v_isShared_2697_ == 0 {
                    v___x_2699_ = v___x_2696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
                    v___x_2699_ = v_reuseFailAlloc_2700_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkObjVar___boxed(
    mut v_x_2702_: *mut crate::leanh::LeanObject,
    mut v_a_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ =
        l_Lean_IR_Checker_checkObjVar(v_x_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
    crate::leanh::lean_dec(v_a_2706_);
    crate::leanh::lean_dec_ref(v_a_2705_);
    crate::leanh::lean_dec(v_a_2704_);
    crate::leanh::lean_dec_ref(v_a_2703_);
    return v_res_2708_;
}
pub unsafe fn l_Lean_IR_Checker_checkScalarVar(
    mut v_x_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2715_ = l_Lean_IR_Checker_getType(
                    v_x_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_,
                );
                if crate::leanh::lean_obj_tag(v___x_2715_) == 0 {
                    v_a_2716_ = crate::leanh::lean_ctor_get(v___x_2715_, 0);
                    v_isSharedCheck_2738_ = (!crate::leanh::lean_is_exclusive(v___x_2715_)) as u8;
                    if v_isSharedCheck_2738_ == 0 {
                        v___x_2718_ = v___x_2715_;
                        v_isShared_2719_ = v_isSharedCheck_2738_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2716_);
                        crate::leanh::lean_dec(v___x_2715_);
                        v___x_2718_ = crate::leanh::lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2738_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2739_ = crate::leanh::lean_ctor_get(v___x_2715_, 0);
                    v_isSharedCheck_2746_ = (!crate::leanh::lean_is_exclusive(v___x_2715_)) as u8;
                    if v_isSharedCheck_2746_ == 0 {
                        v___x_2741_ = v___x_2715_;
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2739_);
                        crate::leanh::lean_dec(v___x_2715_);
                        v___x_2741_ = crate::leanh::lean_box(0);
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2720_ = l_Lean_IR_IRType_isScalar(v_a_2716_);
                if v___x_2720_ == 0 {
                    crate::leanh::lean_del_object(v___x_2718_);
                    v___x_2721_ = l_Lean_IR_Checker_checkScalarType___closed__0;
                    v___x_2722_ = l_Lean_IR_Checker_checkType___closed__0;
                    v___x_2723_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_2716_);
                    v___x_2724_ = l_Std_Format_defWidth;
                    v___x_2725_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2726_ =
                        l_Std_Format_pretty(v___x_2723_, v___x_2724_, v___x_2725_, v___x_2725_);
                    v___x_2727_ = lean_string_append(v___x_2722_, v___x_2726_);
                    crate::leanh::lean_dec_ref(v___x_2726_);
                    v___x_2728_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v_msg_2729_ = lean_string_append(v___x_2727_, v___x_2728_);
                    v___x_2730_ = l_Lean_IR_Checker_checkType___closed__1;
                    v___x_2731_ = lean_string_append(v_msg_2729_, v___x_2730_);
                    v_msg_2732_ = lean_string_append(v___x_2731_, v___x_2721_);
                    v___x_2733_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v_msg_2732_,
                        v_a_2710_,
                        v_a_2711_,
                        v_a_2712_,
                        v_a_2713_,
                    );
                    return v___x_2733_;
                } else {
                    crate::leanh::lean_dec(v_a_2716_);
                    v___x_2734_ = crate::leanh::lean_box(0);
                    if v_isShared_2719_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2718_, 0, v___x_2734_);
                        v___x_2736_ = v___x_2718_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
                        v___x_2736_ = v_reuseFailAlloc_2737_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2736_;
            }
            3 => {
                if v_isShared_2742_ == 0 {
                    v___x_2744_ = v___x_2741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkScalarVar___boxed(
    mut v_x_2747_: *mut crate::leanh::LeanObject,
    mut v_a_2748_: *mut crate::leanh::LeanObject,
    mut v_a_2749_: *mut crate::leanh::LeanObject,
    mut v_a_2750_: *mut crate::leanh::LeanObject,
    mut v_a_2751_: *mut crate::leanh::LeanObject,
    mut v_a_2752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2753_ =
        l_Lean_IR_Checker_checkScalarVar(v_x_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
    crate::leanh::lean_dec(v_a_2751_);
    crate::leanh::lean_dec_ref(v_a_2750_);
    crate::leanh::lean_dec(v_a_2749_);
    crate::leanh::lean_dec_ref(v_a_2748_);
    return v_res_2753_;
}
pub unsafe fn l_Lean_IR_Checker_checkFullApp(
    mut v_c_2758_: *mut crate::leanh::LeanObject,
    mut v_ys_2759_: *mut crate::leanh::LeanObject,
    mut v_a_2760_: *mut crate::leanh::LeanObject,
    mut v_a_2761_: *mut crate::leanh::LeanObject,
    mut v_a_2762_: *mut crate::leanh::LeanObject,
    mut v_a_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: u8 = 0;
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_c_2758_);
                v___x_2765_ = l_Lean_IR_Checker_getDecl(
                    v_c_2758_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_,
                );
                if crate::leanh::lean_obj_tag(v___x_2765_) == 0 {
                    v_a_2766_ = crate::leanh::lean_ctor_get(v___x_2765_, 0);
                    crate::leanh::lean_inc(v_a_2766_);
                    crate::leanh::lean_dec_ref_known(v___x_2765_, 1);
                    v___x_2767_ = lean_array_get_size(v_ys_2759_);
                    v___x_2768_ = l_Lean_IR_Decl_params(v_a_2766_);
                    crate::leanh::lean_dec(v_a_2766_);
                    v___x_2769_ = lean_array_get_size(v___x_2768_);
                    crate::leanh::lean_dec_ref(v___x_2768_);
                    v___x_2770_ = lean_nat_dec_eq(v___x_2767_, v___x_2769_);
                    if v___x_2770_ == 0 {
                        v___x_2771_ = l_Lean_IR_Checker_checkFullApp___closed__0;
                        v___x_2772_ = 1;
                        v___x_2773_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_c_2758_,
                                v___x_2772_,
                            );
                        v___x_2774_ = lean_string_append(v___x_2771_, v___x_2773_);
                        crate::leanh::lean_dec_ref(v___x_2773_);
                        v___x_2775_ = l_Lean_IR_Checker_checkFullApp___closed__1;
                        v___x_2776_ = lean_string_append(v___x_2774_, v___x_2775_);
                        v___x_2777_ = l_Nat_reprFast(v___x_2767_);
                        v___x_2778_ = lean_string_append(v___x_2776_, v___x_2777_);
                        crate::leanh::lean_dec_ref(v___x_2777_);
                        v___x_2779_ = l_Lean_IR_Checker_checkFullApp___closed__2;
                        v___x_2780_ = lean_string_append(v___x_2778_, v___x_2779_);
                        v___x_2781_ = l_Nat_reprFast(v___x_2769_);
                        v___x_2782_ = lean_string_append(v___x_2780_, v___x_2781_);
                        crate::leanh::lean_dec_ref(v___x_2781_);
                        v___x_2783_ = l_Lean_IR_Checker_checkFullApp___closed__3;
                        v___x_2784_ = lean_string_append(v___x_2782_, v___x_2783_);
                        v___x_2785_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                            v___x_2784_,
                            v_a_2760_,
                            v_a_2761_,
                            v_a_2762_,
                            v_a_2763_,
                        );
                        return v___x_2785_;
                    } else {
                        crate::leanh::lean_dec(v_c_2758_);
                        v___x_2786_ = l_Lean_IR_Checker_checkArgs(
                            v_ys_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_,
                        );
                        return v___x_2786_;
                    }
                } else {
                    crate::leanh::lean_dec(v_c_2758_);
                    v_a_2787_ = crate::leanh::lean_ctor_get(v___x_2765_, 0);
                    v_isSharedCheck_2794_ = (!crate::leanh::lean_is_exclusive(v___x_2765_)) as u8;
                    if v_isSharedCheck_2794_ == 0 {
                        v___x_2789_ = v___x_2765_;
                        v_isShared_2790_ = v_isSharedCheck_2794_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2787_);
                        crate::leanh::lean_dec(v___x_2765_);
                        v___x_2789_ = crate::leanh::lean_box(0);
                        v_isShared_2790_ = v_isSharedCheck_2794_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2790_ == 0 {
                    v___x_2792_ = v___x_2789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
                    v___x_2792_ = v_reuseFailAlloc_2793_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkFullApp___boxed(
    mut v_c_2795_: *mut crate::leanh::LeanObject,
    mut v_ys_2796_: *mut crate::leanh::LeanObject,
    mut v_a_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v_a_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2802_ = l_Lean_IR_Checker_checkFullApp(
        v_c_2795_, v_ys_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_,
    );
    crate::leanh::lean_dec(v_a_2800_);
    crate::leanh::lean_dec_ref(v_a_2799_);
    crate::leanh::lean_dec(v_a_2798_);
    crate::leanh::lean_dec_ref(v_a_2797_);
    crate::leanh::lean_dec_ref(v_ys_2796_);
    return v_res_2802_;
}
pub unsafe fn l_Lean_IR_Checker_checkPartialApp(
    mut v_c_2806_: *mut crate::leanh::LeanObject,
    mut v_ys_2807_: *mut crate::leanh::LeanObject,
    mut v_a_2808_: *mut crate::leanh::LeanObject,
    mut v_a_2809_: *mut crate::leanh::LeanObject,
    mut v_a_2810_: *mut crate::leanh::LeanObject,
    mut v_a_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_c_2806_);
                v___x_2813_ = l_Lean_IR_Checker_getDecl(
                    v_c_2806_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_,
                );
                if crate::leanh::lean_obj_tag(v___x_2813_) == 0 {
                    v_a_2814_ = crate::leanh::lean_ctor_get(v___x_2813_, 0);
                    crate::leanh::lean_inc(v_a_2814_);
                    crate::leanh::lean_dec_ref_known(v___x_2813_, 1);
                    v___x_2815_ = lean_array_get_size(v_ys_2807_);
                    v___x_2816_ = l_Lean_IR_Decl_params(v_a_2814_);
                    crate::leanh::lean_dec(v_a_2814_);
                    v___x_2817_ = lean_array_get_size(v___x_2816_);
                    crate::leanh::lean_dec_ref(v___x_2816_);
                    v___x_2818_ = lean_nat_dec_lt(v___x_2815_, v___x_2817_);
                    if v___x_2818_ == 0 {
                        v___x_2819_ = l_Lean_IR_Checker_checkPartialApp___closed__0;
                        v___x_2820_ = 1;
                        v___x_2821_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_c_2806_,
                                v___x_2820_,
                            );
                        v___x_2822_ = lean_string_append(v___x_2819_, v___x_2821_);
                        crate::leanh::lean_dec_ref(v___x_2821_);
                        v___x_2823_ = l_Lean_IR_Checker_checkPartialApp___closed__1;
                        v___x_2824_ = lean_string_append(v___x_2822_, v___x_2823_);
                        v___x_2825_ = l_Nat_reprFast(v___x_2815_);
                        v___x_2826_ = lean_string_append(v___x_2824_, v___x_2825_);
                        crate::leanh::lean_dec_ref(v___x_2825_);
                        v___x_2827_ = l_Lean_IR_Checker_checkPartialApp___closed__2;
                        v___x_2828_ = lean_string_append(v___x_2826_, v___x_2827_);
                        v___x_2829_ = l_Nat_reprFast(v___x_2817_);
                        v___x_2830_ = lean_string_append(v___x_2828_, v___x_2829_);
                        crate::leanh::lean_dec_ref(v___x_2829_);
                        v___x_2831_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                            v___x_2830_,
                            v_a_2808_,
                            v_a_2809_,
                            v_a_2810_,
                            v_a_2811_,
                        );
                        return v___x_2831_;
                    } else {
                        crate::leanh::lean_dec(v_c_2806_);
                        v___x_2832_ = l_Lean_IR_Checker_checkArgs(
                            v_ys_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_,
                        );
                        return v___x_2832_;
                    }
                } else {
                    crate::leanh::lean_dec(v_c_2806_);
                    v_a_2833_ = crate::leanh::lean_ctor_get(v___x_2813_, 0);
                    v_isSharedCheck_2840_ = (!crate::leanh::lean_is_exclusive(v___x_2813_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v___x_2835_ = v___x_2813_;
                        v_isShared_2836_ = v_isSharedCheck_2840_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2833_);
                        crate::leanh::lean_dec(v___x_2813_);
                        v___x_2835_ = crate::leanh::lean_box(0);
                        v_isShared_2836_ = v_isSharedCheck_2840_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2836_ == 0 {
                    v___x_2838_ = v___x_2835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
                    v___x_2838_ = v_reuseFailAlloc_2839_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkPartialApp___boxed(
    mut v_c_2841_: *mut crate::leanh::LeanObject,
    mut v_ys_2842_: *mut crate::leanh::LeanObject,
    mut v_a_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
    mut v_a_2845_: *mut crate::leanh::LeanObject,
    mut v_a_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Lean_IR_Checker_checkPartialApp(
        v_c_2841_, v_ys_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_,
    );
    crate::leanh::lean_dec(v_a_2846_);
    crate::leanh::lean_dec_ref(v_a_2845_);
    crate::leanh::lean_dec(v_a_2844_);
    crate::leanh::lean_dec_ref(v_a_2843_);
    crate::leanh::lean_dec_ref(v_ys_2842_);
    return v_res_2848_;
}
pub unsafe fn l_Lean_IR_Checker_checkExpr(
    mut v_ty_2856_: *mut crate::leanh::LeanObject,
    mut v_e_2857_: *mut crate::leanh::LeanObject,
    mut v_a_2858_: *mut crate::leanh::LeanObject,
    mut v_a_2859_: *mut crate::leanh::LeanObject,
    mut v_a_2860_: *mut crate::leanh::LeanObject,
    mut v_a_2861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2910_: u8 = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: u8 = 0;
    let mut v_x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2934_: u8 = 0;
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_types_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: u8 = 0;
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_types_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: u8 = 0;
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_a_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2980_: u8 = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v_x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_unused_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3031_: u8 = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_a_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3049_: u8 = 0;
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3053_: u8 = 0;
    let mut v_x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3066_: u8 = 0;
    let mut v_x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3087_: u8 = 0;
    let mut v_unused_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_2857_) {
                0 => {
                    v_i_2863_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc_ref(v_i_2863_);
                    v_ys_2864_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc_ref(v_ys_2864_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v_name_2875_ = crate::leanh::lean_ctor_get(v_i_2863_, 0);
                    v_cidx_2876_ = crate::leanh::lean_ctor_get(v_i_2863_, 1);
                    v_size_2877_ = crate::leanh::lean_ctor_get(v_i_2863_, 2);
                    v_usize_2878_ = crate::leanh::lean_ctor_get(v_i_2863_, 3);
                    v_ssize_2879_ = crate::leanh::lean_ctor_get(v_i_2863_, 4);
                    v___x_2917_ = l_Lean_IR_Checker_maxCtorTag;
                    v___x_2918_ = lean_nat_dec_lt(v___x_2917_, v_cidx_2876_);
                    if v___x_2918_ == 0 {
                        v___y_2910_ = v___x_2918_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2919_ = l_Lean_IR_CtorInfo_isRef(v_i_2863_);
                        v___y_2910_ = v___x_2919_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v_x_2920_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc(v_x_2920_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v___x_2921_ = l_Lean_IR_Checker_checkObjVar(
                        v_x_2920_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2921_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2921_, 1);
                        v___x_2922_ = l_Lean_IR_Checker_checkObjType(
                            v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                        );
                        return v___x_2922_;
                    } else {
                        crate::leanh::lean_dec(v_ty_2856_);
                        return v___x_2921_;
                    }
                }
                2 => {
                    v_x_2923_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_x_2923_);
                    v_ys_2924_ = crate::leanh::lean_ctor_get(v_e_2857_, 2);
                    crate::leanh::lean_inc_ref(v_ys_2924_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 3);
                    v___x_2925_ = l_Lean_IR_Checker_checkObjVar(
                        v_x_2923_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2925_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2925_, 1);
                        v___x_2926_ = l_Lean_IR_Checker_checkArgs(
                            v_ys_2924_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                        );
                        crate::leanh::lean_dec_ref(v_ys_2924_);
                        if crate::leanh::lean_obj_tag(v___x_2926_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2926_, 1);
                            v___x_2927_ = l_Lean_IR_Checker_checkObjType(
                                v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                            );
                            return v___x_2927_;
                        } else {
                            crate::leanh::lean_dec(v_ty_2856_);
                            return v___x_2926_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ys_2924_);
                        crate::leanh::lean_dec(v_ty_2856_);
                        return v___x_2925_;
                    }
                }
                3 => {
                    v_i_2928_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_i_2928_);
                    v_x_2929_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc(v_x_2929_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v___x_2930_ = l_Lean_IR_Checker_getType(
                        v_x_2929_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2930_) == 0 {
                        v_a_2931_ = crate::leanh::lean_ctor_get(v___x_2930_, 0);
                        v_isSharedCheck_2976_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2930_)) as u8;
                        if v_isSharedCheck_2976_ == 0 {
                            v___x_2933_ = v___x_2930_;
                            v_isShared_2934_ = v_isSharedCheck_2976_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2931_);
                            crate::leanh::lean_dec(v___x_2930_);
                            v___x_2933_ = crate::leanh::lean_box(0);
                            v_isShared_2934_ = v_isSharedCheck_2976_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_2928_);
                        crate::leanh::lean_dec(v_ty_2856_);
                        v_a_2977_ = crate::leanh::lean_ctor_get(v___x_2930_, 0);
                        v_isSharedCheck_2984_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2930_)) as u8;
                        if v_isSharedCheck_2984_ == 0 {
                            v___x_2979_ = v___x_2930_;
                            v_isShared_2980_ = v_isSharedCheck_2984_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2977_);
                            crate::leanh::lean_dec(v___x_2930_);
                            v___x_2979_ = crate::leanh::lean_box(0);
                            v_isShared_2980_ = v_isSharedCheck_2984_;
                            state = 9;
                            continue;
                        }
                    }
                }
                4 => {
                    v_x_2985_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc(v_x_2985_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v___x_2986_ = l_Lean_IR_Checker_checkObjVar(
                        v_x_2985_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2986_) == 0 {
                        v_isSharedCheck_3005_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2986_)) as u8;
                        if v_isSharedCheck_3005_ == 0 {
                            v_unused_3006_ = crate::leanh::lean_ctor_get(v___x_2986_, 0);
                            crate::leanh::lean_dec(v_unused_3006_);
                            v___x_2988_ = v___x_2986_;
                            v_isShared_2989_ = v_isSharedCheck_3005_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2986_);
                            v___x_2988_ = crate::leanh::lean_box(0);
                            v_isShared_2989_ = v_isSharedCheck_3005_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_ty_2856_);
                        return v___x_2986_;
                    }
                }
                5 => {
                    v_x_3007_ = crate::leanh::lean_ctor_get(v_e_2857_, 2);
                    crate::leanh::lean_inc(v_x_3007_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 3);
                    v___x_3008_ = l_Lean_IR_Checker_checkObjVar(
                        v_x_3007_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3008_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3008_, 1);
                        v___x_3009_ = l_Lean_IR_Checker_checkScalarType(
                            v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                        );
                        return v___x_3009_;
                    } else {
                        crate::leanh::lean_dec(v_ty_2856_);
                        return v___x_3008_;
                    }
                }
                6 => {
                    crate::leanh::lean_dec(v_ty_2856_);
                    v_c_3010_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_c_3010_);
                    v_ys_3011_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc_ref(v_ys_3011_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v___x_3012_ = l_Lean_IR_Checker_checkFullApp(
                        v_c_3010_, v_ys_3011_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    crate::leanh::lean_dec_ref(v_ys_3011_);
                    return v___x_3012_;
                }
                7 => {
                    v_c_3013_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_c_3013_);
                    v_ys_3014_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc_ref(v_ys_3014_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v___x_3015_ = l_Lean_IR_Checker_checkPartialApp(
                        v_c_3013_, v_ys_3014_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    crate::leanh::lean_dec_ref(v_ys_3014_);
                    if crate::leanh::lean_obj_tag(v___x_3015_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3015_, 1);
                        v___x_3016_ = l_Lean_IR_Checker_checkObjType(
                            v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                        );
                        return v___x_3016_;
                    } else {
                        crate::leanh::lean_dec(v_ty_2856_);
                        return v___x_3015_;
                    }
                }
                8 => {
                    v_x_3017_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_x_3017_);
                    v_ys_3018_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc_ref(v_ys_3018_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v___x_3019_ = l_Lean_IR_Checker_checkObjVar(
                        v_x_3017_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3019_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3019_, 1);
                        v___x_3020_ = l_Lean_IR_Checker_checkArgs(
                            v_ys_3018_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                        );
                        crate::leanh::lean_dec_ref(v_ys_3018_);
                        if crate::leanh::lean_obj_tag(v___x_3020_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3020_, 1);
                            v___x_3021_ = l_Lean_IR_Checker_checkObjType(
                                v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                            );
                            return v___x_3021_;
                        } else {
                            crate::leanh::lean_dec(v_ty_2856_);
                            return v___x_3020_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ys_3018_);
                        crate::leanh::lean_dec(v_ty_2856_);
                        return v___x_3019_;
                    }
                }
                9 => {
                    v_ty_3022_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_ty_3022_);
                    v_x_3023_ = crate::leanh::lean_ctor_get(v_e_2857_, 1);
                    crate::leanh::lean_inc(v_x_3023_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 2);
                    v___x_3024_ = l_Lean_IR_Checker_checkObjType(
                        v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3024_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3024_, 1);
                        crate::leanh::lean_inc(v_x_3023_);
                        v___x_3025_ = l_Lean_IR_Checker_checkScalarVar(
                            v_x_3023_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3025_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3025_, 1);
                            v___x_3026_ = l_Lean_IR_Checker_getType(
                                v_x_3023_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3026_) == 0 {
                                v_a_3027_ = crate::leanh::lean_ctor_get(v___x_3026_, 0);
                                v_isSharedCheck_3045_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3026_)) as u8;
                                if v_isSharedCheck_3045_ == 0 {
                                    v___x_3029_ = v___x_3026_;
                                    v_isShared_3030_ = v_isSharedCheck_3045_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3027_);
                                    crate::leanh::lean_dec(v___x_3026_);
                                    v___x_3029_ = crate::leanh::lean_box(0);
                                    v_isShared_3030_ = v_isSharedCheck_3045_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_ty_3022_);
                                v_a_3046_ = crate::leanh::lean_ctor_get(v___x_3026_, 0);
                                v_isSharedCheck_3053_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3026_)) as u8;
                                if v_isSharedCheck_3053_ == 0 {
                                    v___x_3048_ = v___x_3026_;
                                    v_isShared_3049_ = v_isSharedCheck_3053_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3046_);
                                    crate::leanh::lean_dec(v___x_3026_);
                                    v___x_3048_ = crate::leanh::lean_box(0);
                                    v_isShared_3049_ = v_isSharedCheck_3053_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_x_3023_);
                            crate::leanh::lean_dec(v_ty_3022_);
                            return v___x_3025_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_3023_);
                        crate::leanh::lean_dec(v_ty_3022_);
                        return v___x_3024_;
                    }
                }
                10 => {
                    v_x_3054_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_x_3054_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 1);
                    v___x_3055_ = l_Lean_IR_Checker_checkScalarType(
                        v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3055_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3055_, 1);
                        v___x_3056_ = l_Lean_IR_Checker_checkObjVar(
                            v_x_3054_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                        );
                        return v___x_3056_;
                    } else {
                        crate::leanh::lean_dec(v_x_3054_);
                        return v___x_3055_;
                    }
                }
                11 => {
                    v_v_3057_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    v_isSharedCheck_3066_ = (!crate::leanh::lean_is_exclusive(v_e_2857_)) as u8;
                    if v_isSharedCheck_3066_ == 0 {
                        v___x_3059_ = v_e_2857_;
                        v_isShared_3060_ = v_isSharedCheck_3066_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_3057_);
                        crate::leanh::lean_dec(v_e_2857_);
                        v___x_3059_ = crate::leanh::lean_box(0);
                        v_isShared_3060_ = v_isSharedCheck_3066_;
                        state = 17;
                        continue;
                    }
                }
                _ => {
                    v_x_3067_ = crate::leanh::lean_ctor_get(v_e_2857_, 0);
                    crate::leanh::lean_inc(v_x_3067_);
                    crate::leanh::lean_dec_ref_known(v_e_2857_, 1);
                    v___x_3068_ = l_Lean_IR_Checker_checkObjVar(
                        v_x_3067_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3068_) == 0 {
                        v_isSharedCheck_3087_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3068_)) as u8;
                        if v_isSharedCheck_3087_ == 0 {
                            v_unused_3088_ = crate::leanh::lean_ctor_get(v___x_3068_, 0);
                            crate::leanh::lean_dec(v_unused_3088_);
                            v___x_3070_ = v___x_3068_;
                            v_isShared_3071_ = v_isSharedCheck_3087_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3068_);
                            v___x_3070_ = crate::leanh::lean_box(0);
                            v_isShared_3071_ = v_isSharedCheck_3087_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_ty_2856_);
                        return v___x_3068_;
                    }
                }
            },
            1 => {
                v___x_2870_ = l_Lean_IR_CtorInfo_isRef(v_i_2863_);
                crate::leanh::lean_dec_ref(v_i_2863_);
                if v___x_2870_ == 0 {
                    crate::leanh::lean_dec_ref(v_ys_2864_);
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_2871_ = crate::leanh::lean_box(0);
                    v___x_2872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2872_, 0, v___x_2871_);
                    return v___x_2872_;
                } else {
                    v___x_2873_ = l_Lean_IR_Checker_checkObjType(
                        v_ty_2856_,
                        v___y_2866_,
                        v___y_2867_,
                        v___y_2868_,
                        v___y_2869_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2873_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2873_, 1);
                        v___x_2874_ = l_Lean_IR_Checker_checkArgs(
                            v_ys_2864_,
                            v___y_2866_,
                            v___y_2867_,
                            v___y_2868_,
                            v___y_2869_,
                        );
                        crate::leanh::lean_dec_ref(v_ys_2864_);
                        return v___x_2874_;
                    } else {
                        crate::leanh::lean_dec_ref(v_ys_2864_);
                        return v___x_2873_;
                    }
                }
            }
            2 => {
                v___x_2885_ = l_Lean_IR_Checker_maxCtorScalarsSize;
                v___x_2886_ = l_Lean_IR_Checker_usizeSize;
                v___x_2887_ = lean_nat_mul(v_usize_2878_, v___x_2886_);
                v___x_2888_ = lean_nat_add(v_ssize_2879_, v___x_2887_);
                crate::leanh::lean_dec(v___x_2887_);
                v___x_2889_ = lean_nat_dec_lt(v___x_2885_, v___x_2888_);
                crate::leanh::lean_dec(v___x_2888_);
                if v___x_2889_ == 0 {
                    v___y_2866_ = v___y_2881_;
                    v___y_2867_ = v___y_2882_;
                    v___y_2868_ = v___y_2883_;
                    v___y_2869_ = v___y_2884_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2875_);
                    crate::leanh::lean_dec_ref(v_ys_2864_);
                    crate::leanh::lean_dec_ref(v_i_2863_);
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_2890_ = l_Lean_IR_Checker_checkExpr___closed__0;
                    v___x_2891_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_2875_,
                        v___x_2889_,
                    );
                    v___x_2892_ = lean_string_append(v___x_2890_, v___x_2891_);
                    crate::leanh::lean_dec_ref(v___x_2891_);
                    v___x_2893_ = l_Lean_IR_Checker_checkExpr___closed__1;
                    v___x_2894_ = lean_string_append(v___x_2892_, v___x_2893_);
                    v___x_2895_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2894_,
                        v___y_2881_,
                        v___y_2882_,
                        v___y_2883_,
                        v___y_2884_,
                    );
                    return v___x_2895_;
                }
            }
            3 => {
                v___x_2901_ = l_Lean_IR_Checker_maxCtorFields;
                v___x_2902_ = lean_nat_dec_lt(v___x_2901_, v_size_2877_);
                if v___x_2902_ == 0 {
                    v___y_2881_ = v___y_2897_;
                    v___y_2882_ = v___y_2898_;
                    v___y_2883_ = v___y_2899_;
                    v___y_2884_ = v___y_2900_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2875_);
                    crate::leanh::lean_dec_ref(v_ys_2864_);
                    crate::leanh::lean_dec_ref(v_i_2863_);
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_2903_ = l_Lean_IR_Checker_checkExpr___closed__0;
                    v___x_2904_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_2875_,
                        v___x_2902_,
                    );
                    v___x_2905_ = lean_string_append(v___x_2903_, v___x_2904_);
                    crate::leanh::lean_dec_ref(v___x_2904_);
                    v___x_2906_ = l_Lean_IR_Checker_checkExpr___closed__2;
                    v___x_2907_ = lean_string_append(v___x_2905_, v___x_2906_);
                    v___x_2908_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2907_,
                        v___y_2897_,
                        v___y_2898_,
                        v___y_2899_,
                        v___y_2900_,
                    );
                    return v___x_2908_;
                }
            }
            4 => {
                if v___y_2910_ == 0 {
                    v___y_2897_ = v_a_2858_;
                    v___y_2898_ = v_a_2859_;
                    v___y_2899_ = v_a_2860_;
                    v___y_2900_ = v_a_2861_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2875_);
                    crate::leanh::lean_dec_ref(v_ys_2864_);
                    crate::leanh::lean_dec_ref(v_i_2863_);
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_2911_ = l_Lean_IR_Checker_checkExpr___closed__3;
                    v___x_2912_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_2875_,
                        v___y_2910_,
                    );
                    v___x_2913_ = lean_string_append(v___x_2911_, v___x_2912_);
                    crate::leanh::lean_dec_ref(v___x_2912_);
                    v___x_2914_ = l_Lean_IR_Checker_checkExpr___closed__4;
                    v___x_2915_ = lean_string_append(v___x_2913_, v___x_2914_);
                    v___x_2916_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2915_,
                        v_a_2858_,
                        v_a_2859_,
                        v_a_2860_,
                        v_a_2861_,
                    );
                    return v___x_2916_;
                }
            }
            5 => match crate::leanh::lean_obj_tag(v_a_2931_) {
                7 => {
                    crate::leanh::lean_del_object(v___x_2933_);
                    crate::leanh::lean_dec(v_i_2928_);
                    v___x_2935_ = l_Lean_IR_Checker_checkObjType(
                        v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    return v___x_2935_;
                }
                8 => {
                    crate::leanh::lean_del_object(v___x_2933_);
                    crate::leanh::lean_dec(v_i_2928_);
                    v___x_2936_ = l_Lean_IR_Checker_checkObjType(
                        v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    return v___x_2936_;
                }
                10 => {
                    v_types_2937_ = crate::leanh::lean_ctor_get(v_a_2931_, 1);
                    crate::leanh::lean_inc_ref(v_types_2937_);
                    crate::leanh::lean_dec_ref_known(v_a_2931_, 2);
                    v___x_2938_ = lean_array_get_size(v_types_2937_);
                    v___x_2939_ = lean_nat_dec_lt(v_i_2928_, v___x_2938_);
                    if v___x_2939_ == 0 {
                        crate::leanh::lean_dec_ref(v_types_2937_);
                        crate::leanh::lean_del_object(v___x_2933_);
                        crate::leanh::lean_dec(v_i_2928_);
                        crate::leanh::lean_dec(v_ty_2856_);
                        v___x_2940_ = l_Lean_IR_Checker_checkExpr___closed__5;
                        v___x_2941_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                            v___x_2940_,
                            v_a_2858_,
                            v_a_2859_,
                            v_a_2860_,
                            v_a_2861_,
                        );
                        return v___x_2941_;
                    } else {
                        v___x_2942_ = lean_array_fget(v_types_2937_, v_i_2928_);
                        crate::leanh::lean_dec(v_i_2928_);
                        crate::leanh::lean_dec_ref(v_types_2937_);
                        v___x_2943_ = l_Lean_IR_instBEqIRType_beq(v___x_2942_, v_ty_2856_);
                        crate::leanh::lean_dec(v_ty_2856_);
                        crate::leanh::lean_dec(v___x_2942_);
                        if v___x_2943_ == 0 {
                            crate::leanh::lean_del_object(v___x_2933_);
                            v___x_2944_ = l_Lean_IR_Checker_checkEqTypes___closed__0;
                            v___x_2945_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                                v___x_2944_,
                                v_a_2858_,
                                v_a_2859_,
                                v_a_2860_,
                                v_a_2861_,
                            );
                            return v___x_2945_;
                        } else {
                            v___x_2946_ = crate::leanh::lean_box(0);
                            if v_isShared_2934_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2946_);
                                v___x_2948_ = v___x_2933_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2949_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
                                v___x_2948_ = v_reuseFailAlloc_2949_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
                11 => {
                    v_types_2950_ = crate::leanh::lean_ctor_get(v_a_2931_, 1);
                    crate::leanh::lean_inc_ref(v_types_2950_);
                    crate::leanh::lean_dec_ref_known(v_a_2931_, 2);
                    v___x_2951_ = lean_array_get_size(v_types_2950_);
                    v___x_2952_ = lean_nat_dec_lt(v_i_2928_, v___x_2951_);
                    if v___x_2952_ == 0 {
                        crate::leanh::lean_dec_ref(v_types_2950_);
                        crate::leanh::lean_del_object(v___x_2933_);
                        crate::leanh::lean_dec(v_i_2928_);
                        crate::leanh::lean_dec(v_ty_2856_);
                        v___x_2953_ = l_Lean_IR_Checker_checkExpr___closed__5;
                        v___x_2954_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                            v___x_2953_,
                            v_a_2858_,
                            v_a_2859_,
                            v_a_2860_,
                            v_a_2861_,
                        );
                        return v___x_2954_;
                    } else {
                        v___x_2955_ = lean_array_fget(v_types_2950_, v_i_2928_);
                        crate::leanh::lean_dec(v_i_2928_);
                        crate::leanh::lean_dec_ref(v_types_2950_);
                        v___x_2956_ = l_Lean_IR_instBEqIRType_beq(v___x_2955_, v_ty_2856_);
                        crate::leanh::lean_dec(v_ty_2856_);
                        crate::leanh::lean_dec(v___x_2955_);
                        if v___x_2956_ == 0 {
                            crate::leanh::lean_del_object(v___x_2933_);
                            v___x_2957_ = l_Lean_IR_Checker_checkEqTypes___closed__0;
                            v___x_2958_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                                v___x_2957_,
                                v_a_2858_,
                                v_a_2859_,
                                v_a_2860_,
                                v_a_2861_,
                            );
                            return v___x_2958_;
                        } else {
                            v___x_2959_ = crate::leanh::lean_box(0);
                            if v_isShared_2934_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2959_);
                                v___x_2961_ = v___x_2933_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_2962_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
                                v___x_2961_ = v_reuseFailAlloc_2962_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
                12 => {
                    crate::leanh::lean_dec(v_i_2928_);
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_2963_ = crate::leanh::lean_box(0);
                    if v_isShared_2934_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2963_);
                        v___x_2965_ = v___x_2933_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
                        v___x_2965_ = v_reuseFailAlloc_2966_;
                        state = 8;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_2933_);
                    crate::leanh::lean_dec(v_i_2928_);
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_2967_ = l_Lean_IR_Checker_checkExpr___closed__6;
                    v___x_2968_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_2931_);
                    v___x_2969_ = l_Std_Format_defWidth;
                    v___x_2970_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2971_ =
                        l_Std_Format_pretty(v___x_2968_, v___x_2969_, v___x_2970_, v___x_2970_);
                    v___x_2972_ = lean_string_append(v___x_2967_, v___x_2971_);
                    crate::leanh::lean_dec_ref(v___x_2971_);
                    v___x_2973_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v___x_2974_ = lean_string_append(v___x_2972_, v___x_2973_);
                    v___x_2975_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v___x_2974_,
                        v_a_2858_,
                        v_a_2859_,
                        v_a_2860_,
                        v_a_2861_,
                    );
                    return v___x_2975_;
                }
            },
            6 => {
                return v___x_2948_;
            }
            7 => {
                return v___x_2961_;
            }
            8 => {
                return v___x_2965_;
            }
            9 => {
                if v_isShared_2980_ == 0 {
                    v___x_2982_ = v___x_2979_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
                    v___x_2982_ = v_reuseFailAlloc_2983_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2982_;
            }
            11 => {
                v___x_2990_ = crate::leanh::lean_box(5);
                v___x_2991_ = l_Lean_IR_instBEqIRType_beq(v_ty_2856_, v___x_2990_);
                if v___x_2991_ == 0 {
                    crate::leanh::lean_del_object(v___x_2988_);
                    v___x_2992_ = l_Lean_IR_Checker_checkType___closed__0;
                    v___x_2993_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2856_);
                    v___x_2994_ = l_Std_Format_defWidth;
                    v___x_2995_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2996_ =
                        l_Std_Format_pretty(v___x_2993_, v___x_2994_, v___x_2995_, v___x_2995_);
                    v___x_2997_ = lean_string_append(v___x_2992_, v___x_2996_);
                    crate::leanh::lean_dec_ref(v___x_2996_);
                    v___x_2998_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v_msg_2999_ = lean_string_append(v___x_2997_, v___x_2998_);
                    v___x_3000_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v_msg_2999_,
                        v_a_2858_,
                        v_a_2859_,
                        v_a_2860_,
                        v_a_2861_,
                    );
                    return v___x_3000_;
                } else {
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_3001_ = crate::leanh::lean_box(0);
                    if v_isShared_2989_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2988_, 0, v___x_3001_);
                        v___x_3003_ = v___x_2988_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
                        v___x_3003_ = v_reuseFailAlloc_3004_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_3003_;
            }
            13 => {
                v___x_3031_ = l_Lean_IR_instBEqIRType_beq(v_a_3027_, v_ty_3022_);
                crate::leanh::lean_dec(v_ty_3022_);
                if v___x_3031_ == 0 {
                    crate::leanh::lean_del_object(v___x_3029_);
                    v___x_3032_ = l_Lean_IR_Checker_checkType___closed__0;
                    v___x_3033_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_3027_);
                    v___x_3034_ = l_Std_Format_defWidth;
                    v___x_3035_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3036_ =
                        l_Std_Format_pretty(v___x_3033_, v___x_3034_, v___x_3035_, v___x_3035_);
                    v___x_3037_ = lean_string_append(v___x_3032_, v___x_3036_);
                    crate::leanh::lean_dec_ref(v___x_3036_);
                    v___x_3038_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v_msg_3039_ = lean_string_append(v___x_3037_, v___x_3038_);
                    v___x_3040_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v_msg_3039_,
                        v_a_2858_,
                        v_a_2859_,
                        v_a_2860_,
                        v_a_2861_,
                    );
                    return v___x_3040_;
                } else {
                    crate::leanh::lean_dec(v_a_3027_);
                    v___x_3041_ = crate::leanh::lean_box(0);
                    if v_isShared_3030_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3029_, 0, v___x_3041_);
                        v___x_3043_ = v___x_3029_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
                        v___x_3043_ = v_reuseFailAlloc_3044_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_3043_;
            }
            15 => {
                if v_isShared_3049_ == 0 {
                    v___x_3051_ = v___x_3048_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3052_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
                    v___x_3051_ = v_reuseFailAlloc_3052_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3051_;
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_v_3057_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_v_3057_, 1);
                    crate::leanh::lean_del_object(v___x_3059_);
                    v___x_3061_ = l_Lean_IR_Checker_checkObjType(
                        v_ty_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_,
                    );
                    return v___x_3061_;
                } else {
                    crate::leanh::lean_dec_ref(v_v_3057_);
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_3062_ = crate::leanh::lean_box(0);
                    if v_isShared_3060_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3059_, 0);
                        crate::leanh::lean_ctor_set(v___x_3059_, 0, v___x_3062_);
                        v___x_3064_ = v___x_3059_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3065_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
                        v___x_3064_ = v_reuseFailAlloc_3065_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                return v___x_3064_;
            }
            19 => {
                v___x_3072_ = crate::leanh::lean_box(1);
                v___x_3073_ = l_Lean_IR_instBEqIRType_beq(v_ty_2856_, v___x_3072_);
                if v___x_3073_ == 0 {
                    crate::leanh::lean_del_object(v___x_3070_);
                    v___x_3074_ = l_Lean_IR_Checker_checkType___closed__0;
                    v___x_3075_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2856_);
                    v___x_3076_ = l_Std_Format_defWidth;
                    v___x_3077_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3078_ =
                        l_Std_Format_pretty(v___x_3075_, v___x_3076_, v___x_3077_, v___x_3077_);
                    v___x_3079_ = lean_string_append(v___x_3074_, v___x_3078_);
                    crate::leanh::lean_dec_ref(v___x_3078_);
                    v___x_3080_ = l_Lean_IR_Checker_checkVar___closed__2;
                    v_msg_3081_ = lean_string_append(v___x_3079_, v___x_3080_);
                    v___x_3082_ = l_Lean_IR_Checker_throwCheckerError___redArg(
                        v_msg_3081_,
                        v_a_2858_,
                        v_a_2859_,
                        v_a_2860_,
                        v_a_2861_,
                    );
                    return v___x_3082_;
                } else {
                    crate::leanh::lean_dec(v_ty_2856_);
                    v___x_3083_ = crate::leanh::lean_box(0);
                    if v_isShared_3071_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3070_, 0, v___x_3083_);
                        v___x_3085_ = v___x_3070_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
                        v___x_3085_ = v_reuseFailAlloc_3086_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                return v___x_3085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkExpr___boxed(
    mut v_ty_3089_: *mut crate::leanh::LeanObject,
    mut v_e_3090_: *mut crate::leanh::LeanObject,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
    mut v_a_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
    mut v_a_3095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3096_ = l_Lean_IR_Checker_checkExpr(
        v_ty_3089_, v_e_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_,
    );
    crate::leanh::lean_dec(v_a_3094_);
    crate::leanh::lean_dec_ref(v_a_3093_);
    crate::leanh::lean_dec(v_a_3092_);
    crate::leanh::lean_dec_ref(v_a_3091_);
    return v_res_3096_;
}
pub unsafe fn l_Lean_IR_Checker_withParams___lam__0(
    mut v_ctx_3097_: *mut crate::leanh::LeanObject,
    mut v_p_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_unused_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3118_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_3104_ = crate::leanh::lean_ctor_get(v_p_3098_, 0);
                crate::leanh::lean_inc(v_x_3104_);
                v___x_3105_ = l_Lean_IR_Checker_markIndex(
                    v_x_3104_,
                    v___y_3099_,
                    v___y_3100_,
                    v___y_3101_,
                    v___y_3102_,
                );
                if crate::leanh::lean_obj_tag(v___x_3105_) == 0 {
                    v_isSharedCheck_3113_ = (!crate::leanh::lean_is_exclusive(v___x_3105_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v_unused_3114_ = crate::leanh::lean_ctor_get(v___x_3105_, 0);
                        crate::leanh::lean_dec(v_unused_3114_);
                        v___x_3107_ = v___x_3105_;
                        v_isShared_3108_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3105_);
                        v___x_3107_ = crate::leanh::lean_box(0);
                        v_isShared_3108_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_3098_);
                    crate::leanh::lean_dec(v_ctx_3097_);
                    v_a_3115_ = crate::leanh::lean_ctor_get(v___x_3105_, 0);
                    v_isSharedCheck_3122_ = (!crate::leanh::lean_is_exclusive(v___x_3105_)) as u8;
                    if v_isSharedCheck_3122_ == 0 {
                        v___x_3117_ = v___x_3105_;
                        v_isShared_3118_ = v_isSharedCheck_3122_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3115_);
                        crate::leanh::lean_dec(v___x_3105_);
                        v___x_3117_ = crate::leanh::lean_box(0);
                        v_isShared_3118_ = v_isSharedCheck_3122_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3109_ = l_Lean_IR_LocalContext_addParam(v_ctx_3097_, v_p_3098_);
                if v_isShared_3108_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3107_, 0, v___x_3109_);
                    v___x_3111_ = v___x_3107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
                    v___x_3111_ = v_reuseFailAlloc_3112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3111_;
            }
            3 => {
                if v_isShared_3118_ == 0 {
                    v___x_3120_ = v___x_3117_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
                    v___x_3120_ = v_reuseFailAlloc_3121_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_withParams___lam__0___boxed(
    mut v_ctx_3123_: *mut crate::leanh::LeanObject,
    mut v_p_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
    mut v___y_3126_: *mut crate::leanh::LeanObject,
    mut v___y_3127_: *mut crate::leanh::LeanObject,
    mut v___y_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3130_ = l_Lean_IR_Checker_withParams___lam__0(
        v_ctx_3123_,
        v_p_3124_,
        v___y_3125_,
        v___y_3126_,
        v___y_3127_,
        v___y_3128_,
    );
    crate::leanh::lean_dec(v___y_3128_);
    crate::leanh::lean_dec_ref(v___y_3127_);
    crate::leanh::lean_dec(v___y_3126_);
    crate::leanh::lean_dec_ref(v___y_3125_);
    return v_res_3130_;
}
pub unsafe fn _init_l_Lean_IR_Checker_withParams___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3131_;
}
pub unsafe fn _init_l_Lean_IR_Checker_withParams___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_withParams___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_Checker_withParams___closed__0_once),
        _init_l_Lean_IR_Checker_withParams___closed__0,
    );
    v___x_3133_ = l_StateRefT_x27_instMonad___redArg(v___x_3132_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_IR_Checker_withParams(
    mut v_ps_3137_: *mut crate::leanh::LeanObject,
    mut v_k_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localCtx_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currentDecl_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3175_: u8 = 0;
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u8 = 0;
    let mut v___f_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: usize = 0;
    let mut v___x_1045__overap_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: usize = 0;
    let mut v___x_3190_: usize = 0;
    let mut v___x_1050__overap_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3144_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_Checker_withParams___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_IR_Checker_withParams___closed__1_once),
                    _init_l_Lean_IR_Checker_withParams___closed__1,
                );
                v_toApplicative_3145_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                v_toFunctor_3146_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 0);
                v_toSeq_3147_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 2);
                v_toSeqLeft_3148_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 3);
                v_toSeqRight_3149_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 4);
                v___f_3150_ = l_Lean_IR_Checker_withParams___closed__2;
                v___f_3151_ = l_Lean_IR_Checker_withParams___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3146_, 2);
                v___f_3152_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3152_, 0, v_toFunctor_3146_);
                v___f_3153_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3153_, 0, v_toFunctor_3146_);
                v___x_3154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3154_, 0, v___f_3152_);
                crate::leanh::lean_ctor_set(v___x_3154_, 1, v___f_3153_);
                crate::leanh::lean_inc(v_toSeqRight_3149_);
                v___f_3155_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3155_, 0, v_toSeqRight_3149_);
                crate::leanh::lean_inc(v_toSeqLeft_3148_);
                v___f_3156_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3156_, 0, v_toSeqLeft_3148_);
                crate::leanh::lean_inc(v_toSeq_3147_);
                v___f_3157_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3157_, 0, v_toSeq_3147_);
                v___x_3158_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3154_);
                crate::leanh::lean_ctor_set(v___x_3158_, 1, v___f_3150_);
                crate::leanh::lean_ctor_set(v___x_3158_, 2, v___f_3157_);
                crate::leanh::lean_ctor_set(v___x_3158_, 3, v___f_3156_);
                crate::leanh::lean_ctor_set(v___x_3158_, 4, v___f_3155_);
                v___x_3159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3159_, 0, v___x_3158_);
                crate::leanh::lean_ctor_set(v___x_3159_, 1, v___f_3151_);
                v___x_3160_ = l_StateRefT_x27_instMonad___redArg(v___x_3159_);
                v___x_3161_ = l_ReaderT_instMonad___redArg(v___x_3160_);
                v_localCtx_3162_ = crate::leanh::lean_ctor_get(v_a_3139_, 0);
                v_currentDecl_3163_ = crate::leanh::lean_ctor_get(v_a_3139_, 1);
                v_decls_3164_ = crate::leanh::lean_ctor_get(v_a_3139_, 2);
                v___x_3180_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3181_ = lean_array_get_size(v_ps_3137_);
                v___x_3182_ = lean_nat_dec_lt(v___x_3180_, v___x_3181_);
                if v___x_3182_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3161_);
                    crate::leanh::lean_dec_ref(v_ps_3137_);
                    crate::leanh::lean_inc(v_localCtx_3162_);
                    v_a_3166_ = v_localCtx_3162_;
                    state = 1;
                    continue;
                } else {
                    v___f_3183_ = l_Lean_IR_Checker_withParams___closed__4;
                    v___x_3184_ = lean_nat_dec_le(v___x_3181_, v___x_3181_);
                    if v___x_3184_ == 0 {
                        if v___x_3182_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3161_);
                            crate::leanh::lean_dec_ref(v_ps_3137_);
                            crate::leanh::lean_inc(v_localCtx_3162_);
                            v_a_3166_ = v_localCtx_3162_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3185_ = 0usize;
                            v___x_3186_ = lean_usize_of_nat(v___x_3181_);
                            crate::leanh::lean_inc(v_localCtx_3162_);
                            v___x_1045__overap_3187_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_3161_,
                                    v___f_3183_,
                                    v_ps_3137_,
                                    v___x_3185_,
                                    v___x_3186_,
                                    v_localCtx_3162_,
                                );
                            crate::leanh::lean_inc(v_a_3142_);
                            crate::leanh::lean_inc_ref(v_a_3141_);
                            crate::leanh::lean_inc(v_a_3140_);
                            crate::leanh::lean_inc_ref(v_a_3139_);
                            v___x_3188_ = crate::leanh::lean_apply_5(
                                v___x_1045__overap_3187_,
                                v_a_3139_,
                                v_a_3140_,
                                v_a_3141_,
                                v_a_3142_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_3170_ = v___x_3188_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3189_ = 0usize;
                        v___x_3190_ = lean_usize_of_nat(v___x_3181_);
                        crate::leanh::lean_inc(v_localCtx_3162_);
                        v___x_1050__overap_3191_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3161_,
                                v___f_3183_,
                                v_ps_3137_,
                                v___x_3189_,
                                v___x_3190_,
                                v_localCtx_3162_,
                            );
                        crate::leanh::lean_inc(v_a_3142_);
                        crate::leanh::lean_inc_ref(v_a_3141_);
                        crate::leanh::lean_inc(v_a_3140_);
                        crate::leanh::lean_inc_ref(v_a_3139_);
                        v___x_3192_ = crate::leanh::lean_apply_5(
                            v___x_1050__overap_3191_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_3170_ = v___x_3192_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_decls_3164_);
                crate::leanh::lean_inc_ref(v_currentDecl_3163_);
                v___x_3167_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3167_, 0, v_a_3166_);
                crate::leanh::lean_ctor_set(v___x_3167_, 1, v_currentDecl_3163_);
                crate::leanh::lean_ctor_set(v___x_3167_, 2, v_decls_3164_);
                crate::leanh::lean_inc(v_a_3142_);
                crate::leanh::lean_inc_ref(v_a_3141_);
                crate::leanh::lean_inc(v_a_3140_);
                v___x_3168_ = crate::leanh::lean_apply_5(
                    v_k_3138_,
                    v___x_3167_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3168_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3170_) == 0 {
                    v_a_3171_ = crate::leanh::lean_ctor_get(v___y_3170_, 0);
                    crate::leanh::lean_inc(v_a_3171_);
                    crate::leanh::lean_dec_ref_known(v___y_3170_, 1);
                    v_a_3166_ = v_a_3171_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_k_3138_);
                    v_a_3172_ = crate::leanh::lean_ctor_get(v___y_3170_, 0);
                    v_isSharedCheck_3179_ = (!crate::leanh::lean_is_exclusive(v___y_3170_)) as u8;
                    if v_isSharedCheck_3179_ == 0 {
                        v___x_3174_ = v___y_3170_;
                        v_isShared_3175_ = v_isSharedCheck_3179_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3172_);
                        crate::leanh::lean_dec(v___y_3170_);
                        v___x_3174_ = crate::leanh::lean_box(0);
                        v_isShared_3175_ = v_isSharedCheck_3179_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3175_ == 0 {
                    v___x_3177_ = v___x_3174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_withParams___boxed(
    mut v_ps_3193_: *mut crate::leanh::LeanObject,
    mut v_k_3194_: *mut crate::leanh::LeanObject,
    mut v_a_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
    mut v_a_3197_: *mut crate::leanh::LeanObject,
    mut v_a_3198_: *mut crate::leanh::LeanObject,
    mut v_a_3199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3200_ = l_Lean_IR_Checker_withParams(
        v_ps_3193_, v_k_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_,
    );
    crate::leanh::lean_dec(v_a_3198_);
    crate::leanh::lean_dec_ref(v_a_3197_);
    crate::leanh::lean_dec(v_a_3196_);
    crate::leanh::lean_dec_ref(v_a_3195_);
    return v_res_3200_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(
    mut v_as_3201_: *mut crate::leanh::LeanObject,
    mut v_i_3202_: usize,
    mut v_stop_3203_: usize,
    mut v_b_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3210_: u8 = 0;
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: usize = 0;
    let mut v___x_3216_: usize = 0;
    let mut v_a_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3210_ = lean_usize_dec_eq(v_i_3202_, v_stop_3203_);
                if v___x_3210_ == 0 {
                    v___x_3211_ = lean_array_uget_borrowed(v_as_3201_, v_i_3202_);
                    v_x_3212_ = crate::leanh::lean_ctor_get(v___x_3211_, 0);
                    crate::leanh::lean_inc(v_x_3212_);
                    v___x_3213_ = l_Lean_IR_Checker_markIndex(
                        v_x_3212_,
                        v___y_3205_,
                        v___y_3206_,
                        v___y_3207_,
                        v___y_3208_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3213_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3213_, 1);
                        crate::leanh::lean_inc(v___x_3211_);
                        v___x_3214_ = l_Lean_IR_LocalContext_addParam(v_b_3204_, v___x_3211_);
                        v___x_3215_ = 1usize;
                        v___x_3216_ = lean_usize_add(v_i_3202_, v___x_3215_);
                        v_i_3202_ = v___x_3216_;
                        v_b_3204_ = v___x_3214_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_3204_);
                        v_a_3218_ = crate::leanh::lean_ctor_get(v___x_3213_, 0);
                        v_isSharedCheck_3225_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3213_)) as u8;
                        if v_isSharedCheck_3225_ == 0 {
                            v___x_3220_ = v___x_3213_;
                            v_isShared_3221_ = v_isSharedCheck_3225_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3218_);
                            crate::leanh::lean_dec(v___x_3213_);
                            v___x_3220_ = crate::leanh::lean_box(0);
                            v_isShared_3221_ = v_isSharedCheck_3225_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3226_, 0, v_b_3204_);
                    return v___x_3226_;
                }
            }
            1 => {
                if v_isShared_3221_ == 0 {
                    v___x_3223_ = v___x_3220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(
    mut v_as_3227_: *mut crate::leanh::LeanObject,
    mut v_i_3228_: *mut crate::leanh::LeanObject,
    mut v_stop_3229_: *mut crate::leanh::LeanObject,
    mut v_b_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3236_: usize = 0;
    let mut v_stop_boxed_3237_: usize = 0;
    let mut v_res_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3236_ = crate::leanh::lean_unbox_usize(v_i_3228_);
    crate::leanh::lean_dec(v_i_3228_);
    v_stop_boxed_3237_ = crate::leanh::lean_unbox_usize(v_stop_3229_);
    crate::leanh::lean_dec(v_stop_3229_);
    v_res_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_3227_, v_i_boxed_3236_, v_stop_boxed_3237_, v_b_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
    crate::leanh::lean_dec(v___y_3234_);
    crate::leanh::lean_dec_ref(v___y_3233_);
    crate::leanh::lean_dec(v___y_3232_);
    crate::leanh::lean_dec_ref(v___y_3231_);
    crate::leanh::lean_dec_ref(v_as_3227_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_IR_Checker_checkFnBody(
    mut v_fnBody_3239_: *mut crate::leanh::LeanObject,
    mut v_a_3240_: *mut crate::leanh::LeanObject,
    mut v_a_3241_: *mut crate::leanh::LeanObject,
    mut v_a_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localCtx_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currentDecl_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localCtx_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currentDecl_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: u8 = 0;
    let mut v___x_3295_: u8 = 0;
    let mut v___x_3296_: usize = 0;
    let mut v___x_3297_: usize = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: usize = 0;
    let mut v___x_3300_: usize = 0;
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: usize = 0;
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: usize = 0;
    let mut v___x_3349_: usize = 0;
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v_unused_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_fnBody_3239_) {
                0 => {
                    v_x_3254_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3254_);
                    v_ty_3255_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 1);
                    crate::leanh::lean_inc_n(v_ty_3255_, 2);
                    v_e_3256_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 2);
                    crate::leanh::lean_inc_ref_n(v_e_3256_, 2);
                    v_b_3257_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 3);
                    crate::leanh::lean_inc(v_b_3257_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 4);
                    v___x_3258_ = l_Lean_IR_Checker_checkExpr(
                        v_ty_3255_, v_e_3256_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3258_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3258_, 1);
                        crate::leanh::lean_inc(v_x_3254_);
                        v___x_3259_ = l_Lean_IR_Checker_markIndex(
                            v_x_3254_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3259_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3259_, 1);
                            v_localCtx_3260_ = crate::leanh::lean_ctor_get(v_a_3240_, 0);
                            crate::leanh::lean_inc(v_localCtx_3260_);
                            v_currentDecl_3261_ = crate::leanh::lean_ctor_get(v_a_3240_, 1);
                            crate::leanh::lean_inc_ref(v_currentDecl_3261_);
                            v_decls_3262_ = crate::leanh::lean_ctor_get(v_a_3240_, 2);
                            crate::leanh::lean_inc_ref(v_decls_3262_);
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            v___x_3263_ = l_Lean_IR_LocalContext_addLocal(
                                v_localCtx_3260_,
                                v_x_3254_,
                                v_ty_3255_,
                                v_e_3256_,
                            );
                            v___x_3264_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3264_, 0, v___x_3263_);
                            crate::leanh::lean_ctor_set(v___x_3264_, 1, v_currentDecl_3261_);
                            crate::leanh::lean_ctor_set(v___x_3264_, 2, v_decls_3262_);
                            v_fnBody_3239_ = v_b_3257_;
                            v_a_3240_ = v___x_3264_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_3257_);
                            crate::leanh::lean_dec_ref(v_e_3256_);
                            crate::leanh::lean_dec(v_ty_3255_);
                            crate::leanh::lean_dec(v_x_3254_);
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            return v___x_3259_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3257_);
                        crate::leanh::lean_dec_ref(v_e_3256_);
                        crate::leanh::lean_dec(v_ty_3255_);
                        crate::leanh::lean_dec(v_x_3254_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3258_;
                    }
                }
                1 => {
                    v_j_3266_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc_n(v_j_3266_, 2);
                    v_xs_3267_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 1);
                    crate::leanh::lean_inc_ref(v_xs_3267_);
                    v_v_3268_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 2);
                    crate::leanh::lean_inc(v_v_3268_);
                    v_b_3269_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 3);
                    crate::leanh::lean_inc(v_b_3269_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 4);
                    v___x_3270_ = l_Lean_IR_Checker_markIndex(
                        v_j_3266_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3270_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3270_, 1);
                        v_localCtx_3271_ = crate::leanh::lean_ctor_get(v_a_3240_, 0);
                        crate::leanh::lean_inc(v_localCtx_3271_);
                        v_currentDecl_3272_ = crate::leanh::lean_ctor_get(v_a_3240_, 1);
                        crate::leanh::lean_inc_ref(v_currentDecl_3272_);
                        v_decls_3273_ = crate::leanh::lean_ctor_get(v_a_3240_, 2);
                        crate::leanh::lean_inc_ref(v_decls_3273_);
                        v___x_3292_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3293_ = lean_array_get_size(v_xs_3267_);
                        v___x_3294_ = lean_nat_dec_lt(v___x_3292_, v___x_3293_);
                        if v___x_3294_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            crate::leanh::lean_inc(v_localCtx_3271_);
                            v_a_3275_ = v_localCtx_3271_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3295_ = lean_nat_dec_le(v___x_3293_, v___x_3293_);
                            if v___x_3295_ == 0 {
                                if v___x_3294_ == 0 {
                                    crate::leanh::lean_dec_ref(v_a_3240_);
                                    crate::leanh::lean_inc(v_localCtx_3271_);
                                    v_a_3275_ = v_localCtx_3271_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3296_ = 0usize;
                                    v___x_3297_ = lean_usize_of_nat(v___x_3293_);
                                    crate::leanh::lean_inc(v_localCtx_3271_);
                                    v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_3267_, v___x_3296_, v___x_3297_, v_localCtx_3271_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
                                    crate::leanh::lean_dec_ref(v_a_3240_);
                                    v___y_3282_ = v___x_3298_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_3299_ = 0usize;
                                v___x_3300_ = lean_usize_of_nat(v___x_3293_);
                                crate::leanh::lean_inc(v_localCtx_3271_);
                                v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_3267_, v___x_3299_, v___x_3300_, v_localCtx_3271_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
                                crate::leanh::lean_dec_ref(v_a_3240_);
                                v___y_3282_ = v___x_3301_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3269_);
                        crate::leanh::lean_dec(v_v_3268_);
                        crate::leanh::lean_dec_ref(v_xs_3267_);
                        crate::leanh::lean_dec(v_j_3266_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3270_;
                    }
                }
                2 => {
                    v_x_3302_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3302_);
                    v_y_3303_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 2);
                    crate::leanh::lean_inc(v_y_3303_);
                    v_b_3304_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 3);
                    crate::leanh::lean_inc(v_b_3304_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 4);
                    v___x_3305_ = l_Lean_IR_Checker_checkVar(
                        v_x_3302_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3305_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3305_, 1);
                        v___x_3306_ = l_Lean_IR_Checker_checkArg(
                            v_y_3303_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3306_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3306_, 1);
                            v_fnBody_3239_ = v_b_3304_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_3304_);
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            return v___x_3306_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3304_);
                        crate::leanh::lean_dec(v_y_3303_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3305_;
                    }
                }
                3 => {
                    v_x_3308_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3308_);
                    v_b_3309_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 2);
                    crate::leanh::lean_inc(v_b_3309_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 3);
                    v___x_3310_ = l_Lean_IR_Checker_checkVar(
                        v_x_3308_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3310_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3310_, 1);
                        v_fnBody_3239_ = v_b_3309_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_3309_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3310_;
                    }
                }
                4 => {
                    v_x_3312_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3312_);
                    v_y_3313_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 2);
                    crate::leanh::lean_inc(v_y_3313_);
                    v_b_3314_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 3);
                    crate::leanh::lean_inc(v_b_3314_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 4);
                    v___x_3315_ = l_Lean_IR_Checker_checkVar(
                        v_x_3312_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3315_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3315_, 1);
                        v___x_3316_ = l_Lean_IR_Checker_checkVar(
                            v_y_3313_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3316_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3316_, 1);
                            v_fnBody_3239_ = v_b_3314_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_3314_);
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            return v___x_3316_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3314_);
                        crate::leanh::lean_dec(v_y_3313_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3315_;
                    }
                }
                5 => {
                    v_x_3318_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3318_);
                    v_y_3319_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 3);
                    crate::leanh::lean_inc(v_y_3319_);
                    v_b_3320_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 5);
                    crate::leanh::lean_inc(v_b_3320_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 6);
                    v___x_3321_ = l_Lean_IR_Checker_checkVar(
                        v_x_3318_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3321_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3321_, 1);
                        v___x_3322_ = l_Lean_IR_Checker_checkVar(
                            v_y_3319_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3322_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3322_, 1);
                            v_fnBody_3239_ = v_b_3320_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_3320_);
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            return v___x_3322_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3320_);
                        crate::leanh::lean_dec(v_y_3319_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3321_;
                    }
                }
                8 => {
                    v_x_3324_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3324_);
                    v_b_3325_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 1);
                    crate::leanh::lean_inc(v_b_3325_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 2);
                    v___x_3326_ = l_Lean_IR_Checker_checkVar(
                        v_x_3324_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3326_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3326_, 1);
                        v_fnBody_3239_ = v_b_3325_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_3325_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3326_;
                    }
                }
                9 => {
                    v_x_3328_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 1);
                    crate::leanh::lean_inc(v_x_3328_);
                    v_cs_3329_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 3);
                    crate::leanh::lean_inc_ref(v_cs_3329_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 4);
                    v___x_3330_ = l_Lean_IR_Checker_checkVar(
                        v_x_3328_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3330_) == 0 {
                        v_isSharedCheck_3351_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3330_)) as u8;
                        if v_isSharedCheck_3351_ == 0 {
                            v_unused_3352_ = crate::leanh::lean_ctor_get(v___x_3330_, 0);
                            crate::leanh::lean_dec(v_unused_3352_);
                            v___x_3332_ = v___x_3330_;
                            v_isShared_3333_ = v_isSharedCheck_3351_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3330_);
                            v___x_3332_ = crate::leanh::lean_box(0);
                            v_isShared_3333_ = v_isSharedCheck_3351_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_cs_3329_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3330_;
                    }
                }
                10 => {
                    v_x_3353_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3353_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 1);
                    v___x_3354_ = l_Lean_IR_Checker_checkArg(
                        v_x_3353_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    crate::leanh::lean_dec_ref(v_a_3240_);
                    return v___x_3354_;
                }
                11 => {
                    v_j_3355_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_j_3355_);
                    v_ys_3356_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 1);
                    crate::leanh::lean_inc_ref(v_ys_3356_);
                    crate::leanh::lean_dec_ref_known(v_fnBody_3239_, 2);
                    v___x_3357_ = l_Lean_IR_Checker_checkJP(
                        v_j_3355_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3357_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3357_, 1);
                        v___x_3358_ = l_Lean_IR_Checker_checkArgs(
                            v_ys_3356_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_,
                        );
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        crate::leanh::lean_dec_ref(v_ys_3356_);
                        return v___x_3358_;
                    } else {
                        crate::leanh::lean_dec_ref(v_ys_3356_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        return v___x_3357_;
                    }
                }
                12 => {
                    crate::leanh::lean_dec_ref(v_a_3240_);
                    v___x_3359_ = crate::leanh::lean_box(0);
                    v___x_3360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3360_, 0, v___x_3359_);
                    return v___x_3360_;
                }
                _ => {
                    v_x_3361_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 0);
                    crate::leanh::lean_inc(v_x_3361_);
                    v_b_3362_ = crate::leanh::lean_ctor_get(v_fnBody_3239_, 2);
                    crate::leanh::lean_inc(v_b_3362_);
                    crate::leanh::lean_dec(v_fnBody_3239_);
                    v_x_3246_ = v_x_3361_;
                    v_b_3247_ = v_b_3362_;
                    v___y_3248_ = v_a_3240_;
                    v___y_3249_ = v_a_3241_;
                    v___y_3250_ = v_a_3242_;
                    v___y_3251_ = v_a_3243_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_3252_ = l_Lean_IR_Checker_checkVar(
                    v_x_3246_,
                    v___y_3248_,
                    v___y_3249_,
                    v___y_3250_,
                    v___y_3251_,
                );
                if crate::leanh::lean_obj_tag(v___x_3252_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3252_, 1);
                    v_fnBody_3239_ = v_b_3247_;
                    v_a_3240_ = v___y_3248_;
                    v_a_3241_ = v___y_3249_;
                    v_a_3242_ = v___y_3250_;
                    v_a_3243_ = v___y_3251_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3248_);
                    crate::leanh::lean_dec(v_b_3247_);
                    return v___x_3252_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_decls_3273_);
                crate::leanh::lean_inc_ref(v_currentDecl_3272_);
                v___x_3276_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3276_, 0, v_a_3275_);
                crate::leanh::lean_ctor_set(v___x_3276_, 1, v_currentDecl_3272_);
                crate::leanh::lean_ctor_set(v___x_3276_, 2, v_decls_3273_);
                crate::leanh::lean_inc(v_v_3268_);
                v___x_3277_ = l_Lean_IR_Checker_checkFnBody(
                    v_v_3268_,
                    v___x_3276_,
                    v_a_3241_,
                    v_a_3242_,
                    v_a_3243_,
                );
                if crate::leanh::lean_obj_tag(v___x_3277_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3277_, 1);
                    v___x_3278_ = l_Lean_IR_LocalContext_addJP(
                        v_localCtx_3271_,
                        v_j_3266_,
                        v_xs_3267_,
                        v_v_3268_,
                    );
                    v___x_3279_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3279_, 0, v___x_3278_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 1, v_currentDecl_3272_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 2, v_decls_3273_);
                    v_fnBody_3239_ = v_b_3269_;
                    v_a_3240_ = v___x_3279_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_decls_3273_);
                    crate::leanh::lean_dec_ref(v_currentDecl_3272_);
                    crate::leanh::lean_dec(v_localCtx_3271_);
                    crate::leanh::lean_dec(v_b_3269_);
                    crate::leanh::lean_dec(v_v_3268_);
                    crate::leanh::lean_dec_ref(v_xs_3267_);
                    crate::leanh::lean_dec(v_j_3266_);
                    return v___x_3277_;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_3282_) == 0 {
                    v_a_3283_ = crate::leanh::lean_ctor_get(v___y_3282_, 0);
                    crate::leanh::lean_inc(v_a_3283_);
                    crate::leanh::lean_dec_ref_known(v___y_3282_, 1);
                    v_a_3275_ = v_a_3283_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_decls_3273_);
                    crate::leanh::lean_dec_ref(v_currentDecl_3272_);
                    crate::leanh::lean_dec(v_localCtx_3271_);
                    crate::leanh::lean_dec(v_b_3269_);
                    crate::leanh::lean_dec(v_v_3268_);
                    crate::leanh::lean_dec_ref(v_xs_3267_);
                    crate::leanh::lean_dec(v_j_3266_);
                    v_a_3284_ = crate::leanh::lean_ctor_get(v___y_3282_, 0);
                    v_isSharedCheck_3291_ = (!crate::leanh::lean_is_exclusive(v___y_3282_)) as u8;
                    if v_isSharedCheck_3291_ == 0 {
                        v___x_3286_ = v___y_3282_;
                        v_isShared_3287_ = v_isSharedCheck_3291_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3284_);
                        crate::leanh::lean_dec(v___y_3282_);
                        v___x_3286_ = crate::leanh::lean_box(0);
                        v_isShared_3287_ = v_isSharedCheck_3291_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3287_ == 0 {
                    v___x_3289_ = v___x_3286_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3289_;
            }
            6 => {
                v___x_3334_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3335_ = lean_array_get_size(v_cs_3329_);
                v___x_3336_ = crate::leanh::lean_box(0);
                v___x_3337_ = lean_nat_dec_lt(v___x_3334_, v___x_3335_);
                if v___x_3337_ == 0 {
                    crate::leanh::lean_dec_ref(v_cs_3329_);
                    crate::leanh::lean_dec_ref(v_a_3240_);
                    if v_isShared_3333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3336_);
                        v___x_3339_ = v___x_3332_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3336_);
                        v___x_3339_ = v_reuseFailAlloc_3340_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_3341_ = lean_nat_dec_le(v___x_3335_, v___x_3335_);
                    if v___x_3341_ == 0 {
                        if v___x_3337_ == 0 {
                            crate::leanh::lean_dec_ref(v_cs_3329_);
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            if v_isShared_3333_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3336_);
                                v___x_3343_ = v___x_3332_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3344_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3336_);
                                v___x_3343_ = v_reuseFailAlloc_3344_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3332_);
                            v___x_3345_ = 0usize;
                            v___x_3346_ = lean_usize_of_nat(v___x_3335_);
                            v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_3329_, v___x_3345_, v___x_3346_, v___x_3336_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
                            crate::leanh::lean_dec_ref(v_a_3240_);
                            crate::leanh::lean_dec_ref(v_cs_3329_);
                            return v___x_3347_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3332_);
                        v___x_3348_ = 0usize;
                        v___x_3349_ = lean_usize_of_nat(v___x_3335_);
                        v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_3329_, v___x_3348_, v___x_3349_, v___x_3336_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
                        crate::leanh::lean_dec_ref(v_a_3240_);
                        crate::leanh::lean_dec_ref(v_cs_3329_);
                        return v___x_3350_;
                    }
                }
            }
            7 => {
                return v___x_3339_;
            }
            8 => {
                return v___x_3343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(
    mut v_as_3363_: *mut crate::leanh::LeanObject,
    mut v_i_3364_: usize,
    mut v_stop_3365_: usize,
    mut v_b_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: usize = 0;
    let mut v___x_3378_: usize = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3372_ = lean_usize_dec_eq(v_i_3364_, v_stop_3365_);
                if v___x_3372_ == 0 {
                    v___x_3373_ = lean_array_uget_borrowed(v_as_3363_, v_i_3364_);
                    v___x_3374_ = l_Lean_IR_Alt_body(v___x_3373_);
                    crate::leanh::lean_inc_ref(v___y_3367_);
                    v___x_3375_ = l_Lean_IR_Checker_checkFnBody(
                        v___x_3374_,
                        v___y_3367_,
                        v___y_3368_,
                        v___y_3369_,
                        v___y_3370_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3375_) == 0 {
                        v_a_3376_ = crate::leanh::lean_ctor_get(v___x_3375_, 0);
                        crate::leanh::lean_inc(v_a_3376_);
                        crate::leanh::lean_dec_ref_known(v___x_3375_, 1);
                        v___x_3377_ = 1usize;
                        v___x_3378_ = lean_usize_add(v_i_3364_, v___x_3377_);
                        v_i_3364_ = v___x_3378_;
                        v_b_3366_ = v_a_3376_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3375_;
                    }
                } else {
                    v___x_3380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3380_, 0, v_b_3366_);
                    return v___x_3380_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(
    mut v_as_3381_: *mut crate::leanh::LeanObject,
    mut v_i_3382_: *mut crate::leanh::LeanObject,
    mut v_stop_3383_: *mut crate::leanh::LeanObject,
    mut v_b_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3390_: usize = 0;
    let mut v_stop_boxed_3391_: usize = 0;
    let mut v_res_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3390_ = crate::leanh::lean_unbox_usize(v_i_3382_);
    crate::leanh::lean_dec(v_i_3382_);
    v_stop_boxed_3391_ = crate::leanh::lean_unbox_usize(v_stop_3383_);
    crate::leanh::lean_dec(v_stop_3383_);
    v_res_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_3381_, v_i_boxed_3390_, v_stop_boxed_3391_, v_b_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
    crate::leanh::lean_dec(v___y_3388_);
    crate::leanh::lean_dec_ref(v___y_3387_);
    crate::leanh::lean_dec(v___y_3386_);
    crate::leanh::lean_dec_ref(v___y_3385_);
    crate::leanh::lean_dec_ref(v_as_3381_);
    return v_res_3392_;
}
pub unsafe fn l_Lean_IR_Checker_checkFnBody___boxed(
    mut v_fnBody_3393_: *mut crate::leanh::LeanObject,
    mut v_a_3394_: *mut crate::leanh::LeanObject,
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
    mut v_a_3397_: *mut crate::leanh::LeanObject,
    mut v_a_3398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3399_ =
        l_Lean_IR_Checker_checkFnBody(v_fnBody_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_);
    crate::leanh::lean_dec(v_a_3397_);
    crate::leanh::lean_dec_ref(v_a_3396_);
    crate::leanh::lean_dec(v_a_3395_);
    return v_res_3399_;
}
pub unsafe fn l_Lean_IR_Checker_checkDecl(
    mut v_x_3400_: *mut crate::leanh::LeanObject,
    mut v_a_3401_: *mut crate::leanh::LeanObject,
    mut v_a_3402_: *mut crate::leanh::LeanObject,
    mut v_a_3403_: *mut crate::leanh::LeanObject,
    mut v_a_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_xs_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localCtx_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currentDecl_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3421_: u8 = 0;
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: usize = 0;
    let mut v___x_3431_: usize = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: usize = 0;
    let mut v___x_3434_: usize = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v_unused_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localCtx_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: usize = 0;
    let mut v___x_3464_: usize = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: usize = 0;
    let mut v___x_3467_: usize = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3400_) == 0 {
                    v_xs_3406_ = crate::leanh::lean_ctor_get(v_x_3400_, 1);
                    crate::leanh::lean_inc_ref(v_xs_3406_);
                    v_body_3407_ = crate::leanh::lean_ctor_get(v_x_3400_, 3);
                    crate::leanh::lean_inc(v_body_3407_);
                    crate::leanh::lean_dec_ref_known(v_x_3400_, 5);
                    v_localCtx_3408_ = crate::leanh::lean_ctor_get(v_a_3401_, 0);
                    v_currentDecl_3409_ = crate::leanh::lean_ctor_get(v_a_3401_, 1);
                    v_decls_3410_ = crate::leanh::lean_ctor_get(v_a_3401_, 2);
                    v___x_3426_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3427_ = lean_array_get_size(v_xs_3406_);
                    v___x_3428_ = lean_nat_dec_lt(v___x_3426_, v___x_3427_);
                    if v___x_3428_ == 0 {
                        crate::leanh::lean_dec_ref(v_xs_3406_);
                        crate::leanh::lean_inc(v_localCtx_3408_);
                        v_a_3412_ = v_localCtx_3408_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3429_ = lean_nat_dec_le(v___x_3427_, v___x_3427_);
                        if v___x_3429_ == 0 {
                            if v___x_3428_ == 0 {
                                crate::leanh::lean_dec_ref(v_xs_3406_);
                                crate::leanh::lean_inc(v_localCtx_3408_);
                                v_a_3412_ = v_localCtx_3408_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3430_ = 0usize;
                                v___x_3431_ = lean_usize_of_nat(v___x_3427_);
                                crate::leanh::lean_inc(v_localCtx_3408_);
                                v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_3406_, v___x_3430_, v___x_3431_, v_localCtx_3408_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
                                crate::leanh::lean_dec_ref(v_xs_3406_);
                                v___y_3416_ = v___x_3432_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3433_ = 0usize;
                            v___x_3434_ = lean_usize_of_nat(v___x_3427_);
                            crate::leanh::lean_inc(v_localCtx_3408_);
                            v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_3406_, v___x_3433_, v___x_3434_, v_localCtx_3408_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
                            crate::leanh::lean_dec_ref(v_xs_3406_);
                            v___y_3416_ = v___x_3435_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_xs_3436_ = crate::leanh::lean_ctor_get(v_x_3400_, 1);
                    crate::leanh::lean_inc_ref(v_xs_3436_);
                    crate::leanh::lean_dec_ref_known(v_x_3400_, 4);
                    v___x_3437_ = crate::leanh::lean_box(0);
                    v___x_3456_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3457_ = lean_array_get_size(v_xs_3436_);
                    v___x_3458_ = lean_nat_dec_lt(v___x_3456_, v___x_3457_);
                    if v___x_3458_ == 0 {
                        crate::leanh::lean_dec_ref(v_xs_3436_);
                        v___x_3459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3459_, 0, v___x_3437_);
                        return v___x_3459_;
                    } else {
                        v_localCtx_3460_ = crate::leanh::lean_ctor_get(v_a_3401_, 0);
                        v___x_3461_ = lean_nat_dec_le(v___x_3457_, v___x_3457_);
                        if v___x_3461_ == 0 {
                            if v___x_3458_ == 0 {
                                crate::leanh::lean_dec_ref(v_xs_3436_);
                                v___x_3462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3462_, 0, v___x_3437_);
                                return v___x_3462_;
                            } else {
                                v___x_3463_ = 0usize;
                                v___x_3464_ = lean_usize_of_nat(v___x_3457_);
                                crate::leanh::lean_inc(v_localCtx_3460_);
                                v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_3436_, v___x_3463_, v___x_3464_, v_localCtx_3460_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
                                crate::leanh::lean_dec_ref(v_xs_3436_);
                                v___y_3439_ = v___x_3465_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_3466_ = 0usize;
                            v___x_3467_ = lean_usize_of_nat(v___x_3457_);
                            crate::leanh::lean_inc(v_localCtx_3460_);
                            v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_3436_, v___x_3466_, v___x_3467_, v_localCtx_3460_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
                            crate::leanh::lean_dec_ref(v_xs_3436_);
                            v___y_3439_ = v___x_3468_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_decls_3410_);
                crate::leanh::lean_inc_ref(v_currentDecl_3409_);
                v___x_3413_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3413_, 0, v_a_3412_);
                crate::leanh::lean_ctor_set(v___x_3413_, 1, v_currentDecl_3409_);
                crate::leanh::lean_ctor_set(v___x_3413_, 2, v_decls_3410_);
                v___x_3414_ = l_Lean_IR_Checker_checkFnBody(
                    v_body_3407_,
                    v___x_3413_,
                    v_a_3402_,
                    v_a_3403_,
                    v_a_3404_,
                );
                return v___x_3414_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3416_) == 0 {
                    v_a_3417_ = crate::leanh::lean_ctor_get(v___y_3416_, 0);
                    crate::leanh::lean_inc(v_a_3417_);
                    crate::leanh::lean_dec_ref_known(v___y_3416_, 1);
                    v_a_3412_ = v_a_3417_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_body_3407_);
                    v_a_3418_ = crate::leanh::lean_ctor_get(v___y_3416_, 0);
                    v_isSharedCheck_3425_ = (!crate::leanh::lean_is_exclusive(v___y_3416_)) as u8;
                    if v_isSharedCheck_3425_ == 0 {
                        v___x_3420_ = v___y_3416_;
                        v_isShared_3421_ = v_isSharedCheck_3425_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3418_);
                        crate::leanh::lean_dec(v___y_3416_);
                        v___x_3420_ = crate::leanh::lean_box(0);
                        v_isShared_3421_ = v_isSharedCheck_3425_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3421_ == 0 {
                    v___x_3423_ = v___x_3420_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
                    v___x_3423_ = v_reuseFailAlloc_3424_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3423_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_3439_) == 0 {
                    v_isSharedCheck_3446_ = (!crate::leanh::lean_is_exclusive(v___y_3439_)) as u8;
                    if v_isSharedCheck_3446_ == 0 {
                        v_unused_3447_ = crate::leanh::lean_ctor_get(v___y_3439_, 0);
                        crate::leanh::lean_dec(v_unused_3447_);
                        v___x_3441_ = v___y_3439_;
                        v_isShared_3442_ = v_isSharedCheck_3446_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_3439_);
                        v___x_3441_ = crate::leanh::lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3446_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_3448_ = crate::leanh::lean_ctor_get(v___y_3439_, 0);
                    v_isSharedCheck_3455_ = (!crate::leanh::lean_is_exclusive(v___y_3439_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v___x_3450_ = v___y_3439_;
                        v_isShared_3451_ = v_isSharedCheck_3455_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3448_);
                        crate::leanh::lean_dec(v___y_3439_);
                        v___x_3450_ = crate::leanh::lean_box(0);
                        v_isShared_3451_ = v_isSharedCheck_3455_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3442_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3441_, 0, v___x_3437_);
                    v___x_3444_ = v___x_3441_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3437_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3444_;
            }
            8 => {
                if v_isShared_3451_ == 0 {
                    v___x_3453_ = v___x_3450_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Checker_checkDecl___boxed(
    mut v_x_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
    mut v_a_3472_: *mut crate::leanh::LeanObject,
    mut v_a_3473_: *mut crate::leanh::LeanObject,
    mut v_a_3474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3475_ =
        l_Lean_IR_Checker_checkDecl(v_x_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
    crate::leanh::lean_dec(v_a_3473_);
    crate::leanh::lean_dec_ref(v_a_3472_);
    crate::leanh::lean_dec(v_a_3471_);
    crate::leanh::lean_dec_ref(v_a_3470_);
    return v_res_3475_;
}
pub unsafe fn l_Lean_IR_checkDecl(
    mut v_decls_3476_: *mut crate::leanh::LeanObject,
    mut v_decl_3477_: *mut crate::leanh::LeanObject,
    mut v_a_3478_: *mut crate::leanh::LeanObject,
    mut v_a_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3481_ = crate::leanh::lean_box(1);
                v___x_3482_ = lean_st_mk_ref(v___x_3481_);
                crate::leanh::lean_inc_ref(v_decl_3477_);
                v___x_3483_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3483_, 0, v___x_3481_);
                crate::leanh::lean_ctor_set(v___x_3483_, 1, v_decl_3477_);
                crate::leanh::lean_ctor_set(v___x_3483_, 2, v_decls_3476_);
                v___x_3484_ = l_Lean_IR_Checker_checkDecl(
                    v_decl_3477_,
                    v___x_3483_,
                    v___x_3482_,
                    v_a_3478_,
                    v_a_3479_,
                );
                crate::leanh::lean_dec_ref_known(v___x_3483_, 3);
                if crate::leanh::lean_obj_tag(v___x_3484_) == 0 {
                    v_a_3485_ = crate::leanh::lean_ctor_get(v___x_3484_, 0);
                    v_isSharedCheck_3493_ = (!crate::leanh::lean_is_exclusive(v___x_3484_)) as u8;
                    if v_isSharedCheck_3493_ == 0 {
                        v___x_3487_ = v___x_3484_;
                        v_isShared_3488_ = v_isSharedCheck_3493_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3485_);
                        crate::leanh::lean_dec(v___x_3484_);
                        v___x_3487_ = crate::leanh::lean_box(0);
                        v_isShared_3488_ = v_isSharedCheck_3493_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3482_);
                    return v___x_3484_;
                }
            }
            1 => {
                v___x_3489_ = lean_st_ref_get(v___x_3482_);
                crate::leanh::lean_dec(v___x_3482_);
                crate::leanh::lean_dec(v___x_3489_);
                if v_isShared_3488_ == 0 {
                    v___x_3491_ = v___x_3487_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3485_);
                    v___x_3491_ = v_reuseFailAlloc_3492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_checkDecl___boxed(
    mut v_decls_3494_: *mut crate::leanh::LeanObject,
    mut v_decl_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
    mut v_a_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3499_ = l_Lean_IR_checkDecl(v_decls_3494_, v_decl_3495_, v_a_3496_, v_a_3497_);
    crate::leanh::lean_dec(v_a_3497_);
    crate::leanh::lean_dec_ref(v_a_3496_);
    return v_res_3499_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(
    mut v_decls_3500_: *mut crate::leanh::LeanObject,
    mut v_as_3501_: *mut crate::leanh::LeanObject,
    mut v_i_3502_: usize,
    mut v_stop_3503_: usize,
    mut v_b_3504_: *mut crate::leanh::LeanObject,
    mut v___y_3505_: *mut crate::leanh::LeanObject,
    mut v___y_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: usize = 0;
    let mut v___x_3513_: usize = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3508_ = lean_usize_dec_eq(v_i_3502_, v_stop_3503_);
                if v___x_3508_ == 0 {
                    v___x_3509_ = lean_array_uget_borrowed(v_as_3501_, v_i_3502_);
                    crate::leanh::lean_inc(v___x_3509_);
                    crate::leanh::lean_inc_ref(v_decls_3500_);
                    v___x_3510_ =
                        l_Lean_IR_checkDecl(v_decls_3500_, v___x_3509_, v___y_3505_, v___y_3506_);
                    if crate::leanh::lean_obj_tag(v___x_3510_) == 0 {
                        v_a_3511_ = crate::leanh::lean_ctor_get(v___x_3510_, 0);
                        crate::leanh::lean_inc(v_a_3511_);
                        crate::leanh::lean_dec_ref_known(v___x_3510_, 1);
                        v___x_3512_ = 1usize;
                        v___x_3513_ = lean_usize_add(v_i_3502_, v___x_3512_);
                        v_i_3502_ = v___x_3513_;
                        v_b_3504_ = v_a_3511_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_decls_3500_);
                        return v___x_3510_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decls_3500_);
                    v___x_3515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3515_, 0, v_b_3504_);
                    return v___x_3515_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(
    mut v_decls_3516_: *mut crate::leanh::LeanObject,
    mut v_as_3517_: *mut crate::leanh::LeanObject,
    mut v_i_3518_: *mut crate::leanh::LeanObject,
    mut v_stop_3519_: *mut crate::leanh::LeanObject,
    mut v_b_3520_: *mut crate::leanh::LeanObject,
    mut v___y_3521_: *mut crate::leanh::LeanObject,
    mut v___y_3522_: *mut crate::leanh::LeanObject,
    mut v___y_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3524_: usize = 0;
    let mut v_stop_boxed_3525_: usize = 0;
    let mut v_res_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3524_ = crate::leanh::lean_unbox_usize(v_i_3518_);
    crate::leanh::lean_dec(v_i_3518_);
    v_stop_boxed_3525_ = crate::leanh::lean_unbox_usize(v_stop_3519_);
    crate::leanh::lean_dec(v_stop_3519_);
    v_res_3526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_3516_, v_as_3517_, v_i_boxed_3524_, v_stop_boxed_3525_, v_b_3520_, v___y_3521_, v___y_3522_);
    crate::leanh::lean_dec(v___y_3522_);
    crate::leanh::lean_dec_ref(v___y_3521_);
    crate::leanh::lean_dec_ref(v_as_3517_);
    return v_res_3526_;
}
pub unsafe fn l_Lean_IR_checkDecls(
    mut v_decls_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: u8 = 0;
    v___x_3531_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3532_ = lean_array_get_size(v_decls_3527_);
    v___x_3533_ = crate::leanh::lean_box(0);
    v___x_3534_ = lean_nat_dec_lt(v___x_3531_, v___x_3532_);
    if v___x_3534_ == 0 {
        let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_decls_3527_);
        v___x_3535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3535_, 0, v___x_3533_);
        return v___x_3535_;
    } else {
        let mut v___x_3536_: u8 = 0;
        v___x_3536_ = lean_nat_dec_le(v___x_3532_, v___x_3532_);
        if v___x_3536_ == 0 {
            if v___x_3534_ == 0 {
                let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_decls_3527_);
                v___x_3537_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3537_, 0, v___x_3533_);
                return v___x_3537_;
            } else {
                let mut v___x_3538_: usize = 0;
                let mut v___x_3539_: usize = 0;
                let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3538_ = 0usize;
                v___x_3539_ = lean_usize_of_nat(v___x_3532_);
                crate::leanh::lean_inc_ref(v_decls_3527_);
                v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_3527_, v_decls_3527_, v___x_3538_, v___x_3539_, v___x_3533_, v_a_3528_, v_a_3529_);
                crate::leanh::lean_dec_ref(v_decls_3527_);
                return v___x_3540_;
            }
        } else {
            let mut v___x_3541_: usize = 0;
            let mut v___x_3542_: usize = 0;
            let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3541_ = 0usize;
            v___x_3542_ = lean_usize_of_nat(v___x_3532_);
            crate::leanh::lean_inc_ref(v_decls_3527_);
            v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_3527_, v_decls_3527_, v___x_3541_, v___x_3542_, v___x_3533_, v_a_3528_, v_a_3529_);
            crate::leanh::lean_dec_ref(v_decls_3527_);
            return v___x_3543_;
        }
    }
}
pub unsafe fn l_Lean_IR_checkDecls___boxed(
    mut v_decls_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3548_ = l_Lean_IR_checkDecls(v_decls_3544_, v_a_3545_, v_a_3546_);
    crate::leanh::lean_dec(v_a_3546_);
    crate::leanh::lean_dec_ref(v_a_3545_);
    return v_res_3548_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Checker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_IR_Checker_maxCtorFields = _init_l_Lean_IR_Checker_maxCtorFields();
    crate::leanh::lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields);
    l_Lean_IR_Checker_maxCtorScalarsSize = _init_l_Lean_IR_Checker_maxCtorScalarsSize();
    crate::leanh::lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize);
    l_Lean_IR_Checker_maxCtorTag = _init_l_Lean_IR_Checker_maxCtorTag();
    crate::leanh::lean_mark_persistent(l_Lean_IR_Checker_maxCtorTag);
    l_Lean_IR_Checker_usizeSize = _init_l_Lean_IR_Checker_usizeSize();
    crate::leanh::lean_mark_persistent(l_Lean_IR_Checker_usizeSize);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Checker(
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
pub unsafe fn initialize_Lean_Compiler_IR_Checker(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Checker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Checker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Checker(builtin);
}

// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Postponed
// Imports: Lean.Elab.Term.TermElabM
use crate::r#gen::Init::Data::Array::Basic::l_Array_repr___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DocString::Extension::{
    l_Lean_getBuiltinVersoDocStrings, l_Lean_versoDocStringExt,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    initialize_Lean_Elab_Term_TermElabM, runtime_initialize_Lean_Elab_Term_TermElabM,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_evalConstCheck___redArg, l_Lean_Environment_header,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_instInhabitedPersistentEnvExtensionState___redArg,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_app___override, l_Lean_Expr_const___override};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_length;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
    lean_string_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_has_compile_error;
pub static l_Lean_Doc_instBEqPostponedImport___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Doc_instBEqPostponedImport_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instBEqPostponedImport___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instBEqPostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instBEqPostponedImport: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instBEqPostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instHashablePostponedImport_hash___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_instHashablePostponedImport_hash___closed__0: u64 = 0;
static mut l_Lean_Doc_instHashablePostponedImport_hash___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_instHashablePostponedImport_hash___closed__1: u64 = 0;
pub static l_Lean_Doc_instHashablePostponedImport___closed__0_value:
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
    m_fun: l_Lean_Doc_instHashablePostponedImport_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_instHashablePostponedImport___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instHashablePostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instHashablePostponedImport: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instHashablePostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedImport___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Doc_instReprPostponedImport_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_instReprPostponedImport___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instReprPostponedImport: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [68, 111, 99, 0],
};
static mut l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
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
        80, 111, 115, 116, 112, 111, 110, 101, 100, 73, 109, 112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 107, 0],
};
static mut l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8539228228387540046 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        14264559095826683398 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14422704330241461366 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_instToExprPostponedImport___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Doc_instToExprPostponedImport___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_instToExprPostponedImport___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8539228228387540046 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Doc_instToExprPostponedImport___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
            14264559095826683398 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_instToExprPostponedImport___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_instToExprPostponedImport___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instToExprPostponedImport___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instToExprPostponedImport___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instToExprPostponedImport___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Doc_instToExprPostponedImport: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instOrdPostponedImport___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instOrdPostponedImport___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instOrdPostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instOrdPostponedImport: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instOrdPostponedImport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [80, 111, 115, 116, 112, 111, 110, 101, 100, 67, 104, 101, 99, 107, 0]};
static mut l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,10197265652540810871 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instTypeNamePostponedCheck: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [123, 32, 104, 97, 110, 100, 108, 101, 114, 32, 58, 61, 32, 0],
};
static mut l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [44, 32, 105, 109, 112, 111, 114, 116, 115, 32, 58, 61, 32, 0],
};
static mut l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [125, 0],
};
static mut l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instReprPostponedCheck___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Doc_instReprPostponedCheck___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_instReprPostponedImport___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_instReprPostponedCheck___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instReprPostponedCheck: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instReprPostponedCheck___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [80, 111, 115, 116, 112, 111, 110, 101, 100, 67, 104, 101, 99, 107, 72, 97, 110, 100, 108, 101, 114, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0_value) as *mut crate::leanh::LeanObject,7556730971289341272 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 104, 101, 99, 107, 32, 105, 110, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [96, 32, 114, 101, 113, 117, 105, 114, 101, 115, 32, 116, 104, 97, 116, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 44, 32, 98, 117, 116, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 104, 101, 99, 107, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,4988463328408922526 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 112, 97, 115, 115, 101, 100, 44, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [96, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_checkPostponed___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [99, 104, 101, 99, 107, 115, 0],
    };
static mut l_Lean_Doc_checkPostponed___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_checkPostponed___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_checkPostponed___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_checkPostponed___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6969427541253499674 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Doc_checkPostponed___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_checkPostponed___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_checkPostponed___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_checkPostponed___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_checkPostponed___closed__3_value: crate::leanh::LeanStringObject<19> =
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
            80, 111, 115, 116, 112, 111, 110, 101, 100, 32, 99, 104, 101, 99, 107, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_Doc_checkPostponed___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_checkPostponed___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_checkPostponed___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_checkPostponed___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_checkPostponed___closed__5_value: crate::leanh::LeanStringObject<16> =
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
            32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 44, 32, 0,
        ],
    };
static mut l_Lean_Doc_checkPostponed___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_checkPostponed___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_checkPostponed___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_checkPostponed___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_checkPostponed___closed__7_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Doc_checkPostponed___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_checkPostponed___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_checkPostponed___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_checkPostponed___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 111, 115, 116, 112, 111, 110, 101, 100, 75, 105, 110, 100, 0]};
static mut l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject,18024980190372331012 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instTypeNamePostponedKind: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 111, 115, 116, 112, 111, 110, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject,11658146083681944743 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instTypeNamePostponedName: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Doc_instBEqPostponedImport_beq(
    mut v_x_2046_: *mut crate::leanh::LeanObject,
    mut v_x_2047_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2048_: u8 = 0;
    v___x_2048_ = lean_name_eq(v_x_2046_, v_x_2047_);
    return v___x_2048_;
}
pub unsafe fn l_Lean_Doc_instBEqPostponedImport_beq___boxed(
    mut v_x_2049_: *mut crate::leanh::LeanObject,
    mut v_x_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2051_: u8 = 0;
    let mut v_r_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Lean_Doc_instBEqPostponedImport_beq(v_x_2049_, v_x_2050_);
    crate::leanh::lean_dec(v_x_2050_);
    crate::leanh::lean_dec(v_x_2049_);
    v_r_2052_ = crate::leanh::lean_box((v_res_2051_) as usize);
    return v_r_2052_;
}
pub unsafe fn _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__0() -> u64 {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u64 = 0;
    v___x_2055_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2056_ = lean_uint64_of_nat(v___x_2055_);
    return v___x_2056_;
}
pub unsafe fn _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__1() -> u64 {
    let mut v___x_2057_: u64 = 0;
    let mut v___x_2058_: u64 = 0;
    let mut v___x_2059_: u64 = 0;
    v___x_2057_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instHashablePostponedImport_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Doc_instHashablePostponedImport_hash___closed__0_once),
        _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__0,
    );
    v___x_2058_ = 0u64;
    v___x_2059_ = lean_uint64_mix_hash(v___x_2058_, v___x_2057_);
    return v___x_2059_;
}
pub unsafe fn l_Lean_Doc_instHashablePostponedImport_hash(
    mut v_x_2060_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_2061_: u64 = 0;
    v___x_2061_ = 0u64;
    if crate::leanh::lean_obj_tag(v_x_2060_) == 0 {
        let mut v___x_2062_: u64 = 0;
        v___x_2062_ = crate::leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lean_Doc_instHashablePostponedImport_hash___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Doc_instHashablePostponedImport_hash___closed__1_once),
            _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__1,
        );
        return v___x_2062_;
    } else {
        let mut v_hash_2063_: u64 = 0;
        let mut v___x_2064_: u64 = 0;
        v_hash_2063_ = crate::leanh::lean_ctor_get_uint64(
            v_x_2060_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        v___x_2064_ = lean_uint64_mix_hash(v___x_2061_, v_hash_2063_);
        return v___x_2064_;
    }
}
pub unsafe fn l_Lean_Doc_instHashablePostponedImport_hash___boxed(
    mut v_x_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2066_: u64 = 0;
    let mut v_r_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lean_Doc_instHashablePostponedImport_hash(v_x_2065_);
    crate::leanh::lean_dec(v_x_2065_);
    v_r_2067_ = crate::leanh::lean_box_uint64(v_res_2066_);
    return v_r_2067_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Doc_instReprPostponedImport_repr_spec__0(
    mut v_a_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2071_ = lean_nat_to_int(v_a_2070_);
    return v___x_2071_;
}
pub unsafe fn _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2086_ = lean_nat_to_int(v___x_2085_);
    return v___x_2086_;
}
pub unsafe fn _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2088_ = l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0;
    v___x_2089_ = lean_string_length(v___x_2088_);
    return v___x_2089_;
}
pub unsafe fn _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2090_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9_once),
        _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9,
    );
    v___x_2091_ = lean_nat_to_int(v___x_2090_);
    return v___x_2091_;
}
pub unsafe fn l_Lean_Doc_instReprPostponedImport_repr___redArg(
    mut v_x_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6;
    v___x_2098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7_once),
        _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7,
    );
    v___x_2099_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2100_ = l_Lean_Name_reprPrec(v_x_2096_, v___x_2099_);
    v___x_2101_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2098_);
    crate::leanh::lean_ctor_set(v___x_2101_, 1, v___x_2100_);
    v___x_2102_ = 0;
    v___x_2103_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2101_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2103_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2102_,
    );
    v___x_2104_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2104_, 0, v___x_2097_);
    crate::leanh::lean_ctor_set(v___x_2104_, 1, v___x_2103_);
    v___x_2105_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10_once),
        _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10,
    );
    v___x_2106_ = l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11;
    v___x_2107_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2106_);
    crate::leanh::lean_ctor_set(v___x_2107_, 1, v___x_2104_);
    v___x_2108_ = l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12;
    v___x_2109_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2109_, 0, v___x_2107_);
    crate::leanh::lean_ctor_set(v___x_2109_, 1, v___x_2108_);
    v___x_2110_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2105_);
    crate::leanh::lean_ctor_set(v___x_2110_, 1, v___x_2109_);
    v___x_2111_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2111_, 0, v___x_2110_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2111_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2102_,
    );
    return v___x_2111_;
}
pub unsafe fn l_Lean_Doc_instReprPostponedImport_repr(
    mut v_x_2112_: *mut crate::leanh::LeanObject,
    mut v_prec_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = l_Lean_Doc_instReprPostponedImport_repr___redArg(v_x_2112_);
    return v___x_2114_;
}
pub unsafe fn l_Lean_Doc_instReprPostponedImport_repr___boxed(
    mut v_x_2115_: *mut crate::leanh::LeanObject,
    mut v_prec_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2117_ = l_Lean_Doc_instReprPostponedImport_repr(v_x_2115_, v_prec_2116_);
    crate::leanh::lean_dec(v_prec_2116_);
    return v_res_2117_;
}
pub unsafe fn _init_l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2129_ = crate::leanh::lean_box(0);
    v___x_2130_ = l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4;
    v___x_2131_ = l_Lean_Expr_const___override(v___x_2130_, v___x_2129_);
    return v___x_2131_;
}
pub unsafe fn l_Lean_Doc_instToExprPostponedImport___lam__0(
    mut v_x_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5_once),
        _init_l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5,
    );
    v___x_2134_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_x_2132_);
    v___x_2135_ = l_Lean_Expr_app___override(v___x_2133_, v___x_2134_);
    return v___x_2135_;
}
pub unsafe fn _init_l_Lean_Doc_instToExprPostponedImport___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2141_ = crate::leanh::lean_box(0);
    v___x_2142_ = l_Lean_Doc_instToExprPostponedImport___closed__1;
    v___x_2143_ = l_Lean_Expr_const___override(v___x_2142_, v___x_2141_);
    return v___x_2143_;
}
pub unsafe fn _init_l_Lean_Doc_instToExprPostponedImport___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2144_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instToExprPostponedImport___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Doc_instToExprPostponedImport___closed__2_once),
        _init_l_Lean_Doc_instToExprPostponedImport___closed__2,
    );
    v___f_2145_ = l_Lean_Doc_instToExprPostponedImport___closed__0;
    v___x_2146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2146_, 0, v___f_2145_);
    crate::leanh::lean_ctor_set(v___x_2146_, 1, v___x_2144_);
    return v___x_2146_;
}
pub unsafe fn _init_l_Lean_Doc_instToExprPostponedImport() -> *mut crate::leanh::LeanObject {
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2147_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instToExprPostponedImport___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Doc_instToExprPostponedImport___closed__3_once),
        _init_l_Lean_Doc_instToExprPostponedImport___closed__3,
    );
    return v___x_2147_;
}
pub unsafe fn l_Lean_Doc_instReprPostponedCheck___lam__0(
    mut v___x_2166_: *mut crate::leanh::LeanObject,
    mut v_v_2167_: *mut crate::leanh::LeanObject,
    mut v_x_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_handler_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_handler_2169_ = crate::leanh::lean_ctor_get(v_v_2167_, 0);
    crate::leanh::lean_inc(v_handler_2169_);
    v_imports_2170_ = crate::leanh::lean_ctor_get(v_v_2167_, 1);
    crate::leanh::lean_inc_ref(v_imports_2170_);
    crate::leanh::lean_dec_ref(v_v_2167_);
    v___x_2171_ = l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1;
    v___x_2172_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2173_ = l_Lean_Name_reprPrec(v_handler_2169_, v___x_2172_);
    v___x_2174_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2171_);
    crate::leanh::lean_ctor_set(v___x_2174_, 1, v___x_2173_);
    v___x_2175_ = l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3;
    v___x_2176_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2176_, 0, v___x_2174_);
    crate::leanh::lean_ctor_set(v___x_2176_, 1, v___x_2175_);
    v___x_2177_ = l_Array_repr___redArg(v___x_2166_, v_imports_2170_);
    v___x_2178_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2176_);
    crate::leanh::lean_ctor_set(v___x_2178_, 1, v___x_2177_);
    v___x_2179_ = l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5;
    v___x_2180_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2178_);
    crate::leanh::lean_ctor_set(v___x_2180_, 1, v___x_2179_);
    return v___x_2180_;
}
pub unsafe fn l_Lean_Doc_instReprPostponedCheck___lam__0___boxed(
    mut v___x_2181_: *mut crate::leanh::LeanObject,
    mut v_v_2182_: *mut crate::leanh::LeanObject,
    mut v_x_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Lean_Doc_instReprPostponedCheck___lam__0(v___x_2181_, v_v_2182_, v_x_2183_);
    crate::leanh::lean_dec(v_x_2183_);
    return v_res_2184_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = crate::leanh::lean_box(0);
    v___x_2189_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_2190_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2190_, 0, v___x_2189_);
    crate::leanh::lean_ctor_set(v___x_2190_, 1, v___x_2188_);
    return v___x_2190_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0);
    v___x_2193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2193_, 0, v___x_2192_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(
    mut v___y_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg();
    return v_res_2195_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(
    mut v_msgData_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
    mut v___y_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2202_ = lean_st_ref_get(v___y_2200_);
    v_env_2203_ = crate::leanh::lean_ctor_get(v___x_2202_, 0);
    crate::leanh::lean_inc_ref(v_env_2203_);
    crate::leanh::lean_dec(v___x_2202_);
    v___x_2204_ = lean_st_ref_get(v___y_2198_);
    v_mctx_2205_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2205_);
    crate::leanh::lean_dec(v___x_2204_);
    v_lctx_2206_ = crate::leanh::lean_ctor_get(v___y_2197_, 2);
    v_options_2207_ = crate::leanh::lean_ctor_get(v___y_2199_, 2);
    crate::leanh::lean_inc_ref(v_options_2207_);
    crate::leanh::lean_inc_ref(v_lctx_2206_);
    v___x_2208_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2208_, 0, v_env_2203_);
    crate::leanh::lean_ctor_set(v___x_2208_, 1, v_mctx_2205_);
    crate::leanh::lean_ctor_set(v___x_2208_, 2, v_lctx_2206_);
    crate::leanh::lean_ctor_set(v___x_2208_, 3, v_options_2207_);
    v___x_2209_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2209_, 0, v___x_2208_);
    crate::leanh::lean_ctor_set(v___x_2209_, 1, v_msgData_2196_);
    v___x_2210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
    crate::leanh::lean_dec(v___y_2215_);
    crate::leanh::lean_dec_ref(v___y_2214_);
    crate::leanh::lean_dec(v___y_2213_);
    crate::leanh::lean_dec_ref(v___y_2212_);
    return v_res_2217_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2218_ = crate::leanh::lean_box(1);
    v___x_2219_ = l_Lean_MessageData_ofFormat(v___x_2218_);
    return v___x_2219_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2223_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2;
    v___x_2224_ = l_Lean_MessageData_ofFormat(v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_x_2225_: *mut crate::leanh::LeanObject,
    mut v_x_2226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v_before_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_unused_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2226_) == 0 {
                    return v_x_2225_;
                } else {
                    v_head_2227_ = crate::leanh::lean_ctor_get(v_x_2226_, 0);
                    v_tail_2228_ = crate::leanh::lean_ctor_get(v_x_2226_, 1);
                    v_isSharedCheck_2250_ = (!crate::leanh::lean_is_exclusive(v_x_2226_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v___x_2230_ = v_x_2226_;
                        v_isShared_2231_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2228_);
                        crate::leanh::lean_inc(v_head_2227_);
                        crate::leanh::lean_dec(v_x_2226_);
                        v___x_2230_ = crate::leanh::lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2232_ = crate::leanh::lean_ctor_get(v_head_2227_, 0);
                v_isSharedCheck_2248_ = (!crate::leanh::lean_is_exclusive(v_head_2227_)) as u8;
                if v_isSharedCheck_2248_ == 0 {
                    v_unused_2249_ = crate::leanh::lean_ctor_get(v_head_2227_, 1);
                    crate::leanh::lean_dec(v_unused_2249_);
                    v___x_2234_ = v_head_2227_;
                    v_isShared_2235_ = v_isSharedCheck_2248_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_2232_);
                    crate::leanh::lean_dec(v_head_2227_);
                    v___x_2234_ = crate::leanh::lean_box(0);
                    v_isShared_2235_ = v_isSharedCheck_2248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2236_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0);
                if v_isShared_2235_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2234_, 7);
                    crate::leanh::lean_ctor_set(v___x_2234_, 1, v___x_2236_);
                    crate::leanh::lean_ctor_set(v___x_2234_, 0, v_x_2225_);
                    v___x_2238_ = v___x_2234_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2247_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_x_2225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2236_);
                    v___x_2238_ = v_reuseFailAlloc_2247_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2239_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3);
                if v_isShared_2231_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2230_, 7);
                    crate::leanh::lean_ctor_set(v___x_2230_, 1, v___x_2239_);
                    crate::leanh::lean_ctor_set(v___x_2230_, 0, v___x_2238_);
                    v___x_2241_ = v___x_2230_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2246_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2239_);
                    v___x_2241_ = v_reuseFailAlloc_2246_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2242_ = l_Lean_MessageData_ofSyntax(v_before_2232_);
                v___x_2243_ = l_Lean_indentD(v___x_2242_);
                v___x_2244_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2241_);
                crate::leanh::lean_ctor_set(v___x_2244_, 1, v___x_2243_);
                v_x_2225_ = v___x_2244_;
                v_x_2226_ = v_tail_2228_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_opts_2251_: *mut crate::leanh::LeanObject,
    mut v_opt_2252_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2253_ = crate::leanh::lean_ctor_get(v_opt_2252_, 0);
    v_defValue_2254_ = crate::leanh::lean_ctor_get(v_opt_2252_, 1);
    v_map_2255_ = crate::leanh::lean_ctor_get(v_opts_2251_, 0);
    v___x_2256_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2255_,
            v_name_2253_,
        );
    if crate::leanh::lean_obj_tag(v___x_2256_) == 0 {
        let mut v___x_2257_: u8 = 0;
        v___x_2257_ = (crate::leanh::lean_unbox(v_defValue_2254_) as u8);
        return v___x_2257_;
    } else {
        let mut v_val_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2258_ = crate::leanh::lean_ctor_get(v___x_2256_, 0);
        crate::leanh::lean_inc(v_val_2258_);
        crate::leanh::lean_dec_ref_known(v___x_2256_, 1);
        if crate::leanh::lean_obj_tag(v_val_2258_) == 1 {
            let mut v_v_2259_: u8 = 0;
            v_v_2259_ = crate::leanh::lean_ctor_get_uint8(v_val_2258_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2258_, 0);
            return v_v_2259_;
        } else {
            let mut v___x_2260_: u8 = 0;
            crate::leanh::lean_dec(v_val_2258_);
            v___x_2260_ = (crate::leanh::lean_unbox(v_defValue_2254_) as u8);
            return v___x_2260_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_opts_2261_: *mut crate::leanh::LeanObject,
    mut v_opt_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2263_: u8 = 0;
    let mut v_r_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2263_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(v_opts_2261_, v_opt_2262_);
    crate::leanh::lean_dec_ref(v_opt_2262_);
    crate::leanh::lean_dec_ref(v_opts_2261_);
    v_r_2264_ = crate::leanh::lean_box((v_res_2263_) as usize);
    return v_r_2264_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2268_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
    v___x_2269_ = l_Lean_MessageData_ofFormat(v___x_2268_);
    return v___x_2269_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_msgData_2270_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: u8 = 0;
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_unused_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2274_ = crate::leanh::lean_ctor_get(v___y_2272_, 2);
                v___x_2275_ = l_Lean_Elab_pp_macroStack;
                v___x_2276_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(v_options_2274_, v___x_2275_);
                if v___x_2276_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2271_);
                    v___x_2277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2277_, 0, v_msgData_2270_);
                    return v___x_2277_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2271_) == 0 {
                        v___x_2278_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2278_, 0, v_msgData_2270_);
                        return v___x_2278_;
                    } else {
                        v_head_2279_ = crate::leanh::lean_ctor_get(v_macroStack_2271_, 0);
                        crate::leanh::lean_inc(v_head_2279_);
                        v_after_2280_ = crate::leanh::lean_ctor_get(v_head_2279_, 1);
                        v_isSharedCheck_2295_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2279_)) as u8;
                        if v_isSharedCheck_2295_ == 0 {
                            v_unused_2296_ = crate::leanh::lean_ctor_get(v_head_2279_, 0);
                            crate::leanh::lean_dec(v_unused_2296_);
                            v___x_2282_ = v_head_2279_;
                            v_isShared_2283_ = v_isSharedCheck_2295_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2280_);
                            crate::leanh::lean_dec(v_head_2279_);
                            v___x_2282_ = crate::leanh::lean_box(0);
                            v_isShared_2283_ = v_isSharedCheck_2295_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0);
                if v_isShared_2283_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2282_, 7);
                    crate::leanh::lean_ctor_set(v___x_2282_, 1, v___x_2284_);
                    crate::leanh::lean_ctor_set(v___x_2282_, 0, v_msgData_2270_);
                    v___x_2286_ = v___x_2282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2294_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_msgData_2270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2284_);
                    v___x_2286_ = v_reuseFailAlloc_2294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2287_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2);
                v___x_2288_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2286_);
                crate::leanh::lean_ctor_set(v___x_2288_, 1, v___x_2287_);
                v___x_2289_ = l_Lean_MessageData_ofSyntax(v_after_2280_);
                v___x_2290_ = l_Lean_indentD(v___x_2289_);
                v_msgData_2291_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2291_, 0, v___x_2288_);
                crate::leanh::lean_ctor_set(v_msgData_2291_, 1, v___x_2290_);
                v___x_2292_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6(v_msgData_2291_, v_macroStack_2271_);
                v___x_2293_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2293_, 0, v___x_2292_);
                return v___x_2293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_msgData_2297_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(v_msgData_2297_, v_macroStack_2298_, v___y_2299_);
    crate::leanh::lean_dec_ref(v___y_2299_);
    return v_res_2301_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(
    mut v_msg_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2319_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2310_ = crate::leanh::lean_ctor_get(v___y_2307_, 5);
                v___x_2311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2302_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
                v_a_2312_ = crate::leanh::lean_ctor_get(v___x_2311_, 0);
                crate::leanh::lean_inc(v_a_2312_);
                crate::leanh::lean_dec_ref(v___x_2311_);
                v_macroStack_2313_ = crate::leanh::lean_ctor_get(v___y_2303_, 1);
                v___x_2314_ = l_Lean_Elab_getBetterRef(v_ref_2310_, v_macroStack_2313_);
                crate::leanh::lean_inc(v_macroStack_2313_);
                v___x_2315_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(v_a_2312_, v_macroStack_2313_, v___y_2307_);
                v_a_2316_ = crate::leanh::lean_ctor_get(v___x_2315_, 0);
                v_isSharedCheck_2324_ = (!crate::leanh::lean_is_exclusive(v___x_2315_)) as u8;
                if v_isSharedCheck_2324_ == 0 {
                    v___x_2318_ = v___x_2315_;
                    v_isShared_2319_ = v_isSharedCheck_2324_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2316_);
                    crate::leanh::lean_dec(v___x_2315_);
                    v___x_2318_ = crate::leanh::lean_box(0);
                    v_isShared_2319_ = v_isSharedCheck_2324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2320_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2314_);
                crate::leanh::lean_ctor_set(v___x_2320_, 1, v_a_2316_);
                if v_isShared_2319_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2318_, 1);
                    crate::leanh::lean_ctor_set(v___x_2318_, 0, v___x_2320_);
                    v___x_2322_ = v___x_2318_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
                    v___x_2322_ = v_reuseFailAlloc_2323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msg_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
    crate::leanh::lean_dec(v___y_2331_);
    crate::leanh::lean_dec_ref(v___y_2330_);
    crate::leanh::lean_dec(v___y_2329_);
    crate::leanh::lean_dec_ref(v___y_2328_);
    crate::leanh::lean_dec(v___y_2327_);
    crate::leanh::lean_dec_ref(v___y_2326_);
    return v_res_2333_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(
    mut v_x_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2348_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2334_) == 0 {
                    v_a_2342_ = crate::leanh::lean_ctor_get(v_x_2334_, 0);
                    crate::leanh::lean_inc(v_a_2342_);
                    crate::leanh::lean_dec_ref_known(v_x_2334_, 1);
                    v___x_2343_ = l_Lean_stringToMessageData(v_a_2342_);
                    v___x_2344_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2343_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
                    return v___x_2344_;
                } else {
                    v_a_2345_ = crate::leanh::lean_ctor_get(v_x_2334_, 0);
                    v_isSharedCheck_2352_ = (!crate::leanh::lean_is_exclusive(v_x_2334_)) as u8;
                    if v_isSharedCheck_2352_ == 0 {
                        v___x_2347_ = v_x_2334_;
                        v_isShared_2348_ = v_isSharedCheck_2352_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2345_);
                        crate::leanh::lean_dec(v_x_2334_);
                        v___x_2347_ = crate::leanh::lean_box(0);
                        v_isShared_2348_ = v_isSharedCheck_2352_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2348_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2347_, 0);
                    v___x_2350_ = v___x_2347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
                    v___x_2350_ = v_reuseFailAlloc_2351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(
    mut v_x_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
    crate::leanh::lean_dec(v___y_2359_);
    crate::leanh::lean_dec_ref(v___y_2358_);
    crate::leanh::lean_dec(v___y_2357_);
    crate::leanh::lean_dec_ref(v___y_2356_);
    crate::leanh::lean_dec(v___y_2355_);
    crate::leanh::lean_dec_ref(v___y_2354_);
    return v_res_2361_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(
    mut v_typeName_2362_: *mut crate::leanh::LeanObject,
    mut v_constName_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2371_ = lean_st_ref_get(v___y_2369_);
                v_env_2372_ = crate::leanh::lean_ctor_get(v___x_2371_, 0);
                crate::leanh::lean_inc_ref(v_env_2372_);
                crate::leanh::lean_dec(v___x_2371_);
                crate::leanh::lean_inc(v_constName_2363_);
                v___x_2373_ = lean_has_compile_error(v_env_2372_, v_constName_2363_);
                if v___x_2373_ == 0 {
                    v___x_2374_ = lean_st_ref_get(v___y_2369_);
                    v_env_2375_ = crate::leanh::lean_ctor_get(v___x_2374_, 0);
                    crate::leanh::lean_inc_ref(v_env_2375_);
                    crate::leanh::lean_dec(v___x_2374_);
                    v_options_2376_ = crate::leanh::lean_ctor_get(v___y_2368_, 2);
                    v___x_2377_ = l_Lean_Environment_evalConstCheck___redArg(
                        v_env_2375_,
                        v_options_2376_,
                        v_typeName_2362_,
                        v_constName_2363_,
                    );
                    v___x_2378_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_2377_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
                    return v___x_2378_;
                } else {
                    v___x_2379_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg();
                    if crate::leanh::lean_obj_tag(v___x_2379_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2379_, 1);
                        v___x_2380_ = lean_st_ref_get(v___y_2369_);
                        v_env_2381_ = crate::leanh::lean_ctor_get(v___x_2380_, 0);
                        crate::leanh::lean_inc_ref(v_env_2381_);
                        crate::leanh::lean_dec(v___x_2380_);
                        v_options_2382_ = crate::leanh::lean_ctor_get(v___y_2368_, 2);
                        v___x_2383_ = l_Lean_Environment_evalConstCheck___redArg(
                            v_env_2381_,
                            v_options_2382_,
                            v_typeName_2362_,
                            v_constName_2363_,
                        );
                        v___x_2384_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_2383_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
                        return v___x_2384_;
                    } else {
                        crate::leanh::lean_dec(v_constName_2363_);
                        crate::leanh::lean_dec(v_typeName_2362_);
                        v_a_2385_ = crate::leanh::lean_ctor_get(v___x_2379_, 0);
                        v_isSharedCheck_2392_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2379_)) as u8;
                        if v_isSharedCheck_2392_ == 0 {
                            v___x_2387_ = v___x_2379_;
                            v_isShared_2388_ = v_isSharedCheck_2392_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2385_);
                            crate::leanh::lean_dec(v___x_2379_);
                            v___x_2387_ = crate::leanh::lean_box(0);
                            v_isShared_2388_ = v_isSharedCheck_2392_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2388_ == 0 {
                    v___x_2390_ = v___x_2387_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
                    v___x_2390_ = v_reuseFailAlloc_2391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg___boxed(
    mut v_typeName_2393_: *mut crate::leanh::LeanObject,
    mut v_constName_2394_: *mut crate::leanh::LeanObject,
    mut v___y_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(v_typeName_2393_, v_constName_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
    crate::leanh::lean_dec(v___y_2400_);
    crate::leanh::lean_dec_ref(v___y_2399_);
    crate::leanh::lean_dec(v___y_2398_);
    crate::leanh::lean_dec_ref(v___y_2397_);
    crate::leanh::lean_dec(v___y_2396_);
    crate::leanh::lean_dec_ref(v___y_2395_);
    return v_res_2402_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(
    mut v_name_2408_: *mut crate::leanh::LeanObject,
    mut v_a_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
    mut v_a_2411_: *mut crate::leanh::LeanObject,
    mut v_a_2412_: *mut crate::leanh::LeanObject,
    mut v_a_2413_: *mut crate::leanh::LeanObject,
    mut v_a_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ =
        l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1;
    v___x_2417_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(v___x_2416_, v_name_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
    return v___x_2417_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___boxed(
    mut v_name_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
    mut v_a_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2426_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(
        v_name_2418_,
        v_a_2419_,
        v_a_2420_,
        v_a_2421_,
        v_a_2422_,
        v_a_2423_,
        v_a_2424_,
    );
    crate::leanh::lean_dec(v_a_2424_);
    crate::leanh::lean_dec_ref(v_a_2423_);
    crate::leanh::lean_dec(v_a_2422_);
    crate::leanh::lean_dec_ref(v_a_2421_);
    crate::leanh::lean_dec(v_a_2420_);
    crate::leanh::lean_dec_ref(v_a_2419_);
    return v_res_2426_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1(
    mut v_00_u03b1_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg();
    return v___x_2435_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___boxed(
    mut v_00_u03b1_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2444_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1(v_00_u03b1_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
    crate::leanh::lean_dec(v___y_2442_);
    crate::leanh::lean_dec_ref(v___y_2441_);
    crate::leanh::lean_dec(v___y_2440_);
    crate::leanh::lean_dec_ref(v___y_2439_);
    crate::leanh::lean_dec(v___y_2438_);
    crate::leanh::lean_dec_ref(v___y_2437_);
    return v_res_2444_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0(
    mut v_00_u03b1_2445_: *mut crate::leanh::LeanObject,
    mut v_typeName_2446_: *mut crate::leanh::LeanObject,
    mut v_constName_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
    mut v___y_2450_: *mut crate::leanh::LeanObject,
    mut v___y_2451_: *mut crate::leanh::LeanObject,
    mut v___y_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(v_typeName_2446_, v_constName_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
    return v___x_2455_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___boxed(
    mut v_00_u03b1_2456_: *mut crate::leanh::LeanObject,
    mut v_typeName_2457_: *mut crate::leanh::LeanObject,
    mut v_constName_2458_: *mut crate::leanh::LeanObject,
    mut v___y_2459_: *mut crate::leanh::LeanObject,
    mut v___y_2460_: *mut crate::leanh::LeanObject,
    mut v___y_2461_: *mut crate::leanh::LeanObject,
    mut v___y_2462_: *mut crate::leanh::LeanObject,
    mut v___y_2463_: *mut crate::leanh::LeanObject,
    mut v___y_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0(v_00_u03b1_2456_, v_typeName_2457_, v_constName_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
    crate::leanh::lean_dec(v___y_2464_);
    crate::leanh::lean_dec_ref(v___y_2463_);
    crate::leanh::lean_dec(v___y_2462_);
    crate::leanh::lean_dec_ref(v___y_2461_);
    crate::leanh::lean_dec(v___y_2460_);
    crate::leanh::lean_dec_ref(v___y_2459_);
    return v_res_2466_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0(
    mut v_00_u03b1_2467_: *mut crate::leanh::LeanObject,
    mut v_x_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
    mut v___y_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
    return v___x_2476_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___boxed(
    mut v_00_u03b1_2477_: *mut crate::leanh::LeanObject,
    mut v_x_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
    mut v___y_2484_: *mut crate::leanh::LeanObject,
    mut v___y_2485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2486_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0(v_00_u03b1_2477_, v_x_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
    crate::leanh::lean_dec(v___y_2484_);
    crate::leanh::lean_dec_ref(v___y_2483_);
    crate::leanh::lean_dec(v___y_2482_);
    crate::leanh::lean_dec_ref(v___y_2481_);
    crate::leanh::lean_dec(v___y_2480_);
    crate::leanh::lean_dec_ref(v___y_2479_);
    return v_res_2486_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2487_: *mut crate::leanh::LeanObject,
    mut v_msg_2488_: *mut crate::leanh::LeanObject,
    mut v___y_2489_: *mut crate::leanh::LeanObject,
    mut v___y_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2497_: *mut crate::leanh::LeanObject,
    mut v_msg_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2506_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2497_, v_msg_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
    crate::leanh::lean_dec(v___y_2504_);
    crate::leanh::lean_dec_ref(v___y_2503_);
    crate::leanh::lean_dec(v___y_2502_);
    crate::leanh::lean_dec_ref(v___y_2501_);
    crate::leanh::lean_dec(v___y_2500_);
    crate::leanh::lean_dec_ref(v___y_2499_);
    return v_res_2506_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4(
    mut v_msgData_2507_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2508_: *mut crate::leanh::LeanObject,
    mut v___y_2509_: *mut crate::leanh::LeanObject,
    mut v___y_2510_: *mut crate::leanh::LeanObject,
    mut v___y_2511_: *mut crate::leanh::LeanObject,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(v_msgData_2507_, v_macroStack_2508_, v___y_2513_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_msgData_2517_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2526_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4(v_msgData_2517_, v_macroStack_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
    crate::leanh::lean_dec(v___y_2524_);
    crate::leanh::lean_dec_ref(v___y_2523_);
    crate::leanh::lean_dec(v___y_2522_);
    crate::leanh::lean_dec_ref(v___y_2521_);
    crate::leanh::lean_dec(v___y_2520_);
    crate::leanh::lean_dec_ref(v___y_2519_);
    return v_res_2526_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(
    mut v_s_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_passed_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failed_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_passed_2528_ = crate::leanh::lean_ctor_get(v_s_2527_, 0);
    v_failed_2529_ = crate::leanh::lean_ctor_get(v_s_2527_, 1);
    v___x_2530_ = lean_array_get_size(v_failed_2529_);
    v___x_2531_ = lean_nat_add(v_passed_2528_, v___x_2530_);
    return v___x_2531_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total___boxed(
    mut v_s_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2533_ =
        l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v_s_2532_);
    crate::leanh::lean_dec_ref(v_s_2532_);
    return v_res_2533_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(
    mut v_act_2534_: *mut crate::leanh::LeanObject,
    mut v_a_2535_: *mut crate::leanh::LeanObject,
    mut v_a_2536_: *mut crate::leanh::LeanObject,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
    mut v_a_2539_: *mut crate::leanh::LeanObject,
    mut v_a_2540_: *mut crate::leanh::LeanObject,
    mut v_a_2541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passed_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failed_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2552_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2568_: u8 = 0;
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passed_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failed_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_unused_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2541_);
                crate::leanh::lean_inc_ref(v_a_2540_);
                crate::leanh::lean_inc(v_a_2539_);
                crate::leanh::lean_inc_ref(v_a_2538_);
                crate::leanh::lean_inc(v_a_2537_);
                crate::leanh::lean_inc_ref(v_a_2536_);
                v___x_2543_ = crate::leanh::lean_apply_7(
                    v_act_2534_,
                    v_a_2536_,
                    v_a_2537_,
                    v_a_2538_,
                    v_a_2539_,
                    v_a_2540_,
                    v_a_2541_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2543_) == 0 {
                    v_isSharedCheck_2564_ = (!crate::leanh::lean_is_exclusive(v___x_2543_)) as u8;
                    if v_isSharedCheck_2564_ == 0 {
                        v_unused_2565_ = crate::leanh::lean_ctor_get(v___x_2543_, 0);
                        crate::leanh::lean_dec(v_unused_2565_);
                        v___x_2545_ = v___x_2543_;
                        v_isShared_2546_ = v_isSharedCheck_2564_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2543_);
                        v___x_2545_ = crate::leanh::lean_box(0);
                        v_isShared_2546_ = v_isSharedCheck_2564_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2566_ = crate::leanh::lean_ctor_get(v___x_2543_, 0);
                    crate::leanh::lean_inc(v_a_2566_);
                    v___x_2590_ = l_Lean_Exception_isInterrupt(v_a_2566_);
                    if v___x_2590_ == 0 {
                        crate::leanh::lean_inc(v_a_2566_);
                        v___x_2591_ = l_Lean_Exception_isRuntime(v_a_2566_);
                        v___y_2568_ = v___x_2591_;
                        state = 5;
                        continue;
                    } else {
                        v___y_2568_ = v___x_2590_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2547_ = lean_st_ref_take(v_a_2535_);
                v_passed_2548_ = crate::leanh::lean_ctor_get(v___x_2547_, 0);
                v_failed_2549_ = crate::leanh::lean_ctor_get(v___x_2547_, 1);
                v_isSharedCheck_2563_ = (!crate::leanh::lean_is_exclusive(v___x_2547_)) as u8;
                if v_isSharedCheck_2563_ == 0 {
                    v___x_2551_ = v___x_2547_;
                    v_isShared_2552_ = v_isSharedCheck_2563_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_failed_2549_);
                    crate::leanh::lean_inc(v_passed_2548_);
                    crate::leanh::lean_dec(v___x_2547_);
                    v___x_2551_ = crate::leanh::lean_box(0);
                    v_isShared_2552_ = v_isSharedCheck_2563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2553_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2554_ = lean_nat_add(v_passed_2548_, v___x_2553_);
                crate::leanh::lean_dec(v_passed_2548_);
                if v_isShared_2552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2551_, 0, v___x_2554_);
                    v___x_2556_ = v___x_2551_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2554_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_failed_2549_);
                    v___x_2556_ = v_reuseFailAlloc_2562_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2557_ = lean_st_ref_set(v_a_2535_, v___x_2556_);
                v___x_2558_ = crate::leanh::lean_box(0);
                if v_isShared_2546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2545_, 0, v___x_2558_);
                    v___x_2560_ = v___x_2545_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
                    v___x_2560_ = v_reuseFailAlloc_2561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2560_;
            }
            5 => {
                if v___y_2568_ == 0 {
                    v_isSharedCheck_2588_ = (!crate::leanh::lean_is_exclusive(v___x_2543_)) as u8;
                    if v_isSharedCheck_2588_ == 0 {
                        v_unused_2589_ = crate::leanh::lean_ctor_get(v___x_2543_, 0);
                        crate::leanh::lean_dec(v_unused_2589_);
                        v___x_2570_ = v___x_2543_;
                        v_isShared_2571_ = v_isSharedCheck_2588_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2543_);
                        v___x_2570_ = crate::leanh::lean_box(0);
                        v_isShared_2571_ = v_isSharedCheck_2588_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2566_);
                    return v___x_2543_;
                }
            }
            6 => {
                v___x_2572_ = lean_st_ref_take(v_a_2535_);
                v_passed_2573_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
                v_failed_2574_ = crate::leanh::lean_ctor_get(v___x_2572_, 1);
                v_isSharedCheck_2587_ = (!crate::leanh::lean_is_exclusive(v___x_2572_)) as u8;
                if v_isSharedCheck_2587_ == 0 {
                    v___x_2576_ = v___x_2572_;
                    v_isShared_2577_ = v_isSharedCheck_2587_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_failed_2574_);
                    crate::leanh::lean_inc(v_passed_2573_);
                    crate::leanh::lean_dec(v___x_2572_);
                    v___x_2576_ = crate::leanh::lean_box(0);
                    v_isShared_2577_ = v_isSharedCheck_2587_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2578_ = lean_array_push(v_failed_2574_, v_a_2566_);
                if v_isShared_2577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2576_, 1, v___x_2578_);
                    v___x_2580_ = v___x_2576_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_passed_2573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___x_2578_);
                    v___x_2580_ = v_reuseFailAlloc_2586_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2581_ = lean_st_ref_set(v_a_2535_, v___x_2580_);
                v___x_2582_ = crate::leanh::lean_box(0);
                if v_isShared_2571_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2570_, 0);
                    crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2582_);
                    v___x_2584_ = v___x_2570_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck___boxed(
    mut v_act_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_a_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
    mut v_a_2597_: *mut crate::leanh::LeanObject,
    mut v_a_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
    mut v_a_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2601_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(
        v_act_2592_,
        v_a_2593_,
        v_a_2594_,
        v_a_2595_,
        v_a_2596_,
        v_a_2597_,
        v_a_2598_,
        v_a_2599_,
    );
    crate::leanh::lean_dec(v_a_2599_);
    crate::leanh::lean_dec_ref(v_a_2598_);
    crate::leanh::lean_dec(v_a_2597_);
    crate::leanh::lean_dec_ref(v_a_2596_);
    crate::leanh::lean_dec(v_a_2595_);
    crate::leanh::lean_dec_ref(v_a_2594_);
    crate::leanh::lean_dec(v_a_2593_);
    return v_res_2601_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(
    mut v_msg_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2608_ = crate::leanh::lean_ctor_get(v___y_2605_, 5);
                v___x_2609_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
                v_a_2610_ = crate::leanh::lean_ctor_get(v___x_2609_, 0);
                v_isSharedCheck_2618_ = (!crate::leanh::lean_is_exclusive(v___x_2609_)) as u8;
                if v_isSharedCheck_2618_ == 0 {
                    v___x_2612_ = v___x_2609_;
                    v_isShared_2613_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2610_);
                    crate::leanh::lean_dec(v___x_2609_);
                    v___x_2612_ = crate::leanh::lean_box(0);
                    v_isShared_2613_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2608_);
                v___x_2614_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2614_, 0, v_ref_2608_);
                crate::leanh::lean_ctor_set(v___x_2614_, 1, v_a_2610_);
                if v_isShared_2613_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2612_, 1);
                    crate::leanh::lean_ctor_set(v___x_2612_, 0, v___x_2614_);
                    v___x_2616_ = v___x_2612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
                    v___x_2616_ = v_reuseFailAlloc_2617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg___boxed(
    mut v_msg_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
    mut v___y_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(v_msg_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
    crate::leanh::lean_dec(v___y_2623_);
    crate::leanh::lean_dec_ref(v___y_2622_);
    crate::leanh::lean_dec(v___y_2621_);
    crate::leanh::lean_dec_ref(v___y_2620_);
    return v_res_2625_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1(
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_as_2627_: *mut crate::leanh::LeanObject,
    mut v_i_2628_: usize,
    mut v_stop_2629_: usize,
) -> u8 {
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: usize = 0;
    let mut v___x_2634_: usize = 0;
    let mut v___x_2636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2630_ = lean_usize_dec_eq(v_i_2628_, v_stop_2629_);
                if v___x_2630_ == 0 {
                    v___x_2631_ = lean_array_uget_borrowed(v_as_2627_, v_i_2628_);
                    v___x_2632_ = lean_name_eq(v_a_2626_, v___x_2631_);
                    if v___x_2632_ == 0 {
                        v___x_2633_ = 1usize;
                        v___x_2634_ = lean_usize_add(v_i_2628_, v___x_2633_);
                        v_i_2628_ = v___x_2634_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2632_;
                    }
                } else {
                    v___x_2636_ = 0;
                    return v___x_2636_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1___boxed(
    mut v_a_2637_: *mut crate::leanh::LeanObject,
    mut v_as_2638_: *mut crate::leanh::LeanObject,
    mut v_i_2639_: *mut crate::leanh::LeanObject,
    mut v_stop_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2641_: usize = 0;
    let mut v_stop_boxed_2642_: usize = 0;
    let mut v_res_2643_: u8 = 0;
    let mut v_r_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2641_ = crate::leanh::lean_unbox_usize(v_i_2639_);
    crate::leanh::lean_dec(v_i_2639_);
    v_stop_boxed_2642_ = crate::leanh::lean_unbox_usize(v_stop_2640_);
    crate::leanh::lean_dec(v_stop_2640_);
    v_res_2643_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1(v_a_2637_, v_as_2638_, v_i_boxed_2641_, v_stop_boxed_2642_);
    crate::leanh::lean_dec_ref(v_as_2638_);
    crate::leanh::lean_dec(v_a_2637_);
    v_r_2644_ = crate::leanh::lean_box((v_res_2643_) as usize);
    return v_r_2644_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1(
    mut v_as_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    v___x_2647_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2648_ = lean_array_get_size(v_as_2645_);
    v___x_2649_ = lean_nat_dec_lt(v___x_2647_, v___x_2648_);
    if v___x_2649_ == 0 {
        return v___x_2649_;
    } else {
        if v___x_2649_ == 0 {
            return v___x_2649_;
        } else {
            let mut v___x_2650_: usize = 0;
            let mut v___x_2651_: usize = 0;
            let mut v___x_2652_: u8 = 0;
            v___x_2650_ = 0usize;
            v___x_2651_ = lean_usize_of_nat(v___x_2648_);
            v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1(v_a_2646_, v_as_2645_, v___x_2650_, v___x_2651_);
            return v___x_2652_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1___boxed(
    mut v_as_2653_: *mut crate::leanh::LeanObject,
    mut v_a_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2655_: u8 = 0;
    let mut v_r_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1(v_as_2653_, v_a_2654_);
    crate::leanh::lean_dec(v_a_2654_);
    crate::leanh::lean_dec_ref(v_as_2653_);
    v_r_2656_ = crate::leanh::lean_box((v_res_2655_) as usize);
    return v_r_2656_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0;
    v___x_2659_ = l_Lean_stringToMessageData(v___x_2658_);
    return v___x_2659_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2;
    v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
    return v___x_2662_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4;
    v___x_2665_ = l_Lean_stringToMessageData(v___x_2664_);
    return v___x_2665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(
    mut v_declName_2666_: *mut crate::leanh::LeanObject,
    mut v_as_2667_: *mut crate::leanh::LeanObject,
    mut v_sz_2668_: usize,
    mut v_i_2669_: usize,
    mut v_b_2670_: *mut crate::leanh::LeanObject,
    mut v___y_2671_: *mut crate::leanh::LeanObject,
    mut v___y_2672_: *mut crate::leanh::LeanObject,
    mut v___y_2673_: *mut crate::leanh::LeanObject,
    mut v___y_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: usize = 0;
    let mut v___x_2682_: usize = 0;
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2684_ = lean_usize_dec_lt(v_i_2669_, v_sz_2668_);
                if v___x_2684_ == 0 {
                    crate::leanh::lean_dec(v_declName_2666_);
                    v___x_2685_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2685_, 0, v_b_2670_);
                    return v___x_2685_;
                } else {
                    v___x_2686_ = lean_st_ref_get(v___y_2677_);
                    v_env_2687_ = crate::leanh::lean_ctor_get(v___x_2686_, 0);
                    crate::leanh::lean_inc_ref(v_env_2687_);
                    crate::leanh::lean_dec(v___x_2686_);
                    v___x_2688_ = crate::leanh::lean_box(0);
                    v_a_2689_ = lean_array_uget_borrowed(v_as_2667_, v_i_2669_);
                    v___x_2690_ = l_Lean_Environment_header(v_env_2687_);
                    crate::leanh::lean_dec_ref(v_env_2687_);
                    v___x_2691_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2690_);
                    v___x_2692_ = l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1(v___x_2691_, v_a_2689_);
                    crate::leanh::lean_dec_ref(v___x_2691_);
                    if v___x_2692_ == 0 {
                        v___x_2693_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1);
                        crate::leanh::lean_inc(v_declName_2666_);
                        v___x_2694_ = l_Lean_MessageData_ofConstName(v_declName_2666_, v___x_2692_);
                        v___x_2695_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2695_, 0, v___x_2693_);
                        crate::leanh::lean_ctor_set(v___x_2695_, 1, v___x_2694_);
                        v___x_2696_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3);
                        v___x_2697_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2697_, 0, v___x_2695_);
                        crate::leanh::lean_ctor_set(v___x_2697_, 1, v___x_2696_);
                        crate::leanh::lean_inc(v_a_2689_);
                        v___x_2698_ = l_Lean_MessageData_ofName(v_a_2689_);
                        v___x_2699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2699_, 0, v___x_2697_);
                        crate::leanh::lean_ctor_set(v___x_2699_, 1, v___x_2698_);
                        v___x_2700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5);
                        v___x_2701_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2701_, 0, v___x_2699_);
                        crate::leanh::lean_ctor_set(v___x_2701_, 1, v___x_2700_);
                        v___x_2702_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(v___x_2701_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
                        if crate::leanh::lean_obj_tag(v___x_2702_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2702_, 1);
                            v_a_2680_ = v___x_2688_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_declName_2666_);
                            return v___x_2702_;
                        }
                    } else {
                        v_a_2680_ = v___x_2688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2681_ = 1usize;
                v___x_2682_ = lean_usize_add(v_i_2669_, v___x_2681_);
                v_i_2669_ = v___x_2682_;
                v_b_2670_ = v_a_2680_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___boxed(
    mut v_declName_2703_: *mut crate::leanh::LeanObject,
    mut v_as_2704_: *mut crate::leanh::LeanObject,
    mut v_sz_2705_: *mut crate::leanh::LeanObject,
    mut v_i_2706_: *mut crate::leanh::LeanObject,
    mut v_b_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
    mut v___y_2711_: *mut crate::leanh::LeanObject,
    mut v___y_2712_: *mut crate::leanh::LeanObject,
    mut v___y_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2716_: usize = 0;
    let mut v_i_boxed_2717_: usize = 0;
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2716_ = crate::leanh::lean_unbox_usize(v_sz_2705_);
    crate::leanh::lean_dec(v_sz_2705_);
    v_i_boxed_2717_ = crate::leanh::lean_unbox_usize(v_i_2706_);
    crate::leanh::lean_dec(v_i_2706_);
    v_res_2718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(v_declName_2703_, v_as_2704_, v_sz_boxed_2716_, v_i_boxed_2717_, v_b_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
    crate::leanh::lean_dec(v___y_2714_);
    crate::leanh::lean_dec_ref(v___y_2713_);
    crate::leanh::lean_dec(v___y_2712_);
    crate::leanh::lean_dec_ref(v___y_2711_);
    crate::leanh::lean_dec(v___y_2710_);
    crate::leanh::lean_dec_ref(v___y_2709_);
    crate::leanh::lean_dec(v___y_2708_);
    crate::leanh::lean_dec_ref(v_as_2704_);
    return v_res_2718_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed(
    mut v_declName_2719_: *mut crate::leanh::LeanObject,
    mut v_inline_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_is_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2742_: usize = 0;
    let mut v___x_2743_: usize = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2751_: u8 = 0;
    let mut v_unused_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2762_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2766_: u8 = 0;
    let mut v_unused_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_unused_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2793_: usize = 0;
    let mut v___x_2794_: usize = 0;
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2798_: u8 = 0;
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2802_: u8 = 0;
    let mut v_unused_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_handler_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2812_: usize = 0;
    let mut v___x_2813_: usize = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_inline_2720_) {
                0 => {
                    crate::leanh::lean_dec(v_declName_2719_);
                    state = 1;
                    continue;
                }
                1 => {
                    v_content_2753_ = crate::leanh::lean_ctor_get(v_inline_2720_, 0);
                    v_is_2733_ = v_content_2753_;
                    v___y_2734_ = v_a_2721_;
                    v___y_2735_ = v_a_2722_;
                    v___y_2736_ = v_a_2723_;
                    v___y_2737_ = v_a_2724_;
                    v___y_2738_ = v_a_2725_;
                    v___y_2739_ = v_a_2726_;
                    v___y_2740_ = v_a_2727_;
                    state = 2;
                    continue;
                }
                2 => {
                    v_content_2754_ = crate::leanh::lean_ctor_get(v_inline_2720_, 0);
                    v_is_2733_ = v_content_2754_;
                    v___y_2734_ = v_a_2721_;
                    v___y_2735_ = v_a_2722_;
                    v___y_2736_ = v_a_2723_;
                    v___y_2737_ = v_a_2724_;
                    v___y_2738_ = v_a_2725_;
                    v___y_2739_ = v_a_2726_;
                    v___y_2740_ = v_a_2727_;
                    state = 2;
                    continue;
                }
                3 => {
                    crate::leanh::lean_dec(v_declName_2719_);
                    state = 1;
                    continue;
                }
                5 => {
                    crate::leanh::lean_dec(v_declName_2719_);
                    state = 1;
                    continue;
                }
                6 => {
                    v_content_2755_ = crate::leanh::lean_ctor_get(v_inline_2720_, 0);
                    v___x_2756_ = crate::leanh::lean_box(0);
                    v_sz_2757_ = lean_array_size(v_content_2755_);
                    v___x_2758_ = 0usize;
                    v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_2719_, v_content_2755_, v_sz_2757_, v___x_2758_, v___x_2756_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
                    if crate::leanh::lean_obj_tag(v___x_2759_) == 0 {
                        v_isSharedCheck_2766_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2759_)) as u8;
                        if v_isSharedCheck_2766_ == 0 {
                            v_unused_2767_ = crate::leanh::lean_ctor_get(v___x_2759_, 0);
                            crate::leanh::lean_dec(v_unused_2767_);
                            v___x_2761_ = v___x_2759_;
                            v_isShared_2762_ = v_isSharedCheck_2766_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2759_);
                            v___x_2761_ = crate::leanh::lean_box(0);
                            v_isShared_2762_ = v_isSharedCheck_2766_;
                            state = 5;
                            continue;
                        }
                    } else {
                        return v___x_2759_;
                    }
                }
                7 => {
                    v_content_2768_ = crate::leanh::lean_ctor_get(v_inline_2720_, 1);
                    v___x_2769_ = crate::leanh::lean_box(0);
                    v_sz_2770_ = lean_array_size(v_content_2768_);
                    v___x_2771_ = 0usize;
                    v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_2719_, v_content_2768_, v_sz_2770_, v___x_2771_, v___x_2769_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
                    if crate::leanh::lean_obj_tag(v___x_2772_) == 0 {
                        v_isSharedCheck_2779_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2772_)) as u8;
                        if v_isSharedCheck_2779_ == 0 {
                            v_unused_2780_ = crate::leanh::lean_ctor_get(v___x_2772_, 0);
                            crate::leanh::lean_dec(v_unused_2780_);
                            v___x_2774_ = v___x_2772_;
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2772_);
                            v___x_2774_ = crate::leanh::lean_box(0);
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 7;
                            continue;
                        }
                    } else {
                        return v___x_2772_;
                    }
                }
                9 => {
                    v_content_2781_ = crate::leanh::lean_ctor_get(v_inline_2720_, 0);
                    v_is_2733_ = v_content_2781_;
                    v___y_2734_ = v_a_2721_;
                    v___y_2735_ = v_a_2722_;
                    v___y_2736_ = v_a_2723_;
                    v___y_2737_ = v_a_2724_;
                    v___y_2738_ = v_a_2725_;
                    v___y_2739_ = v_a_2726_;
                    v___y_2740_ = v_a_2727_;
                    state = 2;
                    continue;
                }
                10 => {
                    v_container_2782_ = crate::leanh::lean_ctor_get(v_inline_2720_, 0);
                    v_content_2783_ = crate::leanh::lean_ctor_get(v_inline_2720_, 1);
                    v_val_2804_ = crate::leanh::lean_ctor_get(v_container_2782_, 1);
                    v___x_2805_ = l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_;
                    v___x_2806_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                        v_val_2804_,
                        v___x_2805_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2806_) == 1 {
                        v_val_2807_ = crate::leanh::lean_ctor_get(v___x_2806_, 0);
                        crate::leanh::lean_inc(v_val_2807_);
                        crate::leanh::lean_dec_ref_known(v___x_2806_, 1);
                        v_handler_2808_ = crate::leanh::lean_ctor_get(v_val_2807_, 0);
                        crate::leanh::lean_inc(v_handler_2808_);
                        v_imports_2809_ = crate::leanh::lean_ctor_get(v_val_2807_, 1);
                        crate::leanh::lean_inc_ref(v_imports_2809_);
                        v_info_2810_ = crate::leanh::lean_ctor_get(v_val_2807_, 2);
                        crate::leanh::lean_inc(v_info_2810_);
                        crate::leanh::lean_dec(v_val_2807_);
                        v___x_2811_ = crate::leanh::lean_box(0);
                        v_sz_2812_ = lean_array_size(v_imports_2809_);
                        v___x_2813_ = 0usize;
                        crate::leanh::lean_inc(v_declName_2719_);
                        v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(v_declName_2719_, v_imports_2809_, v_sz_2812_, v___x_2813_, v___x_2811_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
                        crate::leanh::lean_dec_ref(v_imports_2809_);
                        if crate::leanh::lean_obj_tag(v___x_2814_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2814_, 1);
                            v___x_2815_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(v_handler_2808_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
                            if crate::leanh::lean_obj_tag(v___x_2815_) == 0 {
                                v_a_2816_ = crate::leanh::lean_ctor_get(v___x_2815_, 0);
                                crate::leanh::lean_inc(v_a_2816_);
                                crate::leanh::lean_dec_ref_known(v___x_2815_, 1);
                                crate::leanh::lean_inc(v_declName_2719_);
                                v___x_2817_ = crate::leanh::lean_apply_2(
                                    v_a_2816_,
                                    v_declName_2719_,
                                    v_info_2810_,
                                );
                                v___x_2818_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(v___x_2817_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
                                if crate::leanh::lean_obj_tag(v___x_2818_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2818_, 1);
                                    v___y_2785_ = v_a_2721_;
                                    v___y_2786_ = v_a_2722_;
                                    v___y_2787_ = v_a_2723_;
                                    v___y_2788_ = v_a_2724_;
                                    v___y_2789_ = v_a_2725_;
                                    v___y_2790_ = v_a_2726_;
                                    v___y_2791_ = v_a_2727_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_declName_2719_);
                                    return v___x_2818_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_info_2810_);
                                crate::leanh::lean_dec(v_declName_2719_);
                                v_a_2819_ = crate::leanh::lean_ctor_get(v___x_2815_, 0);
                                v_isSharedCheck_2826_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2815_)) as u8;
                                if v_isSharedCheck_2826_ == 0 {
                                    v___x_2821_ = v___x_2815_;
                                    v_isShared_2822_ = v_isSharedCheck_2826_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2819_);
                                    crate::leanh::lean_dec(v___x_2815_);
                                    v___x_2821_ = crate::leanh::lean_box(0);
                                    v_isShared_2822_ = v_isSharedCheck_2826_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_info_2810_);
                            crate::leanh::lean_dec(v_handler_2808_);
                            crate::leanh::lean_dec(v_declName_2719_);
                            return v___x_2814_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2806_);
                        v___y_2785_ = v_a_2721_;
                        v___y_2786_ = v_a_2722_;
                        v___y_2787_ = v_a_2723_;
                        v___y_2788_ = v_a_2724_;
                        v___y_2789_ = v_a_2725_;
                        v___y_2790_ = v_a_2726_;
                        v___y_2791_ = v_a_2727_;
                        state = 9;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_declName_2719_);
                    v___x_2827_ = crate::leanh::lean_box(0);
                    v___x_2828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2828_, 0, v___x_2827_);
                    return v___x_2828_;
                }
            },
            1 => {
                v___x_2730_ = crate::leanh::lean_box(0);
                v___x_2731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2731_, 0, v___x_2730_);
                return v___x_2731_;
            }
            2 => {
                v___x_2741_ = crate::leanh::lean_box(0);
                v_sz_2742_ = lean_array_size(v_is_2733_);
                v___x_2743_ = 0usize;
                v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_2719_, v_is_2733_, v_sz_2742_, v___x_2743_, v___x_2741_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
                if crate::leanh::lean_obj_tag(v___x_2744_) == 0 {
                    v_isSharedCheck_2751_ = (!crate::leanh::lean_is_exclusive(v___x_2744_)) as u8;
                    if v_isSharedCheck_2751_ == 0 {
                        v_unused_2752_ = crate::leanh::lean_ctor_get(v___x_2744_, 0);
                        crate::leanh::lean_dec(v_unused_2752_);
                        v___x_2746_ = v___x_2744_;
                        v_isShared_2747_ = v_isSharedCheck_2751_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2744_);
                        v___x_2746_ = crate::leanh::lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2751_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_2744_;
                }
            }
            3 => {
                if v_isShared_2747_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2746_, 0, v___x_2741_);
                    v___x_2749_ = v___x_2746_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2741_);
                    v___x_2749_ = v_reuseFailAlloc_2750_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2749_;
            }
            5 => {
                if v_isShared_2762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2761_, 0, v___x_2756_);
                    v___x_2764_ = v___x_2761_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2756_);
                    v___x_2764_ = v_reuseFailAlloc_2765_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2764_;
            }
            7 => {
                if v_isShared_2775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2774_, 0, v___x_2769_);
                    v___x_2777_ = v___x_2774_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2769_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2777_;
            }
            9 => {
                v___x_2792_ = crate::leanh::lean_box(0);
                v_sz_2793_ = lean_array_size(v_content_2783_);
                v___x_2794_ = 0usize;
                v___x_2795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_2719_, v_content_2783_, v_sz_2793_, v___x_2794_, v___x_2792_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
                if crate::leanh::lean_obj_tag(v___x_2795_) == 0 {
                    v_isSharedCheck_2802_ = (!crate::leanh::lean_is_exclusive(v___x_2795_)) as u8;
                    if v_isSharedCheck_2802_ == 0 {
                        v_unused_2803_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                        crate::leanh::lean_dec(v_unused_2803_);
                        v___x_2797_ = v___x_2795_;
                        v_isShared_2798_ = v_isSharedCheck_2802_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2795_);
                        v___x_2797_ = crate::leanh::lean_box(0);
                        v_isShared_2798_ = v_isSharedCheck_2802_;
                        state = 10;
                        continue;
                    }
                } else {
                    return v___x_2795_;
                }
            }
            10 => {
                if v_isShared_2798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2797_, 0, v___x_2792_);
                    v___x_2800_ = v___x_2797_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2792_);
                    v___x_2800_ = v_reuseFailAlloc_2801_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2800_;
            }
            12 => {
                if v_isShared_2822_ == 0 {
                    v___x_2824_ = v___x_2821_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2825_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(
    mut v_declName_2829_: *mut crate::leanh::LeanObject,
    mut v_as_2830_: *mut crate::leanh::LeanObject,
    mut v_sz_2831_: usize,
    mut v_i_2832_: usize,
    mut v_b_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: usize = 0;
    let mut v___x_2848_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2842_ = lean_usize_dec_lt(v_i_2832_, v_sz_2831_);
                if v___x_2842_ == 0 {
                    crate::leanh::lean_dec(v_declName_2829_);
                    v___x_2843_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2843_, 0, v_b_2833_);
                    return v___x_2843_;
                } else {
                    v_a_2844_ = lean_array_uget_borrowed(v_as_2830_, v_i_2832_);
                    crate::leanh::lean_inc(v_declName_2829_);
                    v___x_2845_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed(v_declName_2829_, v_a_2844_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
                    if crate::leanh::lean_obj_tag(v___x_2845_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2845_, 1);
                        v___x_2846_ = crate::leanh::lean_box(0);
                        v___x_2847_ = 1usize;
                        v___x_2848_ = lean_usize_add(v_i_2832_, v___x_2847_);
                        v_i_2832_ = v___x_2848_;
                        v_b_2833_ = v___x_2846_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_2829_);
                        return v___x_2845_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0___boxed(
    mut v_declName_2850_: *mut crate::leanh::LeanObject,
    mut v_as_2851_: *mut crate::leanh::LeanObject,
    mut v_sz_2852_: *mut crate::leanh::LeanObject,
    mut v_i_2853_: *mut crate::leanh::LeanObject,
    mut v_b_2854_: *mut crate::leanh::LeanObject,
    mut v___y_2855_: *mut crate::leanh::LeanObject,
    mut v___y_2856_: *mut crate::leanh::LeanObject,
    mut v___y_2857_: *mut crate::leanh::LeanObject,
    mut v___y_2858_: *mut crate::leanh::LeanObject,
    mut v___y_2859_: *mut crate::leanh::LeanObject,
    mut v___y_2860_: *mut crate::leanh::LeanObject,
    mut v___y_2861_: *mut crate::leanh::LeanObject,
    mut v___y_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2863_: usize = 0;
    let mut v_i_boxed_2864_: usize = 0;
    let mut v_res_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2863_ = crate::leanh::lean_unbox_usize(v_sz_2852_);
    crate::leanh::lean_dec(v_sz_2852_);
    v_i_boxed_2864_ = crate::leanh::lean_unbox_usize(v_i_2853_);
    crate::leanh::lean_dec(v_i_2853_);
    v_res_2865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_2850_, v_as_2851_, v_sz_boxed_2863_, v_i_boxed_2864_, v_b_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
    crate::leanh::lean_dec(v___y_2861_);
    crate::leanh::lean_dec_ref(v___y_2860_);
    crate::leanh::lean_dec(v___y_2859_);
    crate::leanh::lean_dec_ref(v___y_2858_);
    crate::leanh::lean_dec(v___y_2857_);
    crate::leanh::lean_dec_ref(v___y_2856_);
    crate::leanh::lean_dec(v___y_2855_);
    crate::leanh::lean_dec_ref(v_as_2851_);
    return v_res_2865_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed___boxed(
    mut v_declName_2866_: *mut crate::leanh::LeanObject,
    mut v_inline_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_a_2869_: *mut crate::leanh::LeanObject,
    mut v_a_2870_: *mut crate::leanh::LeanObject,
    mut v_a_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2876_ =
        l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed(
            v_declName_2866_,
            v_inline_2867_,
            v_a_2868_,
            v_a_2869_,
            v_a_2870_,
            v_a_2871_,
            v_a_2872_,
            v_a_2873_,
            v_a_2874_,
        );
    crate::leanh::lean_dec(v_a_2874_);
    crate::leanh::lean_dec_ref(v_a_2873_);
    crate::leanh::lean_dec(v_a_2872_);
    crate::leanh::lean_dec_ref(v_a_2871_);
    crate::leanh::lean_dec(v_a_2870_);
    crate::leanh::lean_dec_ref(v_a_2869_);
    crate::leanh::lean_dec(v_a_2868_);
    crate::leanh::lean_dec_ref(v_inline_2867_);
    return v_res_2876_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2(
    mut v_00_u03b1_2877_: *mut crate::leanh::LeanObject,
    mut v_msg_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2887_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(v_msg_2878_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
    return v___x_2887_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___boxed(
    mut v_00_u03b1_2888_: *mut crate::leanh::LeanObject,
    mut v_msg_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2898_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2(v_00_u03b1_2888_, v_msg_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec_ref(v___y_2895_);
    crate::leanh::lean_dec(v___y_2894_);
    crate::leanh::lean_dec_ref(v___y_2893_);
    crate::leanh::lean_dec(v___y_2892_);
    crate::leanh::lean_dec_ref(v___y_2891_);
    crate::leanh::lean_dec(v___y_2890_);
    return v_res_2898_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(
    mut v_declName_2899_: *mut crate::leanh::LeanObject,
    mut v_as_2900_: *mut crate::leanh::LeanObject,
    mut v_sz_2901_: usize,
    mut v_i_2902_: usize,
    mut v_b_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
    mut v___y_2906_: *mut crate::leanh::LeanObject,
    mut v___y_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2916_: usize = 0;
    let mut v___x_2917_: usize = 0;
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: usize = 0;
    let mut v___x_2920_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2912_ = lean_usize_dec_lt(v_i_2902_, v_sz_2901_);
                if v___x_2912_ == 0 {
                    crate::leanh::lean_dec(v_declName_2899_);
                    v___x_2913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2913_, 0, v_b_2903_);
                    return v___x_2913_;
                } else {
                    v___x_2914_ = crate::leanh::lean_box(0);
                    v_a_2915_ = lean_array_uget_borrowed(v_as_2900_, v_i_2902_);
                    v_sz_2916_ = lean_array_size(v_a_2915_);
                    v___x_2917_ = 0usize;
                    crate::leanh::lean_inc(v_declName_2899_);
                    v___x_2918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_2899_, v_a_2915_, v_sz_2916_, v___x_2917_, v___x_2914_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
                    if crate::leanh::lean_obj_tag(v___x_2918_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2918_, 1);
                        v___x_2919_ = 1usize;
                        v___x_2920_ = lean_usize_add(v_i_2902_, v___x_2919_);
                        v_i_2902_ = v___x_2920_;
                        v_b_2903_ = v___x_2914_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_2899_);
                        return v___x_2918_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2(
    mut v_declName_2922_: *mut crate::leanh::LeanObject,
    mut v_as_2923_: *mut crate::leanh::LeanObject,
    mut v_sz_2924_: usize,
    mut v_i_2925_: usize,
    mut v_b_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
    mut v___y_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2935_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2941_: usize = 0;
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2944_: usize = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: usize = 0;
    let mut v___x_2947_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2935_ = lean_usize_dec_lt(v_i_2925_, v_sz_2924_);
                if v___x_2935_ == 0 {
                    crate::leanh::lean_dec(v_declName_2922_);
                    v___x_2936_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2936_, 0, v_b_2926_);
                    return v___x_2936_;
                } else {
                    v_a_2937_ = lean_array_uget_borrowed(v_as_2923_, v_i_2925_);
                    v_term_2938_ = crate::leanh::lean_ctor_get(v_a_2937_, 0);
                    v_desc_2939_ = crate::leanh::lean_ctor_get(v_a_2937_, 1);
                    v___x_2940_ = crate::leanh::lean_box(0);
                    v_sz_2941_ = lean_array_size(v_term_2938_);
                    v___x_2942_ = 0usize;
                    crate::leanh::lean_inc(v_declName_2922_);
                    v___x_2943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_2922_, v_term_2938_, v_sz_2941_, v___x_2942_, v___x_2940_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
                    if crate::leanh::lean_obj_tag(v___x_2943_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2943_, 1);
                        v_sz_2944_ = lean_array_size(v_desc_2939_);
                        crate::leanh::lean_inc(v_declName_2922_);
                        v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_2922_, v_desc_2939_, v_sz_2944_, v___x_2942_, v___x_2940_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
                        if crate::leanh::lean_obj_tag(v___x_2945_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2945_, 1);
                            v___x_2946_ = 1usize;
                            v___x_2947_ = lean_usize_add(v_i_2925_, v___x_2946_);
                            v_i_2925_ = v___x_2947_;
                            v_b_2926_ = v___x_2940_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_declName_2922_);
                            return v___x_2945_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_2922_);
                        return v___x_2943_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed(
    mut v_declName_2949_: *mut crate::leanh::LeanObject,
    mut v_doc_2950_: *mut crate::leanh::LeanObject,
    mut v_a_2951_: *mut crate::leanh::LeanObject,
    mut v_a_2952_: *mut crate::leanh::LeanObject,
    mut v_a_2953_: *mut crate::leanh::LeanObject,
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bs_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2969_: usize = 0;
    let mut v___x_2970_: usize = 0;
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_unused_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2982_: usize = 0;
    let mut v___x_2983_: usize = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2987_: u8 = 0;
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2991_: u8 = 0;
    let mut v_unused_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3000_: u8 = 0;
    let mut v_unused_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3004_: usize = 0;
    let mut v___x_3005_: usize = 0;
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v_unused_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3017_: usize = 0;
    let mut v___x_3018_: usize = 0;
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3026_: u8 = 0;
    let mut v_unused_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3030_: usize = 0;
    let mut v___x_3031_: usize = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_unused_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_container_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3052_: usize = 0;
    let mut v___x_3053_: usize = 0;
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3057_: u8 = 0;
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut v_unused_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_handler_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3071_: usize = 0;
    let mut v___x_3072_: usize = 0;
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3081_: u8 = 0;
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_items_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_doc_2950_) {
                0 => {
                    v_contents_2980_ = crate::leanh::lean_ctor_get(v_doc_2950_, 0);
                    crate::leanh::lean_inc_ref(v_contents_2980_);
                    crate::leanh::lean_dec_ref_known(v_doc_2950_, 1);
                    v___x_2981_ = crate::leanh::lean_box(0);
                    v_sz_2982_ = lean_array_size(v_contents_2980_);
                    v___x_2983_ = 0usize;
                    v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_2949_, v_contents_2980_, v_sz_2982_, v___x_2983_, v___x_2981_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
                    crate::leanh::lean_dec_ref(v_contents_2980_);
                    if crate::leanh::lean_obj_tag(v___x_2984_) == 0 {
                        v_isSharedCheck_2991_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2984_)) as u8;
                        if v_isSharedCheck_2991_ == 0 {
                            v_unused_2992_ = crate::leanh::lean_ctor_get(v___x_2984_, 0);
                            crate::leanh::lean_dec(v_unused_2992_);
                            v___x_2986_ = v___x_2984_;
                            v_isShared_2987_ = v_isSharedCheck_2991_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2984_);
                            v___x_2986_ = crate::leanh::lean_box(0);
                            v_isShared_2987_ = v_isSharedCheck_2991_;
                            state = 4;
                            continue;
                        }
                    } else {
                        return v___x_2984_;
                    }
                }
                1 => {
                    crate::leanh::lean_dec(v_declName_2949_);
                    v_isSharedCheck_3000_ = (!crate::leanh::lean_is_exclusive(v_doc_2950_)) as u8;
                    if v_isSharedCheck_3000_ == 0 {
                        v_unused_3001_ = crate::leanh::lean_ctor_get(v_doc_2950_, 0);
                        crate::leanh::lean_dec(v_unused_3001_);
                        v___x_2994_ = v_doc_2950_;
                        v_isShared_2995_ = v_isSharedCheck_3000_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_doc_2950_);
                        v___x_2994_ = crate::leanh::lean_box(0);
                        v_isShared_2995_ = v_isSharedCheck_3000_;
                        state = 6;
                        continue;
                    }
                }
                2 => {
                    v_items_3002_ = crate::leanh::lean_ctor_get(v_doc_2950_, 0);
                    crate::leanh::lean_inc_ref(v_items_3002_);
                    crate::leanh::lean_dec_ref_known(v_doc_2950_, 1);
                    v___x_3003_ = crate::leanh::lean_box(0);
                    v_sz_3004_ = lean_array_size(v_items_3002_);
                    v___x_3005_ = 0usize;
                    v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(v_declName_2949_, v_items_3002_, v_sz_3004_, v___x_3005_, v___x_3003_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
                    crate::leanh::lean_dec_ref(v_items_3002_);
                    if crate::leanh::lean_obj_tag(v___x_3006_) == 0 {
                        v_isSharedCheck_3013_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3006_)) as u8;
                        if v_isSharedCheck_3013_ == 0 {
                            v_unused_3014_ = crate::leanh::lean_ctor_get(v___x_3006_, 0);
                            crate::leanh::lean_dec(v_unused_3014_);
                            v___x_3008_ = v___x_3006_;
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3006_);
                            v___x_3008_ = crate::leanh::lean_box(0);
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 8;
                            continue;
                        }
                    } else {
                        return v___x_3006_;
                    }
                }
                3 => {
                    v_items_3015_ = crate::leanh::lean_ctor_get(v_doc_2950_, 1);
                    crate::leanh::lean_inc_ref(v_items_3015_);
                    crate::leanh::lean_dec_ref_known(v_doc_2950_, 2);
                    v___x_3016_ = crate::leanh::lean_box(0);
                    v_sz_3017_ = lean_array_size(v_items_3015_);
                    v___x_3018_ = 0usize;
                    v___x_3019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(v_declName_2949_, v_items_3015_, v_sz_3017_, v___x_3018_, v___x_3016_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
                    crate::leanh::lean_dec_ref(v_items_3015_);
                    if crate::leanh::lean_obj_tag(v___x_3019_) == 0 {
                        v_isSharedCheck_3026_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3019_)) as u8;
                        if v_isSharedCheck_3026_ == 0 {
                            v_unused_3027_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                            crate::leanh::lean_dec(v_unused_3027_);
                            v___x_3021_ = v___x_3019_;
                            v_isShared_3022_ = v_isSharedCheck_3026_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3019_);
                            v___x_3021_ = crate::leanh::lean_box(0);
                            v_isShared_3022_ = v_isSharedCheck_3026_;
                            state = 10;
                            continue;
                        }
                    } else {
                        return v___x_3019_;
                    }
                }
                4 => {
                    v_items_3028_ = crate::leanh::lean_ctor_get(v_doc_2950_, 0);
                    crate::leanh::lean_inc_ref(v_items_3028_);
                    crate::leanh::lean_dec_ref_known(v_doc_2950_, 1);
                    v___x_3029_ = crate::leanh::lean_box(0);
                    v_sz_3030_ = lean_array_size(v_items_3028_);
                    v___x_3031_ = 0usize;
                    v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2(v_declName_2949_, v_items_3028_, v_sz_3030_, v___x_3031_, v___x_3029_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
                    crate::leanh::lean_dec_ref(v_items_3028_);
                    if crate::leanh::lean_obj_tag(v___x_3032_) == 0 {
                        v_isSharedCheck_3039_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3032_)) as u8;
                        if v_isSharedCheck_3039_ == 0 {
                            v_unused_3040_ = crate::leanh::lean_ctor_get(v___x_3032_, 0);
                            crate::leanh::lean_dec(v_unused_3040_);
                            v___x_3034_ = v___x_3032_;
                            v_isShared_3035_ = v_isSharedCheck_3039_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3032_);
                            v___x_3034_ = crate::leanh::lean_box(0);
                            v_isShared_3035_ = v_isSharedCheck_3039_;
                            state = 12;
                            continue;
                        }
                    } else {
                        return v___x_3032_;
                    }
                }
                7 => {
                    v_container_3041_ = crate::leanh::lean_ctor_get(v_doc_2950_, 0);
                    crate::leanh::lean_inc(v_container_3041_);
                    v_content_3042_ = crate::leanh::lean_ctor_get(v_doc_2950_, 1);
                    crate::leanh::lean_inc_ref(v_content_3042_);
                    crate::leanh::lean_dec_ref_known(v_doc_2950_, 2);
                    v_val_3063_ = crate::leanh::lean_ctor_get(v_container_3041_, 1);
                    crate::leanh::lean_inc(v_val_3063_);
                    crate::leanh::lean_dec(v_container_3041_);
                    v___x_3064_ = l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_;
                    v___x_3065_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                        v_val_3063_,
                        v___x_3064_,
                    );
                    crate::leanh::lean_dec(v_val_3063_);
                    if crate::leanh::lean_obj_tag(v___x_3065_) == 1 {
                        v_val_3066_ = crate::leanh::lean_ctor_get(v___x_3065_, 0);
                        crate::leanh::lean_inc(v_val_3066_);
                        crate::leanh::lean_dec_ref_known(v___x_3065_, 1);
                        v_handler_3067_ = crate::leanh::lean_ctor_get(v_val_3066_, 0);
                        crate::leanh::lean_inc(v_handler_3067_);
                        v_imports_3068_ = crate::leanh::lean_ctor_get(v_val_3066_, 1);
                        crate::leanh::lean_inc_ref(v_imports_3068_);
                        v_info_3069_ = crate::leanh::lean_ctor_get(v_val_3066_, 2);
                        crate::leanh::lean_inc(v_info_3069_);
                        crate::leanh::lean_dec(v_val_3066_);
                        v___x_3070_ = crate::leanh::lean_box(0);
                        v_sz_3071_ = lean_array_size(v_imports_3068_);
                        v___x_3072_ = 0usize;
                        crate::leanh::lean_inc(v_declName_2949_);
                        v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(v_declName_2949_, v_imports_3068_, v_sz_3071_, v___x_3072_, v___x_3070_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
                        crate::leanh::lean_dec_ref(v_imports_3068_);
                        if crate::leanh::lean_obj_tag(v___x_3073_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3073_, 1);
                            v___x_3074_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(v_handler_3067_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
                            if crate::leanh::lean_obj_tag(v___x_3074_) == 0 {
                                v_a_3075_ = crate::leanh::lean_ctor_get(v___x_3074_, 0);
                                crate::leanh::lean_inc(v_a_3075_);
                                crate::leanh::lean_dec_ref_known(v___x_3074_, 1);
                                crate::leanh::lean_inc(v_declName_2949_);
                                v___x_3076_ = crate::leanh::lean_apply_2(
                                    v_a_3075_,
                                    v_declName_2949_,
                                    v_info_3069_,
                                );
                                v___x_3077_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(v___x_3076_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
                                if crate::leanh::lean_obj_tag(v___x_3077_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3077_, 1);
                                    v___y_3044_ = v_a_2951_;
                                    v___y_3045_ = v_a_2952_;
                                    v___y_3046_ = v_a_2953_;
                                    v___y_3047_ = v_a_2954_;
                                    v___y_3048_ = v_a_2955_;
                                    v___y_3049_ = v_a_2956_;
                                    v___y_3050_ = v_a_2957_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_content_3042_);
                                    crate::leanh::lean_dec(v_declName_2949_);
                                    return v___x_3077_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_info_3069_);
                                crate::leanh::lean_dec_ref(v_content_3042_);
                                crate::leanh::lean_dec(v_declName_2949_);
                                v_a_3078_ = crate::leanh::lean_ctor_get(v___x_3074_, 0);
                                v_isSharedCheck_3085_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3074_)) as u8;
                                if v_isSharedCheck_3085_ == 0 {
                                    v___x_3080_ = v___x_3074_;
                                    v_isShared_3081_ = v_isSharedCheck_3085_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3078_);
                                    crate::leanh::lean_dec(v___x_3074_);
                                    v___x_3080_ = crate::leanh::lean_box(0);
                                    v_isShared_3081_ = v_isSharedCheck_3085_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_info_3069_);
                            crate::leanh::lean_dec(v_handler_3067_);
                            crate::leanh::lean_dec_ref(v_content_3042_);
                            crate::leanh::lean_dec(v_declName_2949_);
                            return v___x_3073_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3065_);
                        v___y_3044_ = v_a_2951_;
                        v___y_3045_ = v_a_2952_;
                        v___y_3046_ = v_a_2953_;
                        v___y_3047_ = v_a_2954_;
                        v___y_3048_ = v_a_2955_;
                        v___y_3049_ = v_a_2956_;
                        v___y_3050_ = v_a_2957_;
                        state = 14;
                        continue;
                    }
                }
                _ => {
                    v_items_3086_ = crate::leanh::lean_ctor_get(v_doc_2950_, 0);
                    crate::leanh::lean_inc_ref(v_items_3086_);
                    crate::leanh::lean_dec_ref(v_doc_2950_);
                    v_bs_2960_ = v_items_3086_;
                    v___y_2961_ = v_a_2951_;
                    v___y_2962_ = v_a_2952_;
                    v___y_2963_ = v_a_2953_;
                    v___y_2964_ = v_a_2954_;
                    v___y_2965_ = v_a_2955_;
                    v___y_2966_ = v_a_2956_;
                    v___y_2967_ = v_a_2957_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2968_ = crate::leanh::lean_box(0);
                v_sz_2969_ = lean_array_size(v_bs_2960_);
                v___x_2970_ = 0usize;
                v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_2949_, v_bs_2960_, v_sz_2969_, v___x_2970_, v___x_2968_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
                crate::leanh::lean_dec_ref(v_bs_2960_);
                if crate::leanh::lean_obj_tag(v___x_2971_) == 0 {
                    v_isSharedCheck_2978_ = (!crate::leanh::lean_is_exclusive(v___x_2971_)) as u8;
                    if v_isSharedCheck_2978_ == 0 {
                        v_unused_2979_ = crate::leanh::lean_ctor_get(v___x_2971_, 0);
                        crate::leanh::lean_dec(v_unused_2979_);
                        v___x_2973_ = v___x_2971_;
                        v_isShared_2974_ = v_isSharedCheck_2978_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2971_);
                        v___x_2973_ = crate::leanh::lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_2978_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2971_;
                }
            }
            2 => {
                if v_isShared_2974_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2973_, 0, v___x_2968_);
                    v___x_2976_ = v___x_2973_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2968_);
                    v___x_2976_ = v_reuseFailAlloc_2977_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2976_;
            }
            4 => {
                if v_isShared_2987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2986_, 0, v___x_2981_);
                    v___x_2989_ = v___x_2986_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2981_);
                    v___x_2989_ = v_reuseFailAlloc_2990_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2989_;
            }
            6 => {
                v___x_2996_ = crate::leanh::lean_box(0);
                if v_isShared_2995_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2994_, 0);
                    crate::leanh::lean_ctor_set(v___x_2994_, 0, v___x_2996_);
                    v___x_2998_ = v___x_2994_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
                    v___x_2998_ = v_reuseFailAlloc_2999_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2998_;
            }
            8 => {
                if v_isShared_3009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3008_, 0, v___x_3003_);
                    v___x_3011_ = v___x_3008_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3003_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3011_;
            }
            10 => {
                if v_isShared_3022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3021_, 0, v___x_3016_);
                    v___x_3024_ = v___x_3021_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3016_);
                    v___x_3024_ = v_reuseFailAlloc_3025_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3024_;
            }
            12 => {
                if v_isShared_3035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3034_, 0, v___x_3029_);
                    v___x_3037_ = v___x_3034_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3029_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3037_;
            }
            14 => {
                v___x_3051_ = crate::leanh::lean_box(0);
                v_sz_3052_ = lean_array_size(v_content_3042_);
                v___x_3053_ = 0usize;
                v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_2949_, v_content_3042_, v_sz_3052_, v___x_3053_, v___x_3051_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
                crate::leanh::lean_dec_ref(v_content_3042_);
                if crate::leanh::lean_obj_tag(v___x_3054_) == 0 {
                    v_isSharedCheck_3061_ = (!crate::leanh::lean_is_exclusive(v___x_3054_)) as u8;
                    if v_isSharedCheck_3061_ == 0 {
                        v_unused_3062_ = crate::leanh::lean_ctor_get(v___x_3054_, 0);
                        crate::leanh::lean_dec(v_unused_3062_);
                        v___x_3056_ = v___x_3054_;
                        v_isShared_3057_ = v_isSharedCheck_3061_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3054_);
                        v___x_3056_ = crate::leanh::lean_box(0);
                        v_isShared_3057_ = v_isSharedCheck_3061_;
                        state = 15;
                        continue;
                    }
                } else {
                    return v___x_3054_;
                }
            }
            15 => {
                if v_isShared_3057_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3056_, 0, v___x_3051_);
                    v___x_3059_ = v___x_3056_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3051_);
                    v___x_3059_ = v_reuseFailAlloc_3060_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3059_;
            }
            17 => {
                if v_isShared_3081_ == 0 {
                    v___x_3083_ = v___x_3080_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(
    mut v_declName_3087_: *mut crate::leanh::LeanObject,
    mut v_as_3088_: *mut crate::leanh::LeanObject,
    mut v_sz_3089_: usize,
    mut v_i_3090_: usize,
    mut v_b_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: usize = 0;
    let mut v___x_3106_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3100_ = lean_usize_dec_lt(v_i_3090_, v_sz_3089_);
                if v___x_3100_ == 0 {
                    crate::leanh::lean_dec(v_declName_3087_);
                    v___x_3101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3101_, 0, v_b_3091_);
                    return v___x_3101_;
                } else {
                    v_a_3102_ = lean_array_uget_borrowed(v_as_3088_, v_i_3090_);
                    crate::leanh::lean_inc(v_a_3102_);
                    crate::leanh::lean_inc(v_declName_3087_);
                    v___x_3103_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed(v_declName_3087_, v_a_3102_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
                    if crate::leanh::lean_obj_tag(v___x_3103_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3103_, 1);
                        v___x_3104_ = crate::leanh::lean_box(0);
                        v___x_3105_ = 1usize;
                        v___x_3106_ = lean_usize_add(v_i_3090_, v___x_3105_);
                        v_i_3090_ = v___x_3106_;
                        v_b_3091_ = v___x_3104_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_3087_);
                        return v___x_3103_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0___boxed(
    mut v_declName_3108_: *mut crate::leanh::LeanObject,
    mut v_as_3109_: *mut crate::leanh::LeanObject,
    mut v_sz_3110_: *mut crate::leanh::LeanObject,
    mut v_i_3111_: *mut crate::leanh::LeanObject,
    mut v_b_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3121_: usize = 0;
    let mut v_i_boxed_3122_: usize = 0;
    let mut v_res_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3121_ = crate::leanh::lean_unbox_usize(v_sz_3110_);
    crate::leanh::lean_dec(v_sz_3110_);
    v_i_boxed_3122_ = crate::leanh::lean_unbox_usize(v_i_3111_);
    crate::leanh::lean_dec(v_i_3111_);
    v_res_3123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_3108_, v_as_3109_, v_sz_boxed_3121_, v_i_boxed_3122_, v_b_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
    crate::leanh::lean_dec(v___y_3119_);
    crate::leanh::lean_dec_ref(v___y_3118_);
    crate::leanh::lean_dec(v___y_3117_);
    crate::leanh::lean_dec_ref(v___y_3116_);
    crate::leanh::lean_dec(v___y_3115_);
    crate::leanh::lean_dec_ref(v___y_3114_);
    crate::leanh::lean_dec(v___y_3113_);
    crate::leanh::lean_dec_ref(v_as_3109_);
    return v_res_3123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1___boxed(
    mut v_declName_3124_: *mut crate::leanh::LeanObject,
    mut v_as_3125_: *mut crate::leanh::LeanObject,
    mut v_sz_3126_: *mut crate::leanh::LeanObject,
    mut v_i_3127_: *mut crate::leanh::LeanObject,
    mut v_b_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
    mut v___y_3133_: *mut crate::leanh::LeanObject,
    mut v___y_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3137_: usize = 0;
    let mut v_i_boxed_3138_: usize = 0;
    let mut v_res_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3137_ = crate::leanh::lean_unbox_usize(v_sz_3126_);
    crate::leanh::lean_dec(v_sz_3126_);
    v_i_boxed_3138_ = crate::leanh::lean_unbox_usize(v_i_3127_);
    crate::leanh::lean_dec(v_i_3127_);
    v_res_3139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(v_declName_3124_, v_as_3125_, v_sz_boxed_3137_, v_i_boxed_3138_, v_b_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
    crate::leanh::lean_dec(v___y_3135_);
    crate::leanh::lean_dec_ref(v___y_3134_);
    crate::leanh::lean_dec(v___y_3133_);
    crate::leanh::lean_dec_ref(v___y_3132_);
    crate::leanh::lean_dec(v___y_3131_);
    crate::leanh::lean_dec_ref(v___y_3130_);
    crate::leanh::lean_dec(v___y_3129_);
    crate::leanh::lean_dec_ref(v_as_3125_);
    return v_res_3139_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2___boxed(
    mut v_declName_3140_: *mut crate::leanh::LeanObject,
    mut v_as_3141_: *mut crate::leanh::LeanObject,
    mut v_sz_3142_: *mut crate::leanh::LeanObject,
    mut v_i_3143_: *mut crate::leanh::LeanObject,
    mut v_b_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3153_: usize = 0;
    let mut v_i_boxed_3154_: usize = 0;
    let mut v_res_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3153_ = crate::leanh::lean_unbox_usize(v_sz_3142_);
    crate::leanh::lean_dec(v_sz_3142_);
    v_i_boxed_3154_ = crate::leanh::lean_unbox_usize(v_i_3143_);
    crate::leanh::lean_dec(v_i_3143_);
    v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2(v_declName_3140_, v_as_3141_, v_sz_boxed_3153_, v_i_boxed_3154_, v_b_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
    crate::leanh::lean_dec(v___y_3151_);
    crate::leanh::lean_dec_ref(v___y_3150_);
    crate::leanh::lean_dec(v___y_3149_);
    crate::leanh::lean_dec_ref(v___y_3148_);
    crate::leanh::lean_dec(v___y_3147_);
    crate::leanh::lean_dec_ref(v___y_3146_);
    crate::leanh::lean_dec(v___y_3145_);
    crate::leanh::lean_dec_ref(v_as_3141_);
    return v_res_3155_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed___boxed(
    mut v_declName_3156_: *mut crate::leanh::LeanObject,
    mut v_doc_3157_: *mut crate::leanh::LeanObject,
    mut v_a_3158_: *mut crate::leanh::LeanObject,
    mut v_a_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3166_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed(
        v_declName_3156_,
        v_doc_3157_,
        v_a_3158_,
        v_a_3159_,
        v_a_3160_,
        v_a_3161_,
        v_a_3162_,
        v_a_3163_,
        v_a_3164_,
    );
    crate::leanh::lean_dec(v_a_3164_);
    crate::leanh::lean_dec_ref(v_a_3163_);
    crate::leanh::lean_dec(v_a_3162_);
    crate::leanh::lean_dec_ref(v_a_3161_);
    crate::leanh::lean_dec(v_a_3160_);
    crate::leanh::lean_dec_ref(v_a_3159_);
    crate::leanh::lean_dec(v_a_3158_);
    return v_res_3166_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed(
    mut v_declName_3167_: *mut crate::leanh::LeanObject,
    mut v_doc_3168_: *mut crate::leanh::LeanObject,
    mut v_a_3169_: *mut crate::leanh::LeanObject,
    mut v_a_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
    mut v_a_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_content_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subParts_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3180_: usize = 0;
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3183_: usize = 0;
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_unused_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_content_3177_ = crate::leanh::lean_ctor_get(v_doc_3168_, 3);
                v_subParts_3178_ = crate::leanh::lean_ctor_get(v_doc_3168_, 4);
                v___x_3179_ = crate::leanh::lean_box(0);
                v_sz_3180_ = lean_array_size(v_content_3177_);
                v___x_3181_ = 0usize;
                crate::leanh::lean_inc(v_declName_3167_);
                v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_3167_, v_content_3177_, v_sz_3180_, v___x_3181_, v___x_3179_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
                if crate::leanh::lean_obj_tag(v___x_3182_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3182_, 1);
                    v_sz_3183_ = lean_array_size(v_subParts_3178_);
                    v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(v_declName_3167_, v_subParts_3178_, v_sz_3183_, v___x_3181_, v___x_3179_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
                    if crate::leanh::lean_obj_tag(v___x_3184_) == 0 {
                        v_isSharedCheck_3191_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3184_)) as u8;
                        if v_isSharedCheck_3191_ == 0 {
                            v_unused_3192_ = crate::leanh::lean_ctor_get(v___x_3184_, 0);
                            crate::leanh::lean_dec(v_unused_3192_);
                            v___x_3186_ = v___x_3184_;
                            v_isShared_3187_ = v_isSharedCheck_3191_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3184_);
                            v___x_3186_ = crate::leanh::lean_box(0);
                            v_isShared_3187_ = v_isSharedCheck_3191_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3184_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_3167_);
                    return v___x_3182_;
                }
            }
            1 => {
                if v_isShared_3187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3186_, 0, v___x_3179_);
                    v___x_3189_ = v___x_3186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3179_);
                    v___x_3189_ = v_reuseFailAlloc_3190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(
    mut v_declName_3193_: *mut crate::leanh::LeanObject,
    mut v_as_3194_: *mut crate::leanh::LeanObject,
    mut v_sz_3195_: usize,
    mut v_i_3196_: usize,
    mut v_b_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: usize = 0;
    let mut v___x_3212_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3206_ = lean_usize_dec_lt(v_i_3196_, v_sz_3195_);
                if v___x_3206_ == 0 {
                    crate::leanh::lean_dec(v_declName_3193_);
                    v___x_3207_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3207_, 0, v_b_3197_);
                    return v___x_3207_;
                } else {
                    v_a_3208_ = lean_array_uget_borrowed(v_as_3194_, v_i_3196_);
                    crate::leanh::lean_inc(v_declName_3193_);
                    v___x_3209_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed(v_declName_3193_, v_a_3208_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
                    if crate::leanh::lean_obj_tag(v___x_3209_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3209_, 1);
                        v___x_3210_ = crate::leanh::lean_box(0);
                        v___x_3211_ = 1usize;
                        v___x_3212_ = lean_usize_add(v_i_3196_, v___x_3211_);
                        v_i_3196_ = v___x_3212_;
                        v_b_3197_ = v___x_3210_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_3193_);
                        return v___x_3209_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0___boxed(
    mut v_declName_3214_: *mut crate::leanh::LeanObject,
    mut v_as_3215_: *mut crate::leanh::LeanObject,
    mut v_sz_3216_: *mut crate::leanh::LeanObject,
    mut v_i_3217_: *mut crate::leanh::LeanObject,
    mut v_b_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3227_: usize = 0;
    let mut v_i_boxed_3228_: usize = 0;
    let mut v_res_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3227_ = crate::leanh::lean_unbox_usize(v_sz_3216_);
    crate::leanh::lean_dec(v_sz_3216_);
    v_i_boxed_3228_ = crate::leanh::lean_unbox_usize(v_i_3217_);
    crate::leanh::lean_dec(v_i_3217_);
    v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(v_declName_3214_, v_as_3215_, v_sz_boxed_3227_, v_i_boxed_3228_, v_b_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
    crate::leanh::lean_dec(v___y_3225_);
    crate::leanh::lean_dec_ref(v___y_3224_);
    crate::leanh::lean_dec(v___y_3223_);
    crate::leanh::lean_dec_ref(v___y_3222_);
    crate::leanh::lean_dec(v___y_3221_);
    crate::leanh::lean_dec_ref(v___y_3220_);
    crate::leanh::lean_dec(v___y_3219_);
    crate::leanh::lean_dec_ref(v_as_3215_);
    return v_res_3229_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed___boxed(
    mut v_declName_3230_: *mut crate::leanh::LeanObject,
    mut v_doc_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
    mut v_a_3239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3240_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed(
        v_declName_3230_,
        v_doc_3231_,
        v_a_3232_,
        v_a_3233_,
        v_a_3234_,
        v_a_3235_,
        v_a_3236_,
        v_a_3237_,
        v_a_3238_,
    );
    crate::leanh::lean_dec(v_a_3238_);
    crate::leanh::lean_dec_ref(v_a_3237_);
    crate::leanh::lean_dec(v_a_3236_);
    crate::leanh::lean_dec_ref(v_a_3235_);
    crate::leanh::lean_dec(v_a_3234_);
    crate::leanh::lean_dec_ref(v_a_3233_);
    crate::leanh::lean_dec(v_a_3232_);
    crate::leanh::lean_dec_ref(v_doc_3231_);
    return v_res_3240_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(
    mut v_declName_3241_: *mut crate::leanh::LeanObject,
    mut v_doc_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
    mut v_a_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_text_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subsections_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3254_: usize = 0;
    let mut v___x_3255_: usize = 0;
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3257_: usize = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_unused_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_text_3251_ = crate::leanh::lean_ctor_get(v_doc_3242_, 0);
                v_subsections_3252_ = crate::leanh::lean_ctor_get(v_doc_3242_, 1);
                v___x_3253_ = crate::leanh::lean_box(0);
                v_sz_3254_ = lean_array_size(v_text_3251_);
                v___x_3255_ = 0usize;
                crate::leanh::lean_inc(v_declName_3241_);
                v___x_3256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_3241_, v_text_3251_, v_sz_3254_, v___x_3255_, v___x_3253_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
                if crate::leanh::lean_obj_tag(v___x_3256_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3256_, 1);
                    v_sz_3257_ = lean_array_size(v_subsections_3252_);
                    v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(v_declName_3241_, v_subsections_3252_, v_sz_3257_, v___x_3255_, v___x_3253_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
                    if crate::leanh::lean_obj_tag(v___x_3258_) == 0 {
                        v_isSharedCheck_3265_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3258_)) as u8;
                        if v_isSharedCheck_3265_ == 0 {
                            v_unused_3266_ = crate::leanh::lean_ctor_get(v___x_3258_, 0);
                            crate::leanh::lean_dec(v_unused_3266_);
                            v___x_3260_ = v___x_3258_;
                            v_isShared_3261_ = v_isSharedCheck_3265_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3258_);
                            v___x_3260_ = crate::leanh::lean_box(0);
                            v_isShared_3261_ = v_isSharedCheck_3265_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3258_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_3241_);
                    return v___x_3256_;
                }
            }
            1 => {
                if v_isShared_3261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3253_);
                    v___x_3263_ = v___x_3260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3253_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed___boxed(
    mut v_declName_3267_: *mut crate::leanh::LeanObject,
    mut v_doc_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
    mut v_a_3271_: *mut crate::leanh::LeanObject,
    mut v_a_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
    mut v_a_3274_: *mut crate::leanh::LeanObject,
    mut v_a_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ =
        l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(
            v_declName_3267_,
            v_doc_3268_,
            v_a_3269_,
            v_a_3270_,
            v_a_3271_,
            v_a_3272_,
            v_a_3273_,
            v_a_3274_,
            v_a_3275_,
        );
    crate::leanh::lean_dec(v_a_3275_);
    crate::leanh::lean_dec_ref(v_a_3274_);
    crate::leanh::lean_dec(v_a_3273_);
    crate::leanh::lean_dec_ref(v_a_3272_);
    crate::leanh::lean_dec(v_a_3271_);
    crate::leanh::lean_dec_ref(v_a_3270_);
    crate::leanh::lean_dec(v_a_3269_);
    crate::leanh::lean_dec_ref(v_doc_3268_);
    return v_res_3277_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(
    mut v_init_3283_: *mut crate::leanh::LeanObject,
    mut v_x_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
    mut v___y_3288_: *mut crate::leanh::LeanObject,
    mut v___y_3289_: *mut crate::leanh::LeanObject,
    mut v___y_3290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: u8 = 0;
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3284_) == 0 {
                    v_k_3292_ = crate::leanh::lean_ctor_get(v_x_3284_, 1);
                    crate::leanh::lean_inc(v_k_3292_);
                    v_v_3293_ = crate::leanh::lean_ctor_get(v_x_3284_, 2);
                    crate::leanh::lean_inc(v_v_3293_);
                    v_l_3294_ = crate::leanh::lean_ctor_get(v_x_3284_, 3);
                    crate::leanh::lean_inc(v_l_3294_);
                    v_r_3295_ = crate::leanh::lean_ctor_get(v_x_3284_, 4);
                    crate::leanh::lean_inc(v_r_3295_);
                    crate::leanh::lean_dec_ref_known(v_x_3284_, 5);
                    v___x_3296_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_init_3283_, v_l_3294_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
                    if crate::leanh::lean_obj_tag(v___x_3296_) == 0 {
                        v_a_3297_ = crate::leanh::lean_ctor_get(v___x_3296_, 0);
                        crate::leanh::lean_inc(v_a_3297_);
                        crate::leanh::lean_dec_ref_known(v___x_3296_, 1);
                        v_a_3298_ = crate::leanh::lean_ctor_get(v_a_3297_, 0);
                        crate::leanh::lean_inc(v_a_3298_);
                        crate::leanh::lean_dec(v_a_3297_);
                        v___x_3299_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3300_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1;
                        v___x_3301_ = lean_st_mk_ref(v___x_3300_);
                        crate::leanh::lean_inc(v_k_3292_);
                        v___x_3302_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_k_3292_, v_v_3293_, v___x_3301_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
                        crate::leanh::lean_dec(v_v_3293_);
                        if crate::leanh::lean_obj_tag(v___x_3302_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3302_, 1);
                            v___x_3303_ = lean_st_ref_get(v___x_3301_);
                            crate::leanh::lean_dec(v___x_3301_);
                            v___x_3304_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v___x_3303_);
                            v___x_3305_ = lean_nat_dec_lt(v___x_3299_, v___x_3304_);
                            crate::leanh::lean_dec(v___x_3304_);
                            if v___x_3305_ == 0 {
                                crate::leanh::lean_dec(v___x_3303_);
                                crate::leanh::lean_dec(v_k_3292_);
                                v_init_3283_ = v_a_3298_;
                                v_x_3284_ = v_r_3295_;
                                state = 0;
                                continue;
                            } else {
                                v___x_3307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3307_, 0, v_k_3292_);
                                crate::leanh::lean_ctor_set(v___x_3307_, 1, v___x_3303_);
                                v___x_3308_ = lean_array_push(v_a_3298_, v___x_3307_);
                                v_init_3283_ = v___x_3308_;
                                v_x_3284_ = v_r_3295_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3301_);
                            crate::leanh::lean_dec(v_a_3298_);
                            crate::leanh::lean_dec(v_r_3295_);
                            crate::leanh::lean_dec(v_k_3292_);
                            v_a_3310_ = crate::leanh::lean_ctor_get(v___x_3302_, 0);
                            v_isSharedCheck_3317_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3302_)) as u8;
                            if v_isSharedCheck_3317_ == 0 {
                                v___x_3312_ = v___x_3302_;
                                v_isShared_3313_ = v_isSharedCheck_3317_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3310_);
                                crate::leanh::lean_dec(v___x_3302_);
                                v___x_3312_ = crate::leanh::lean_box(0);
                                v_isShared_3313_ = v_isSharedCheck_3317_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_3295_);
                        crate::leanh::lean_dec(v_v_3293_);
                        crate::leanh::lean_dec(v_k_3292_);
                        return v___x_3296_;
                    }
                } else {
                    v___x_3318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3318_, 0, v_init_3283_);
                    v___x_3319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3319_, 0, v___x_3318_);
                    return v___x_3319_;
                }
            }
            1 => {
                if v_isShared_3313_ == 0 {
                    v___x_3315_ = v___x_3312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
                    v___x_3315_ = v_reuseFailAlloc_3316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___boxed(
    mut v_init_3320_: *mut crate::leanh::LeanObject,
    mut v_x_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(
        v_init_3320_,
        v_x_3321_,
        v___y_3322_,
        v___y_3323_,
        v___y_3324_,
        v___y_3325_,
        v___y_3326_,
        v___y_3327_,
    );
    crate::leanh::lean_dec(v___y_3327_);
    crate::leanh::lean_dec_ref(v___y_3326_);
    crate::leanh::lean_dec(v___y_3325_);
    crate::leanh::lean_dec_ref(v___y_3324_);
    crate::leanh::lean_dec(v___y_3323_);
    crate::leanh::lean_dec_ref(v___y_3322_);
    return v_res_3329_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9(
    mut v_init_3330_: *mut crate::leanh::LeanObject,
    mut v_x_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3360_: u8 = 0;
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3331_) == 0 {
                    v_k_3339_ = crate::leanh::lean_ctor_get(v_x_3331_, 1);
                    crate::leanh::lean_inc(v_k_3339_);
                    v_v_3340_ = crate::leanh::lean_ctor_get(v_x_3331_, 2);
                    crate::leanh::lean_inc(v_v_3340_);
                    v_l_3341_ = crate::leanh::lean_ctor_get(v_x_3331_, 3);
                    crate::leanh::lean_inc(v_l_3341_);
                    v_r_3342_ = crate::leanh::lean_ctor_get(v_x_3331_, 4);
                    crate::leanh::lean_inc(v_r_3342_);
                    crate::leanh::lean_dec_ref_known(v_x_3331_, 5);
                    v___x_3343_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_init_3330_, v_l_3341_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
                    if crate::leanh::lean_obj_tag(v___x_3343_) == 0 {
                        v_a_3344_ = crate::leanh::lean_ctor_get(v___x_3343_, 0);
                        crate::leanh::lean_inc(v_a_3344_);
                        crate::leanh::lean_dec_ref_known(v___x_3343_, 1);
                        v_a_3345_ = crate::leanh::lean_ctor_get(v_a_3344_, 0);
                        crate::leanh::lean_inc(v_a_3345_);
                        crate::leanh::lean_dec(v_a_3344_);
                        v___x_3346_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3347_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1;
                        v___x_3348_ = lean_st_mk_ref(v___x_3347_);
                        crate::leanh::lean_inc(v_k_3339_);
                        v___x_3349_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_k_3339_, v_v_3340_, v___x_3348_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
                        crate::leanh::lean_dec(v_v_3340_);
                        if crate::leanh::lean_obj_tag(v___x_3349_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3349_, 1);
                            v___x_3350_ = lean_st_ref_get(v___x_3348_);
                            crate::leanh::lean_dec(v___x_3348_);
                            v___x_3351_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v___x_3350_);
                            v___x_3352_ = lean_nat_dec_lt(v___x_3346_, v___x_3351_);
                            crate::leanh::lean_dec(v___x_3351_);
                            if v___x_3352_ == 0 {
                                crate::leanh::lean_dec(v___x_3350_);
                                crate::leanh::lean_dec(v_k_3339_);
                                v___x_3353_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_a_3345_, v_r_3342_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
                                return v___x_3353_;
                            } else {
                                v___x_3354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3354_, 0, v_k_3339_);
                                crate::leanh::lean_ctor_set(v___x_3354_, 1, v___x_3350_);
                                v___x_3355_ = lean_array_push(v_a_3345_, v___x_3354_);
                                v___x_3356_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v___x_3355_, v_r_3342_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
                                return v___x_3356_;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3348_);
                            crate::leanh::lean_dec(v_a_3345_);
                            crate::leanh::lean_dec(v_r_3342_);
                            crate::leanh::lean_dec(v_k_3339_);
                            v_a_3357_ = crate::leanh::lean_ctor_get(v___x_3349_, 0);
                            v_isSharedCheck_3364_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3349_)) as u8;
                            if v_isSharedCheck_3364_ == 0 {
                                v___x_3359_ = v___x_3349_;
                                v_isShared_3360_ = v_isSharedCheck_3364_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3357_);
                                crate::leanh::lean_dec(v___x_3349_);
                                v___x_3359_ = crate::leanh::lean_box(0);
                                v_isShared_3360_ = v_isSharedCheck_3364_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_3342_);
                        crate::leanh::lean_dec(v_v_3340_);
                        crate::leanh::lean_dec(v_k_3339_);
                        return v___x_3343_;
                    }
                } else {
                    v___x_3365_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3365_, 0, v_init_3330_);
                    v___x_3366_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3366_, 0, v___x_3365_);
                    return v___x_3366_;
                }
            }
            1 => {
                if v_isShared_3360_ == 0 {
                    v___x_3362_ = v___x_3359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
                    v___x_3362_ = v_reuseFailAlloc_3363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9___boxed(
    mut v_init_3367_: *mut crate::leanh::LeanObject,
    mut v_x_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9(
        v_init_3367_,
        v_x_3368_,
        v___y_3369_,
        v___y_3370_,
        v___y_3371_,
        v___y_3372_,
        v___y_3373_,
        v___y_3374_,
    );
    crate::leanh::lean_dec(v___y_3374_);
    crate::leanh::lean_dec_ref(v___y_3373_);
    crate::leanh::lean_dec(v___y_3372_);
    crate::leanh::lean_dec_ref(v___y_3371_);
    crate::leanh::lean_dec(v___y_3370_);
    crate::leanh::lean_dec_ref(v___y_3369_);
    return v_res_3376_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0(
    mut v_as_3377_: *mut crate::leanh::LeanObject,
    mut v_sz_3378_: usize,
    mut v_i_3379_: usize,
    mut v_b_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3388_: u8 = 0;
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: usize = 0;
    let mut v___x_3404_: usize = 0;
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3419_: u8 = 0;
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3388_ = lean_usize_dec_lt(v_i_3379_, v_sz_3378_);
                if v___x_3388_ == 0 {
                    v___x_3389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3389_, 0, v_b_3380_);
                    return v___x_3389_;
                } else {
                    v_a_3390_ = lean_array_uget(v_as_3377_, v_i_3379_);
                    v_fst_3391_ = crate::leanh::lean_ctor_get(v_a_3390_, 0);
                    v_snd_3392_ = crate::leanh::lean_ctor_get(v_a_3390_, 1);
                    v_isSharedCheck_3420_ = (!crate::leanh::lean_is_exclusive(v_a_3390_)) as u8;
                    if v_isSharedCheck_3420_ == 0 {
                        v___x_3394_ = v_a_3390_;
                        v_isShared_3395_ = v_isSharedCheck_3420_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3392_);
                        crate::leanh::lean_inc(v_fst_3391_);
                        crate::leanh::lean_dec(v_a_3390_);
                        v___x_3394_ = crate::leanh::lean_box(0);
                        v_isShared_3395_ = v_isSharedCheck_3420_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3396_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3397_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1;
                v___x_3398_ = lean_st_mk_ref(v___x_3397_);
                crate::leanh::lean_inc(v_fst_3391_);
                v___x_3399_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_fst_3391_, v_snd_3392_, v___x_3398_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
                crate::leanh::lean_dec(v_snd_3392_);
                if crate::leanh::lean_obj_tag(v___x_3399_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3399_, 1);
                    v___x_3400_ = lean_st_ref_get(v___x_3398_);
                    crate::leanh::lean_dec(v___x_3398_);
                    v___x_3406_ =
                        l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(
                            v___x_3400_,
                        );
                    v___x_3407_ = lean_nat_dec_lt(v___x_3396_, v___x_3406_);
                    crate::leanh::lean_dec(v___x_3406_);
                    if v___x_3407_ == 0 {
                        crate::leanh::lean_dec(v___x_3400_);
                        crate::leanh::lean_del_object(v___x_3394_);
                        crate::leanh::lean_dec(v_fst_3391_);
                        v_a_3402_ = v_b_3380_;
                        state = 2;
                        continue;
                    } else {
                        if v_isShared_3395_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3394_, 1, v___x_3400_);
                            v___x_3409_ = v___x_3394_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3411_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_fst_3391_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3411_, 1, v___x_3400_);
                            v___x_3409_ = v_reuseFailAlloc_3411_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3398_);
                    crate::leanh::lean_del_object(v___x_3394_);
                    crate::leanh::lean_dec(v_fst_3391_);
                    crate::leanh::lean_dec_ref(v_b_3380_);
                    v_a_3412_ = crate::leanh::lean_ctor_get(v___x_3399_, 0);
                    v_isSharedCheck_3419_ = (!crate::leanh::lean_is_exclusive(v___x_3399_)) as u8;
                    if v_isSharedCheck_3419_ == 0 {
                        v___x_3414_ = v___x_3399_;
                        v_isShared_3415_ = v_isSharedCheck_3419_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3412_);
                        crate::leanh::lean_dec(v___x_3399_);
                        v___x_3414_ = crate::leanh::lean_box(0);
                        v_isShared_3415_ = v_isSharedCheck_3419_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3403_ = 1usize;
                v___x_3404_ = lean_usize_add(v_i_3379_, v___x_3403_);
                v_i_3379_ = v___x_3404_;
                v_b_3380_ = v_a_3402_;
                state = 0;
                continue;
            }
            3 => {
                v___x_3410_ = lean_array_push(v_b_3380_, v___x_3409_);
                v_a_3402_ = v___x_3410_;
                state = 2;
                continue;
            }
            4 => {
                if v_isShared_3415_ == 0 {
                    v___x_3417_ = v___x_3414_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
                    v___x_3417_ = v_reuseFailAlloc_3418_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0___boxed(
    mut v_as_3421_: *mut crate::leanh::LeanObject,
    mut v_sz_3422_: *mut crate::leanh::LeanObject,
    mut v_i_3423_: *mut crate::leanh::LeanObject,
    mut v_b_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3432_: usize = 0;
    let mut v_i_boxed_3433_: usize = 0;
    let mut v_res_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3432_ = crate::leanh::lean_unbox_usize(v_sz_3422_);
    crate::leanh::lean_dec(v_sz_3422_);
    v_i_boxed_3433_ = crate::leanh::lean_unbox_usize(v_i_3423_);
    crate::leanh::lean_dec(v_i_3423_);
    v_res_3434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0(v_as_3421_, v_sz_boxed_3432_, v_i_boxed_3433_, v_b_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
    crate::leanh::lean_dec(v___y_3430_);
    crate::leanh::lean_dec_ref(v___y_3429_);
    crate::leanh::lean_dec(v___y_3428_);
    crate::leanh::lean_dec_ref(v___y_3427_);
    crate::leanh::lean_dec(v___y_3426_);
    crate::leanh::lean_dec_ref(v___y_3425_);
    crate::leanh::lean_dec_ref(v_as_3421_);
    return v_res_3434_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0(
    mut v_as_3435_: *mut crate::leanh::LeanObject,
    mut v_sz_3436_: usize,
    mut v_i_3437_: usize,
    mut v_b_3438_: *mut crate::leanh::LeanObject,
    mut v___y_3439_: *mut crate::leanh::LeanObject,
    mut v___y_3440_: *mut crate::leanh::LeanObject,
    mut v___y_3441_: *mut crate::leanh::LeanObject,
    mut v___y_3442_: *mut crate::leanh::LeanObject,
    mut v___y_3443_: *mut crate::leanh::LeanObject,
    mut v___y_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: usize = 0;
    let mut v___x_3462_: usize = 0;
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3446_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
                if v___x_3446_ == 0 {
                    v___x_3447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3447_, 0, v_b_3438_);
                    return v___x_3447_;
                } else {
                    v_a_3448_ = lean_array_uget(v_as_3435_, v_i_3437_);
                    v_fst_3449_ = crate::leanh::lean_ctor_get(v_a_3448_, 0);
                    v_snd_3450_ = crate::leanh::lean_ctor_get(v_a_3448_, 1);
                    v_isSharedCheck_3478_ = (!crate::leanh::lean_is_exclusive(v_a_3448_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3452_ = v_a_3448_;
                        v_isShared_3453_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3450_);
                        crate::leanh::lean_inc(v_fst_3449_);
                        crate::leanh::lean_dec(v_a_3448_);
                        v___x_3452_ = crate::leanh::lean_box(0);
                        v_isShared_3453_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3454_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3455_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1;
                v___x_3456_ = lean_st_mk_ref(v___x_3455_);
                crate::leanh::lean_inc(v_fst_3449_);
                v___x_3457_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_fst_3449_, v_snd_3450_, v___x_3456_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
                crate::leanh::lean_dec(v_snd_3450_);
                if crate::leanh::lean_obj_tag(v___x_3457_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3457_, 1);
                    v___x_3458_ = lean_st_ref_get(v___x_3456_);
                    crate::leanh::lean_dec(v___x_3456_);
                    v___x_3464_ =
                        l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(
                            v___x_3458_,
                        );
                    v___x_3465_ = lean_nat_dec_lt(v___x_3454_, v___x_3464_);
                    crate::leanh::lean_dec(v___x_3464_);
                    if v___x_3465_ == 0 {
                        crate::leanh::lean_dec(v___x_3458_);
                        crate::leanh::lean_del_object(v___x_3452_);
                        crate::leanh::lean_dec(v_fst_3449_);
                        v_a_3460_ = v_b_3438_;
                        state = 2;
                        continue;
                    } else {
                        if v_isShared_3453_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3452_, 1, v___x_3458_);
                            v___x_3467_ = v___x_3452_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3469_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_fst_3449_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3458_);
                            v___x_3467_ = v_reuseFailAlloc_3469_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3456_);
                    crate::leanh::lean_del_object(v___x_3452_);
                    crate::leanh::lean_dec(v_fst_3449_);
                    crate::leanh::lean_dec_ref(v_b_3438_);
                    v_a_3470_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
                    v_isSharedCheck_3477_ = (!crate::leanh::lean_is_exclusive(v___x_3457_)) as u8;
                    if v_isSharedCheck_3477_ == 0 {
                        v___x_3472_ = v___x_3457_;
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3470_);
                        crate::leanh::lean_dec(v___x_3457_);
                        v___x_3472_ = crate::leanh::lean_box(0);
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3461_ = 1usize;
                v___x_3462_ = lean_usize_add(v_i_3437_, v___x_3461_);
                v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0(v_as_3435_, v_sz_3436_, v___x_3462_, v_a_3460_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
                return v___x_3463_;
            }
            3 => {
                v___x_3468_ = lean_array_push(v_b_3438_, v___x_3467_);
                v_a_3460_ = v___x_3468_;
                state = 2;
                continue;
            }
            4 => {
                if v_isShared_3473_ == 0 {
                    v___x_3475_ = v___x_3472_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
                    v___x_3475_ = v_reuseFailAlloc_3476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0___boxed(
    mut v_as_3479_: *mut crate::leanh::LeanObject,
    mut v_sz_3480_: *mut crate::leanh::LeanObject,
    mut v_i_3481_: *mut crate::leanh::LeanObject,
    mut v_b_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v___y_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3490_: usize = 0;
    let mut v_i_boxed_3491_: usize = 0;
    let mut v_res_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3490_ = crate::leanh::lean_unbox_usize(v_sz_3480_);
    crate::leanh::lean_dec(v_sz_3480_);
    v_i_boxed_3491_ = crate::leanh::lean_unbox_usize(v_i_3481_);
    crate::leanh::lean_dec(v_i_3481_);
    v_res_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0(v_as_3479_, v_sz_boxed_3490_, v_i_boxed_3491_, v_b_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
    crate::leanh::lean_dec(v___y_3488_);
    crate::leanh::lean_dec_ref(v___y_3487_);
    crate::leanh::lean_dec(v___y_3486_);
    crate::leanh::lean_dec_ref(v___y_3485_);
    crate::leanh::lean_dec(v___y_3484_);
    crate::leanh::lean_dec_ref(v___y_3483_);
    crate::leanh::lean_dec_ref(v_as_3479_);
    return v_res_3492_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8(
    mut v_as_3493_: *mut crate::leanh::LeanObject,
    mut v_sz_3494_: usize,
    mut v_i_3495_: usize,
    mut v_b_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3507_: usize = 0;
    let mut v___x_3508_: usize = 0;
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: usize = 0;
    let mut v___x_3512_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3504_ = lean_usize_dec_lt(v_i_3495_, v_sz_3494_);
                if v___x_3504_ == 0 {
                    v___x_3505_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3505_, 0, v_b_3496_);
                    return v___x_3505_;
                } else {
                    v_a_3506_ = lean_array_uget_borrowed(v_as_3493_, v_i_3495_);
                    v_sz_3507_ = lean_array_size(v_a_3506_);
                    v___x_3508_ = 0usize;
                    v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0(v_a_3506_, v_sz_3507_, v___x_3508_, v_b_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
                    if crate::leanh::lean_obj_tag(v___x_3509_) == 0 {
                        v_a_3510_ = crate::leanh::lean_ctor_get(v___x_3509_, 0);
                        crate::leanh::lean_inc(v_a_3510_);
                        crate::leanh::lean_dec_ref_known(v___x_3509_, 1);
                        v___x_3511_ = 1usize;
                        v___x_3512_ = lean_usize_add(v_i_3495_, v___x_3511_);
                        v_i_3495_ = v___x_3512_;
                        v_b_3496_ = v_a_3510_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3509_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8___boxed(
    mut v_as_3514_: *mut crate::leanh::LeanObject,
    mut v_sz_3515_: *mut crate::leanh::LeanObject,
    mut v_i_3516_: *mut crate::leanh::LeanObject,
    mut v_b_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
    mut v___y_3520_: *mut crate::leanh::LeanObject,
    mut v___y_3521_: *mut crate::leanh::LeanObject,
    mut v___y_3522_: *mut crate::leanh::LeanObject,
    mut v___y_3523_: *mut crate::leanh::LeanObject,
    mut v___y_3524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3525_: usize = 0;
    let mut v_i_boxed_3526_: usize = 0;
    let mut v_res_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3525_ = crate::leanh::lean_unbox_usize(v_sz_3515_);
    crate::leanh::lean_dec(v_sz_3515_);
    v_i_boxed_3526_ = crate::leanh::lean_unbox_usize(v_i_3516_);
    crate::leanh::lean_dec(v_i_3516_);
    v_res_3527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8(v_as_3514_, v_sz_boxed_3525_, v_i_boxed_3526_, v_b_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
    crate::leanh::lean_dec(v___y_3523_);
    crate::leanh::lean_dec_ref(v___y_3522_);
    crate::leanh::lean_dec(v___y_3521_);
    crate::leanh::lean_dec_ref(v___y_3520_);
    crate::leanh::lean_dec(v___y_3519_);
    crate::leanh::lean_dec_ref(v___y_3518_);
    crate::leanh::lean_dec_ref(v_as_3514_);
    return v_res_3527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1(
    mut v_sz_3528_: usize,
    mut v_i_3529_: usize,
    mut v_bs_3530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3531_: u8 = 0;
    let mut v_v_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3531_ = lean_usize_dec_lt(v_i_3529_, v_sz_3528_);
                if v___x_3531_ == 0 {
                    return v_bs_3530_;
                } else {
                    v_v_3532_ = lean_array_uget(v_bs_3530_, v_i_3529_);
                    v___x_3533_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3534_ = lean_array_uset(v_bs_3530_, v_i_3529_, v___x_3533_);
                    v___x_3535_ = l_Lean_Exception_toMessageData(v_v_3532_);
                    v___x_3536_ = 1usize;
                    v___x_3537_ = lean_usize_add(v_i_3529_, v___x_3536_);
                    v___x_3538_ = lean_array_uset(v_bs_x27_3534_, v_i_3529_, v___x_3535_);
                    v_i_3529_ = v___x_3537_;
                    v_bs_3530_ = v___x_3538_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1___boxed(
    mut v_sz_3540_: *mut crate::leanh::LeanObject,
    mut v_i_3541_: *mut crate::leanh::LeanObject,
    mut v_bs_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3543_: usize = 0;
    let mut v_i_boxed_3544_: usize = 0;
    let mut v_res_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3543_ = crate::leanh::lean_unbox_usize(v_sz_3540_);
    crate::leanh::lean_dec(v_sz_3540_);
    v_i_boxed_3544_ = crate::leanh::lean_unbox_usize(v_i_3541_);
    crate::leanh::lean_dec(v_i_3541_);
    v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1(v_sz_boxed_3543_, v_i_boxed_3544_, v_bs_3542_);
    return v_res_3545_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0()
-> f64 {
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: f64 = 0.0;
    v___x_3546_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3547_ = lean_float_of_nat(v___x_3546_);
    return v___x_3547_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4;
    v___x_3554_ = l_Lean_stringToMessageData(v___x_3553_);
    return v___x_3554_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6;
    v___x_3557_ = l_Lean_stringToMessageData(v___x_3556_);
    return v___x_3557_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8;
    v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
    return v___x_3560_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10;
    v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
    return v___x_3563_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2(
    mut v_sz_3564_: usize,
    mut v_i_3565_: usize,
    mut v_bs_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3567_: u8 = 0;
    let mut v_v_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: f64 = 0.0;
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passed_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failed_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3567_ = lean_usize_dec_lt(v_i_3565_, v_sz_3564_);
                if v___x_3567_ == 0 {
                    return v_bs_3566_;
                } else {
                    v_v_3568_ = lean_array_uget(v_bs_3566_, v_i_3565_);
                    v_fst_3569_ = crate::leanh::lean_ctor_get(v_v_3568_, 0);
                    v_snd_3570_ = crate::leanh::lean_ctor_get(v_v_3568_, 1);
                    v_isSharedCheck_3618_ = (!crate::leanh::lean_is_exclusive(v_v_3568_)) as u8;
                    if v_isSharedCheck_3618_ == 0 {
                        v___x_3572_ = v_v_3568_;
                        v_isShared_3573_ = v_isSharedCheck_3618_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3570_);
                        crate::leanh::lean_inc(v_fst_3569_);
                        crate::leanh::lean_dec(v_v_3568_);
                        v___x_3572_ = crate::leanh::lean_box(0);
                        v_isShared_3573_ = v_isSharedCheck_3618_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3574_ = crate::leanh::lean_box(0);
                v___x_3575_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3576_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0);
                v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1;
                v___x_3578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3;
                v___x_3579_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                crate::leanh::lean_ctor_set(v___x_3579_, 1, v___x_3574_);
                crate::leanh::lean_ctor_set(v___x_3579_, 2, v___x_3577_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3579_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3576_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3579_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3576_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3579_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3567_,
                );
                v_passed_3580_ = crate::leanh::lean_ctor_get(v_snd_3570_, 0);
                v_failed_3581_ = crate::leanh::lean_ctor_get(v_snd_3570_, 1);
                v_isSharedCheck_3617_ = (!crate::leanh::lean_is_exclusive(v_snd_3570_)) as u8;
                if v_isSharedCheck_3617_ == 0 {
                    v___x_3583_ = v_snd_3570_;
                    v_isShared_3584_ = v_isSharedCheck_3617_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_failed_3581_);
                    crate::leanh::lean_inc(v_passed_3580_);
                    crate::leanh::lean_dec(v_snd_3570_);
                    v___x_3583_ = crate::leanh::lean_box(0);
                    v_isShared_3584_ = v_isSharedCheck_3617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5);
                v___x_3586_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7);
                v_bs_x27_3587_ = lean_array_uset(v_bs_3566_, v_i_3565_, v___x_3575_);
                v___x_3588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9);
                v___x_3589_ = 0;
                v___x_3590_ = l_Lean_MessageData_ofConstName(v_fst_3569_, v___x_3589_);
                if v_isShared_3584_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3583_, 7);
                    crate::leanh::lean_ctor_set(v___x_3583_, 1, v___x_3590_);
                    crate::leanh::lean_ctor_set(v___x_3583_, 0, v___x_3588_);
                    v___x_3592_ = v___x_3583_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3616_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3616_, 1, v___x_3590_);
                    v___x_3592_ = v_reuseFailAlloc_3616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3593_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11);
                if v_isShared_3573_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3572_, 7);
                    crate::leanh::lean_ctor_set(v___x_3572_, 1, v___x_3593_);
                    crate::leanh::lean_ctor_set(v___x_3572_, 0, v___x_3592_);
                    v___x_3595_ = v___x_3572_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3615_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3615_, 1, v___x_3593_);
                    v___x_3595_ = v_reuseFailAlloc_3615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3596_ = l_Nat_reprFast(v_passed_3580_);
                v___x_3597_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3597_, 0, v___x_3596_);
                v___x_3598_ = l_Lean_MessageData_ofFormat(v___x_3597_);
                v___x_3599_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3599_, 0, v___x_3595_);
                crate::leanh::lean_ctor_set(v___x_3599_, 1, v___x_3598_);
                v___x_3600_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3600_, 0, v___x_3599_);
                crate::leanh::lean_ctor_set(v___x_3600_, 1, v___x_3585_);
                v___x_3601_ = lean_array_get_size(v_failed_3581_);
                v___x_3602_ = l_Nat_reprFast(v___x_3601_);
                v___x_3603_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3603_, 0, v___x_3602_);
                v___x_3604_ = l_Lean_MessageData_ofFormat(v___x_3603_);
                v___x_3605_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3605_, 0, v___x_3600_);
                crate::leanh::lean_ctor_set(v___x_3605_, 1, v___x_3604_);
                v___x_3606_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3606_, 0, v___x_3605_);
                crate::leanh::lean_ctor_set(v___x_3606_, 1, v___x_3586_);
                v_sz_3607_ = lean_array_size(v_failed_3581_);
                v___x_3608_ = 0usize;
                v___x_3609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1(v_sz_3607_, v___x_3608_, v_failed_3581_);
                v___x_3610_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3579_);
                crate::leanh::lean_ctor_set(v___x_3610_, 1, v___x_3606_);
                crate::leanh::lean_ctor_set(v___x_3610_, 2, v___x_3609_);
                v___x_3611_ = 1usize;
                v___x_3612_ = lean_usize_add(v_i_3565_, v___x_3611_);
                v___x_3613_ = lean_array_uset(v_bs_x27_3587_, v_i_3565_, v___x_3610_);
                v_i_3565_ = v___x_3612_;
                v_bs_3566_ = v___x_3613_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___boxed(
    mut v_sz_3619_: *mut crate::leanh::LeanObject,
    mut v_i_3620_: *mut crate::leanh::LeanObject,
    mut v_bs_3621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3622_: usize = 0;
    let mut v_i_boxed_3623_: usize = 0;
    let mut v_res_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3622_ = crate::leanh::lean_unbox_usize(v_sz_3619_);
    crate::leanh::lean_dec(v_sz_3619_);
    v_i_boxed_3623_ = crate::leanh::lean_unbox_usize(v_i_3620_);
    crate::leanh::lean_dec(v_i_3620_);
    v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2(v_sz_boxed_3622_, v_i_boxed_3623_, v_bs_3621_);
    return v_res_3624_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6(
    mut v_sz_3625_: usize,
    mut v_i_3626_: usize,
    mut v_bs_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3628_: u8 = 0;
    let mut v_v_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_passed_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: usize = 0;
    let mut v___x_3635_: usize = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3628_ = lean_usize_dec_lt(v_i_3626_, v_sz_3625_);
                if v___x_3628_ == 0 {
                    return v_bs_3627_;
                } else {
                    v_v_3629_ = lean_array_uget_borrowed(v_bs_3627_, v_i_3626_);
                    v_snd_3630_ = crate::leanh::lean_ctor_get(v_v_3629_, 1);
                    v_passed_3631_ = crate::leanh::lean_ctor_get(v_snd_3630_, 0);
                    crate::leanh::lean_inc(v_passed_3631_);
                    v___x_3632_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3633_ = lean_array_uset(v_bs_3627_, v_i_3626_, v___x_3632_);
                    v___x_3634_ = 1usize;
                    v___x_3635_ = lean_usize_add(v_i_3626_, v___x_3634_);
                    v___x_3636_ = lean_array_uset(v_bs_x27_3633_, v_i_3626_, v_passed_3631_);
                    v_i_3626_ = v___x_3635_;
                    v_bs_3627_ = v___x_3636_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6___boxed(
    mut v_sz_3638_: *mut crate::leanh::LeanObject,
    mut v_i_3639_: *mut crate::leanh::LeanObject,
    mut v_bs_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3641_: usize = 0;
    let mut v_i_boxed_3642_: usize = 0;
    let mut v_res_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3641_ = crate::leanh::lean_unbox_usize(v_sz_3638_);
    crate::leanh::lean_dec(v_sz_3638_);
    v_i_boxed_3642_ = crate::leanh::lean_unbox_usize(v_i_3639_);
    crate::leanh::lean_dec(v_i_3639_);
    v_res_3643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6(v_sz_boxed_3641_, v_i_boxed_3642_, v_bs_3640_);
    return v_res_3643_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(
    mut v_as_3644_: *mut crate::leanh::LeanObject,
    mut v_i_3645_: usize,
    mut v_stop_3646_: usize,
    mut v_b_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: usize = 0;
    let mut v___x_3650_: usize = 0;
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3648_ = lean_usize_dec_eq(v_i_3645_, v_stop_3646_);
                if v___x_3648_ == 0 {
                    v___x_3649_ = 1usize;
                    v___x_3650_ = lean_usize_sub(v_i_3645_, v___x_3649_);
                    v___x_3651_ = lean_array_uget_borrowed(v_as_3644_, v___x_3650_);
                    v___x_3652_ = lean_nat_add(v___x_3651_, v_b_3647_);
                    crate::leanh::lean_dec(v_b_3647_);
                    v_i_3645_ = v___x_3650_;
                    v_b_3647_ = v___x_3652_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3647_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5___boxed(
    mut v_as_3654_: *mut crate::leanh::LeanObject,
    mut v_i_3655_: *mut crate::leanh::LeanObject,
    mut v_stop_3656_: *mut crate::leanh::LeanObject,
    mut v_b_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3658_: usize = 0;
    let mut v_stop_boxed_3659_: usize = 0;
    let mut v_res_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3658_ = crate::leanh::lean_unbox_usize(v_i_3655_);
    crate::leanh::lean_dec(v_i_3655_);
    v_stop_boxed_3659_ = crate::leanh::lean_unbox_usize(v_stop_3656_);
    crate::leanh::lean_dec(v_stop_3656_);
    v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(v_as_3654_, v_i_boxed_3658_, v_stop_boxed_3659_, v_b_3657_);
    crate::leanh::lean_dec_ref(v_as_3654_);
    return v_res_3660_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4(
    mut v_sz_3661_: usize,
    mut v_i_3662_: usize,
    mut v_bs_3663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3664_: u8 = 0;
    let mut v_v_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failed_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: usize = 0;
    let mut v___x_3672_: usize = 0;
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3664_ = lean_usize_dec_lt(v_i_3662_, v_sz_3661_);
                if v___x_3664_ == 0 {
                    return v_bs_3663_;
                } else {
                    v_v_3665_ = lean_array_uget_borrowed(v_bs_3663_, v_i_3662_);
                    v_snd_3666_ = crate::leanh::lean_ctor_get(v_v_3665_, 1);
                    v_failed_3667_ = crate::leanh::lean_ctor_get(v_snd_3666_, 1);
                    crate::leanh::lean_inc_ref(v_failed_3667_);
                    v___x_3668_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3669_ = lean_array_uset(v_bs_3663_, v_i_3662_, v___x_3668_);
                    v___x_3670_ = lean_array_get_size(v_failed_3667_);
                    crate::leanh::lean_dec_ref(v_failed_3667_);
                    v___x_3671_ = 1usize;
                    v___x_3672_ = lean_usize_add(v_i_3662_, v___x_3671_);
                    v___x_3673_ = lean_array_uset(v_bs_x27_3669_, v_i_3662_, v___x_3670_);
                    v_i_3662_ = v___x_3672_;
                    v_bs_3663_ = v___x_3673_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4___boxed(
    mut v_sz_3675_: *mut crate::leanh::LeanObject,
    mut v_i_3676_: *mut crate::leanh::LeanObject,
    mut v_bs_3677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3678_: usize = 0;
    let mut v_i_boxed_3679_: usize = 0;
    let mut v_res_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3678_ = crate::leanh::lean_unbox_usize(v_sz_3675_);
    crate::leanh::lean_dec(v_sz_3675_);
    v_i_boxed_3679_ = crate::leanh::lean_unbox_usize(v_i_3676_);
    crate::leanh::lean_dec(v_i_3676_);
    v_res_3680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4(v_sz_boxed_3678_, v_i_boxed_3679_, v_bs_3677_);
    return v_res_3680_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0(
    mut v___y_3689_: u8,
    mut v_suppressElabErrors_3690_: u8,
    mut v_x_3691_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3691_) == 1 {
        let mut v_pre_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_3692_ = crate::leanh::lean_ctor_get(v_x_3691_, 0);
        match crate::leanh::lean_obj_tag(v_pre_3692_) {
            1 => {
                let mut v_pre_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_3693_ = crate::leanh::lean_ctor_get(v_pre_3692_, 0);
                match crate::leanh::lean_obj_tag(v_pre_3693_) {
                    0 => {
                        let mut v_str_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3697_: u8 = 0;
                        v_str_3694_ = crate::leanh::lean_ctor_get(v_x_3691_, 1);
                        v_str_3695_ = crate::leanh::lean_ctor_get(v_pre_3692_, 1);
                        v___x_3696_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0;
                        v___x_3697_ = lean_string_dec_eq(v_str_3695_, v___x_3696_);
                        if v___x_3697_ == 0 {
                            let mut v___x_3698_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3699_: u8 = 0;
                            v___x_3698_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1;
                            v___x_3699_ = lean_string_dec_eq(v_str_3695_, v___x_3698_);
                            if v___x_3699_ == 0 {
                                return v___y_3689_;
                            } else {
                                let mut v___x_3700_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3701_: u8 = 0;
                                v___x_3700_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2;
                                v___x_3701_ = lean_string_dec_eq(v_str_3694_, v___x_3700_);
                                if v___x_3701_ == 0 {
                                    return v___y_3689_;
                                } else {
                                    return v_suppressElabErrors_3690_;
                                }
                            }
                        } else {
                            let mut v___x_3702_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3703_: u8 = 0;
                            v___x_3702_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3;
                            v___x_3703_ = lean_string_dec_eq(v_str_3694_, v___x_3702_);
                            if v___x_3703_ == 0 {
                                return v___y_3689_;
                            } else {
                                return v_suppressElabErrors_3690_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_3704_ = crate::leanh::lean_ctor_get(v_pre_3693_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3704_) == 0 {
                            let mut v_str_3705_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3706_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3707_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3708_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3709_: u8 = 0;
                            v_str_3705_ = crate::leanh::lean_ctor_get(v_x_3691_, 1);
                            v_str_3706_ = crate::leanh::lean_ctor_get(v_pre_3692_, 1);
                            v_str_3707_ = crate::leanh::lean_ctor_get(v_pre_3693_, 1);
                            v___x_3708_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4;
                            v___x_3709_ = lean_string_dec_eq(v_str_3707_, v___x_3708_);
                            if v___x_3709_ == 0 {
                                return v___y_3689_;
                            } else {
                                let mut v___x_3710_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3711_: u8 = 0;
                                v___x_3710_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5;
                                v___x_3711_ = lean_string_dec_eq(v_str_3706_, v___x_3710_);
                                if v___x_3711_ == 0 {
                                    return v___y_3689_;
                                } else {
                                    let mut v___x_3712_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3713_: u8 = 0;
                                    v___x_3712_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6;
                                    v___x_3713_ = lean_string_dec_eq(v_str_3705_, v___x_3712_);
                                    if v___x_3713_ == 0 {
                                        return v___y_3689_;
                                    } else {
                                        return v_suppressElabErrors_3690_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3689_;
                        }
                    }
                    _ => {
                        return v___y_3689_;
                    }
                }
            }
            0 => {
                let mut v_str_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3716_: u8 = 0;
                v_str_3714_ = crate::leanh::lean_ctor_get(v_x_3691_, 1);
                v___x_3715_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7;
                v___x_3716_ = lean_string_dec_eq(v_str_3714_, v___x_3715_);
                if v___x_3716_ == 0 {
                    return v___y_3689_;
                } else {
                    return v_suppressElabErrors_3690_;
                }
            }
            _ => {
                return v___y_3689_;
            }
        }
    } else {
        return v___y_3689_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___boxed(
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_3718_: *mut crate::leanh::LeanObject,
    mut v_x_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_12662__boxed_3720_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3721_: u8 = 0;
    let mut v_res_3722_: u8 = 0;
    let mut v_r_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_12662__boxed_3720_ = (crate::leanh::lean_unbox(v___y_3717_) as u8);
    v_suppressElabErrors_boxed_3721_ = (crate::leanh::lean_unbox(v_suppressElabErrors_3718_) as u8);
    v_res_3722_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0(v___y_12662__boxed_3720_, v_suppressElabErrors_boxed_3721_, v_x_3719_);
    crate::leanh::lean_dec(v_x_3719_);
    v_r_3723_ = crate::leanh::lean_box((v_res_3722_) as usize);
    return v_r_3723_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(
    mut v_ref_3724_: *mut crate::leanh::LeanObject,
    mut v_msgData_3725_: *mut crate::leanh::LeanObject,
    mut v_severity_3726_: u8,
    mut v_isSilent_3727_: u8,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3735_: u8 = 0;
    let mut v___y_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: u8 = 0;
    let mut v___y_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3768_: u8 = 0;
    let mut v___y_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3771_: u8 = 0;
    let mut v___y_3772_: u8 = 0;
    let mut v___y_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: u8 = 0;
    let mut v___y_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v___y_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3797_: u8 = 0;
    let mut v___y_3798_: u8 = 0;
    let mut v___y_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3801_: u8 = 0;
    let mut v___y_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3807_: u8 = 0;
    let mut v___y_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3809_: u8 = 0;
    let mut v___y_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: u8 = 0;
    let mut v_ref_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: u8 = 0;
    let mut v___y_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3821_: u8 = 0;
    let mut v___y_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: u8 = 0;
    let mut v___y_3825_: u8 = 0;
    let mut v___y_3827_: u8 = 0;
    let mut v_fileName_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3832_: u8 = 0;
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: u8 = 0;
    let mut v___x_3837_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u8 = 0;
    let mut v___x_3843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3817_ = 2;
                v___x_3842_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3726_, v___x_3817_);
                if v___x_3842_ == 0 {
                    v___y_3827_ = v___x_3842_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_3725_);
                    v___x_3843_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3725_);
                    v___y_3827_ = v___x_3843_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3743_ = lean_st_ref_take(v___y_3742_);
                v_currNamespace_3744_ = crate::leanh::lean_ctor_get(v___y_3741_, 6);
                v_openDecls_3745_ = crate::leanh::lean_ctor_get(v___y_3741_, 7);
                v_env_3746_ = crate::leanh::lean_ctor_get(v___x_3743_, 0);
                v_nextMacroScope_3747_ = crate::leanh::lean_ctor_get(v___x_3743_, 1);
                v_ngen_3748_ = crate::leanh::lean_ctor_get(v___x_3743_, 2);
                v_auxDeclNGen_3749_ = crate::leanh::lean_ctor_get(v___x_3743_, 3);
                v_traceState_3750_ = crate::leanh::lean_ctor_get(v___x_3743_, 4);
                v_cache_3751_ = crate::leanh::lean_ctor_get(v___x_3743_, 5);
                v_messages_3752_ = crate::leanh::lean_ctor_get(v___x_3743_, 6);
                v_infoState_3753_ = crate::leanh::lean_ctor_get(v___x_3743_, 7);
                v_snapshotTasks_3754_ = crate::leanh::lean_ctor_get(v___x_3743_, 8);
                v_isSharedCheck_3768_ = (!crate::leanh::lean_is_exclusive(v___x_3743_)) as u8;
                if v_isSharedCheck_3768_ == 0 {
                    v___x_3756_ = v___x_3743_;
                    v_isShared_3757_ = v_isSharedCheck_3768_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3754_);
                    crate::leanh::lean_inc(v_infoState_3753_);
                    crate::leanh::lean_inc(v_messages_3752_);
                    crate::leanh::lean_inc(v_cache_3751_);
                    crate::leanh::lean_inc(v_traceState_3750_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3749_);
                    crate::leanh::lean_inc(v_ngen_3748_);
                    crate::leanh::lean_inc(v_nextMacroScope_3747_);
                    crate::leanh::lean_inc(v_env_3746_);
                    crate::leanh::lean_dec(v___x_3743_);
                    v___x_3756_ = crate::leanh::lean_box(0);
                    v_isShared_3757_ = v_isSharedCheck_3768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_3745_);
                crate::leanh::lean_inc(v_currNamespace_3744_);
                v___x_3758_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3758_, 0, v_currNamespace_3744_);
                crate::leanh::lean_ctor_set(v___x_3758_, 1, v_openDecls_3745_);
                v___x_3759_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3759_, 0, v___x_3758_);
                crate::leanh::lean_ctor_set(v___x_3759_, 1, v___y_3739_);
                crate::leanh::lean_inc_ref(v___y_3734_);
                crate::leanh::lean_inc_ref(v___y_3736_);
                v___x_3760_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_3760_, 0, v___y_3736_);
                crate::leanh::lean_ctor_set(v___x_3760_, 1, v___y_3738_);
                crate::leanh::lean_ctor_set(v___x_3760_, 2, v___y_3737_);
                crate::leanh::lean_ctor_set(v___x_3760_, 3, v___y_3734_);
                crate::leanh::lean_ctor_set(v___x_3760_, 4, v___x_3759_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3735_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_3740_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3727_,
                );
                v___x_3761_ = l_Lean_MessageLog_add(v___x_3760_, v_messages_3752_);
                if v_isShared_3757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3756_, 6, v___x_3761_);
                    v___x_3763_ = v___x_3756_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3767_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_env_3746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_nextMacroScope_3747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 2, v_ngen_3748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 3, v_auxDeclNGen_3749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 4, v_traceState_3750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 5, v_cache_3751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 6, v___x_3761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 7, v_infoState_3753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 8, v_snapshotTasks_3754_);
                    v___x_3763_ = v_reuseFailAlloc_3767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3764_ = lean_st_ref_set(v___y_3742_, v___x_3763_);
                v___x_3765_ = crate::leanh::lean_box(0);
                v___x_3766_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3766_, 0, v___x_3765_);
                return v___x_3766_;
            }
            4 => {
                v___x_3778_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3725_,
                    );
                v___x_3779_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v___x_3778_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
                v_a_3780_ = crate::leanh::lean_ctor_get(v___x_3779_, 0);
                v_isSharedCheck_3793_ = (!crate::leanh::lean_is_exclusive(v___x_3779_)) as u8;
                if v_isSharedCheck_3793_ == 0 {
                    v___x_3782_ = v___x_3779_;
                    v_isShared_3783_ = v_isSharedCheck_3793_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3780_);
                    crate::leanh::lean_dec(v___x_3779_);
                    v___x_3782_ = crate::leanh::lean_box(0);
                    v_isShared_3783_ = v_isSharedCheck_3793_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_3774_, 2);
                v___x_3784_ = l_Lean_FileMap_toPosition(v___y_3774_, v___y_3775_);
                crate::leanh::lean_dec(v___y_3775_);
                v___x_3785_ = l_Lean_FileMap_toPosition(v___y_3774_, v___y_3777_);
                crate::leanh::lean_dec(v___y_3777_);
                v___x_3786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3786_, 0, v___x_3785_);
                v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1;
                if v___y_3772_ == 0 {
                    crate::leanh::lean_del_object(v___x_3782_);
                    crate::leanh::lean_dec_ref(v___y_3770_);
                    v___y_3734_ = v___x_3787_;
                    v___y_3735_ = v___y_3771_;
                    v___y_3736_ = v___y_3773_;
                    v___y_3737_ = v___x_3786_;
                    v___y_3738_ = v___x_3784_;
                    v___y_3739_ = v_a_3780_;
                    v___y_3740_ = v___y_3776_;
                    v___y_3741_ = v___y_3730_;
                    v___y_3742_ = v___y_3731_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3780_);
                    v___x_3788_ = l_Lean_MessageData_hasTag(v___y_3770_, v_a_3780_);
                    if v___x_3788_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3786_, 1);
                        crate::leanh::lean_dec_ref(v___x_3784_);
                        crate::leanh::lean_dec(v_a_3780_);
                        v___x_3789_ = crate::leanh::lean_box(0);
                        if v_isShared_3783_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3782_, 0, v___x_3789_);
                            v___x_3791_ = v___x_3782_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3792_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
                            v___x_3791_ = v_reuseFailAlloc_3792_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3782_);
                        v___y_3734_ = v___x_3787_;
                        v___y_3735_ = v___y_3771_;
                        v___y_3736_ = v___y_3773_;
                        v___y_3737_ = v___x_3786_;
                        v___y_3738_ = v___x_3784_;
                        v___y_3739_ = v_a_3780_;
                        v___y_3740_ = v___y_3776_;
                        v___y_3741_ = v___y_3730_;
                        v___y_3742_ = v___y_3731_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3791_;
            }
            7 => {
                v___x_3803_ = l_Lean_Syntax_getTailPos_x3f(v___y_3796_, v___y_3797_);
                crate::leanh::lean_dec(v___y_3796_);
                if crate::leanh::lean_obj_tag(v___x_3803_) == 0 {
                    crate::leanh::lean_inc(v___y_3802_);
                    v___y_3770_ = v___y_3795_;
                    v___y_3771_ = v___y_3797_;
                    v___y_3772_ = v___y_3798_;
                    v___y_3773_ = v___y_3799_;
                    v___y_3774_ = v___y_3800_;
                    v___y_3775_ = v___y_3802_;
                    v___y_3776_ = v___y_3801_;
                    v___y_3777_ = v___y_3802_;
                    state = 4;
                    continue;
                } else {
                    v_val_3804_ = crate::leanh::lean_ctor_get(v___x_3803_, 0);
                    crate::leanh::lean_inc(v_val_3804_);
                    crate::leanh::lean_dec_ref_known(v___x_3803_, 1);
                    v___y_3770_ = v___y_3795_;
                    v___y_3771_ = v___y_3797_;
                    v___y_3772_ = v___y_3798_;
                    v___y_3773_ = v___y_3799_;
                    v___y_3774_ = v___y_3800_;
                    v___y_3775_ = v___y_3802_;
                    v___y_3776_ = v___y_3801_;
                    v___y_3777_ = v_val_3804_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3813_ = l_Lean_replaceRef(v_ref_3724_, v___y_3808_);
                v___x_3814_ = l_Lean_Syntax_getPos_x3f(v_ref_3813_, v___y_3807_);
                if crate::leanh::lean_obj_tag(v___x_3814_) == 0 {
                    v___x_3815_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3795_ = v___y_3806_;
                    v___y_3796_ = v_ref_3813_;
                    v___y_3797_ = v___y_3807_;
                    v___y_3798_ = v___y_3809_;
                    v___y_3799_ = v___y_3810_;
                    v___y_3800_ = v___y_3811_;
                    v___y_3801_ = v___y_3812_;
                    v___y_3802_ = v___x_3815_;
                    state = 7;
                    continue;
                } else {
                    v_val_3816_ = crate::leanh::lean_ctor_get(v___x_3814_, 0);
                    crate::leanh::lean_inc(v_val_3816_);
                    crate::leanh::lean_dec_ref_known(v___x_3814_, 1);
                    v___y_3795_ = v___y_3806_;
                    v___y_3796_ = v_ref_3813_;
                    v___y_3797_ = v___y_3807_;
                    v___y_3798_ = v___y_3809_;
                    v___y_3799_ = v___y_3810_;
                    v___y_3800_ = v___y_3811_;
                    v___y_3801_ = v___y_3812_;
                    v___y_3802_ = v_val_3816_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3825_ == 0 {
                    v___y_3806_ = v___y_3820_;
                    v___y_3807_ = v___y_3824_;
                    v___y_3808_ = v___y_3819_;
                    v___y_3809_ = v___y_3821_;
                    v___y_3810_ = v___y_3822_;
                    v___y_3811_ = v___y_3823_;
                    v___y_3812_ = v_severity_3726_;
                    state = 8;
                    continue;
                } else {
                    v___y_3806_ = v___y_3820_;
                    v___y_3807_ = v___y_3824_;
                    v___y_3808_ = v___y_3819_;
                    v___y_3809_ = v___y_3821_;
                    v___y_3810_ = v___y_3822_;
                    v___y_3811_ = v___y_3823_;
                    v___y_3812_ = v___x_3817_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3827_ == 0 {
                    v_fileName_3828_ = crate::leanh::lean_ctor_get(v___y_3730_, 0);
                    v_fileMap_3829_ = crate::leanh::lean_ctor_get(v___y_3730_, 1);
                    v_options_3830_ = crate::leanh::lean_ctor_get(v___y_3730_, 2);
                    v_ref_3831_ = crate::leanh::lean_ctor_get(v___y_3730_, 5);
                    v_suppressElabErrors_3832_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3730_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3833_ = crate::leanh::lean_box((v___y_3827_) as usize);
                    v___x_3834_ = crate::leanh::lean_box((v_suppressElabErrors_3832_) as usize);
                    v___f_3835_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_3835_, 0, v___x_3833_);
                    crate::leanh::lean_closure_set(v___f_3835_, 1, v___x_3834_);
                    v___x_3836_ = 1;
                    v___x_3837_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3726_, v___x_3836_);
                    if v___x_3837_ == 0 {
                        v___y_3819_ = v_ref_3831_;
                        v___y_3820_ = v___f_3835_;
                        v___y_3821_ = v_suppressElabErrors_3832_;
                        v___y_3822_ = v_fileName_3828_;
                        v___y_3823_ = v_fileMap_3829_;
                        v___y_3824_ = v___y_3827_;
                        v___y_3825_ = v___x_3837_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3838_ = l_Lean_warningAsError;
                        v___x_3839_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(v_options_3830_, v___x_3838_);
                        v___y_3819_ = v_ref_3831_;
                        v___y_3820_ = v___f_3835_;
                        v___y_3821_ = v_suppressElabErrors_3832_;
                        v___y_3822_ = v_fileName_3828_;
                        v___y_3823_ = v_fileMap_3829_;
                        v___y_3824_ = v___y_3827_;
                        v___y_3825_ = v___x_3839_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_3725_);
                    v___x_3840_ = crate::leanh::lean_box(0);
                    v___x_3841_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3841_, 0, v___x_3840_);
                    return v___x_3841_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_ref_3844_: *mut crate::leanh::LeanObject,
    mut v_msgData_3845_: *mut crate::leanh::LeanObject,
    mut v_severity_3846_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3847_: *mut crate::leanh::LeanObject,
    mut v___y_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
    mut v___y_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3853_: u8 = 0;
    let mut v_isSilent_boxed_3854_: u8 = 0;
    let mut v_res_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3853_ = (crate::leanh::lean_unbox(v_severity_3846_) as u8);
    v_isSilent_boxed_3854_ = (crate::leanh::lean_unbox(v_isSilent_3847_) as u8);
    v_res_3855_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(v_ref_3844_, v_msgData_3845_, v_severity_boxed_3853_, v_isSilent_boxed_3854_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
    crate::leanh::lean_dec(v___y_3851_);
    crate::leanh::lean_dec_ref(v___y_3850_);
    crate::leanh::lean_dec(v___y_3849_);
    crate::leanh::lean_dec_ref(v___y_3848_);
    crate::leanh::lean_dec(v_ref_3844_);
    return v_res_3855_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4(
    mut v_msgData_3856_: *mut crate::leanh::LeanObject,
    mut v_severity_3857_: u8,
    mut v_isSilent_3858_: u8,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
    mut v___y_3863_: *mut crate::leanh::LeanObject,
    mut v___y_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3866_ = crate::leanh::lean_ctor_get(v___y_3863_, 5);
    v___x_3867_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(v_ref_3866_, v_msgData_3856_, v_severity_3857_, v_isSilent_3858_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4___boxed(
    mut v_msgData_3868_: *mut crate::leanh::LeanObject,
    mut v_severity_3869_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3878_: u8 = 0;
    let mut v_isSilent_boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3878_ = (crate::leanh::lean_unbox(v_severity_3869_) as u8);
    v_isSilent_boxed_3879_ = (crate::leanh::lean_unbox(v_isSilent_3870_) as u8);
    v_res_3880_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4(
        v_msgData_3868_,
        v_severity_boxed_3878_,
        v_isSilent_boxed_3879_,
        v___y_3871_,
        v___y_3872_,
        v___y_3873_,
        v___y_3874_,
        v___y_3875_,
        v___y_3876_,
    );
    crate::leanh::lean_dec(v___y_3876_);
    crate::leanh::lean_dec_ref(v___y_3875_);
    crate::leanh::lean_dec(v___y_3874_);
    crate::leanh::lean_dec_ref(v___y_3873_);
    crate::leanh::lean_dec(v___y_3872_);
    crate::leanh::lean_dec_ref(v___y_3871_);
    return v_res_3880_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3(
    mut v_msgData_3881_: *mut crate::leanh::LeanObject,
    mut v___y_3882_: *mut crate::leanh::LeanObject,
    mut v___y_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3889_: u8 = 0;
    let mut v___x_3890_: u8 = 0;
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3889_ = 0;
    v___x_3890_ = 0;
    v___x_3891_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4(
        v_msgData_3881_,
        v___x_3889_,
        v___x_3890_,
        v___y_3882_,
        v___y_3883_,
        v___y_3884_,
        v___y_3885_,
        v___y_3886_,
        v___y_3887_,
    );
    return v___x_3891_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3___boxed(
    mut v_msgData_3892_: *mut crate::leanh::LeanObject,
    mut v___y_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
    mut v___y_3896_: *mut crate::leanh::LeanObject,
    mut v___y_3897_: *mut crate::leanh::LeanObject,
    mut v___y_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3900_ = l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3(
        v_msgData_3892_,
        v___y_3893_,
        v___y_3894_,
        v___y_3895_,
        v___y_3896_,
        v___y_3897_,
        v___y_3898_,
    );
    crate::leanh::lean_dec(v___y_3898_);
    crate::leanh::lean_dec_ref(v___y_3897_);
    crate::leanh::lean_dec(v___y_3896_);
    crate::leanh::lean_dec_ref(v___y_3895_);
    crate::leanh::lean_dec(v___y_3894_);
    crate::leanh::lean_dec_ref(v___y_3893_);
    return v_res_3900_;
}
pub unsafe fn _init_l_Lean_Doc_checkPostponed___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3906_: f64 = 0.0;
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1;
    v___x_3905_ = 1;
    v___x_3906_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0);
    v___x_3907_ = crate::leanh::lean_box(0);
    v___x_3908_ = l_Lean_Doc_checkPostponed___closed__1;
    v___x_3909_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_3909_, 0, v___x_3908_);
    crate::leanh::lean_ctor_set(v___x_3909_, 1, v___x_3907_);
    crate::leanh::lean_ctor_set(v___x_3909_, 2, v___x_3904_);
    crate::leanh::lean_ctor_set_float(
        v___x_3909_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_3906_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_3909_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_3906_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3909_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_3905_,
    );
    return v___x_3909_;
}
pub unsafe fn _init_l_Lean_Doc_checkPostponed___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3911_ = l_Lean_Doc_checkPostponed___closed__3;
    v___x_3912_ = l_Lean_stringToMessageData(v___x_3911_);
    return v___x_3912_;
}
pub unsafe fn _init_l_Lean_Doc_checkPostponed___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Lean_Doc_checkPostponed___closed__5;
    v___x_3915_ = l_Lean_stringToMessageData(v___x_3914_);
    return v___x_3915_;
}
pub unsafe fn _init_l_Lean_Doc_checkPostponed___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3918_ = crate::leanh::lean_box(1);
    v___x_3919_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3918_);
    return v___x_3919_;
}
pub unsafe fn l_Lean_Doc_checkPostponed(
    mut v_a_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
    mut v_a_3922_: *mut crate::leanh::LeanObject,
    mut v_a_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_a_3925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3938_: usize = 0;
    let mut v___x_3939_: usize = 0;
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3955_: usize = 0;
    let mut v___x_3956_: usize = 0;
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: usize = 0;
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3974_: usize = 0;
    let mut v___x_3975_: usize = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: u8 = 0;
    let mut v___x_3979_: usize = 0;
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3998_: usize = 0;
    let mut v___x_3999_: usize = 0;
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_a_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_a_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v_ref_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3981_ = lean_st_ref_get(v_a_3925_);
                v___x_3982_ = l_Lean_versoDocStringExt;
                v_toEnvExtension_3983_ = crate::leanh::lean_ctor_get(v___x_3982_, 0);
                v_asyncMode_3984_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3983_, 2);
                v___x_3985_ = l_Lean_getBuiltinVersoDocStrings();
                if crate::leanh::lean_obj_tag(v___x_3985_) == 0 {
                    v_a_3986_ = crate::leanh::lean_ctor_get(v___x_3985_, 0);
                    crate::leanh::lean_inc(v_a_3986_);
                    crate::leanh::lean_dec_ref_known(v___x_3985_, 1);
                    v_checked_3987_ = l_Lean_Doc_checkPostponed___closed__7;
                    v___x_3988_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_checked_3987_, v_a_3986_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
                    if crate::leanh::lean_obj_tag(v___x_3988_) == 0 {
                        v_a_3989_ = crate::leanh::lean_ctor_get(v___x_3988_, 0);
                        crate::leanh::lean_inc(v_a_3989_);
                        crate::leanh::lean_dec_ref_known(v___x_3988_, 1);
                        v_env_3990_ = crate::leanh::lean_ctor_get(v___x_3981_, 0);
                        crate::leanh::lean_inc_ref(v_env_3990_);
                        crate::leanh::lean_dec(v___x_3981_);
                        v___x_3991_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__8),
                            core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__8_once),
                            _init_l_Lean_Doc_checkPostponed___closed__8,
                        );
                        v___x_3992_ = crate::leanh::lean_box(0);
                        v___x_3993_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3991_, v_toEnvExtension_3983_, v_env_3990_, v_asyncMode_3984_, v___x_3992_);
                        v_a_4021_ = crate::leanh::lean_ctor_get(v_a_3989_, 0);
                        crate::leanh::lean_inc(v_a_4021_);
                        crate::leanh::lean_dec(v_a_3989_);
                        v_a_3995_ = v_a_4021_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3981_);
                        v_a_4022_ = crate::leanh::lean_ctor_get(v___x_3988_, 0);
                        v_isSharedCheck_4029_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3988_)) as u8;
                        if v_isSharedCheck_4029_ == 0 {
                            v___x_4024_ = v___x_3988_;
                            v_isShared_4025_ = v_isSharedCheck_4029_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4022_);
                            crate::leanh::lean_dec(v___x_3988_);
                            v___x_4024_ = crate::leanh::lean_box(0);
                            v_isShared_4025_ = v_isSharedCheck_4029_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3981_);
                    v_a_4030_ = crate::leanh::lean_ctor_get(v___x_3985_, 0);
                    v_isSharedCheck_4042_ = (!crate::leanh::lean_is_exclusive(v___x_3985_)) as u8;
                    if v_isSharedCheck_4042_ == 0 {
                        v___x_4032_ = v___x_3985_;
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4030_);
                        crate::leanh::lean_dec(v___x_3985_);
                        v___x_4032_ = crate::leanh::lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3932_ = l_Nat_reprFast(v___y_3931_);
                v___x_3933_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3933_, 0, v___x_3932_);
                v___x_3934_ = l_Lean_MessageData_ofFormat(v___x_3933_);
                v___x_3935_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3935_, 0, v___y_3930_);
                crate::leanh::lean_ctor_set(v___x_3935_, 1, v___x_3934_);
                v___x_3936_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7);
                v___x_3937_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3937_, 0, v___x_3935_);
                crate::leanh::lean_ctor_set(v___x_3937_, 1, v___x_3936_);
                v_sz_3938_ = lean_array_size(v___y_3928_);
                v___x_3939_ = 0usize;
                v___x_3940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2(v_sz_3938_, v___x_3939_, v___y_3928_);
                crate::leanh::lean_inc_ref(v___y_3929_);
                v___x_3941_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3941_, 0, v___y_3929_);
                crate::leanh::lean_ctor_set(v___x_3941_, 1, v___x_3937_);
                crate::leanh::lean_ctor_set(v___x_3941_, 2, v___x_3940_);
                v___x_3942_ = l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3(
                    v___x_3941_,
                    v_a_3920_,
                    v_a_3921_,
                    v_a_3922_,
                    v_a_3923_,
                    v_a_3924_,
                    v_a_3925_,
                );
                return v___x_3942_;
            }
            2 => {
                v___x_3949_ = l_Nat_reprFast(v___y_3948_);
                v___x_3950_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3949_);
                v___x_3951_ = l_Lean_MessageData_ofFormat(v___x_3950_);
                v___x_3952_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3952_, 0, v___y_3947_);
                crate::leanh::lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                v___x_3953_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5);
                v___x_3954_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3954_, 0, v___x_3952_);
                crate::leanh::lean_ctor_set(v___x_3954_, 1, v___x_3953_);
                v_sz_3955_ = lean_array_size(v___y_3945_);
                v___x_3956_ = 0usize;
                crate::leanh::lean_inc_ref(v___y_3945_);
                v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4(v_sz_3955_, v___x_3956_, v___y_3945_);
                v___x_3958_ = lean_array_get_size(v___x_3957_);
                v___x_3959_ = lean_nat_dec_lt(v___y_3944_, v___x_3958_);
                if v___x_3959_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3957_);
                    v___y_3928_ = v___y_3945_;
                    v___y_3929_ = v___y_3946_;
                    v___y_3930_ = v___x_3954_;
                    v___y_3931_ = v___y_3944_;
                    state = 1;
                    continue;
                } else {
                    v___x_3960_ = lean_usize_of_nat(v___x_3958_);
                    v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(v___x_3957_, v___x_3960_, v___x_3956_, v___y_3944_);
                    crate::leanh::lean_dec_ref(v___x_3957_);
                    v___y_3928_ = v___y_3945_;
                    v___y_3929_ = v___y_3946_;
                    v___y_3930_ = v___x_3954_;
                    v___y_3931_ = v___x_3961_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3964_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3965_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__2_once),
                    _init_l_Lean_Doc_checkPostponed___closed__2,
                );
                v___x_3966_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__4_once),
                    _init_l_Lean_Doc_checkPostponed___closed__4,
                );
                v___x_3967_ = lean_array_get_size(v_a_3963_);
                v___x_3968_ = l_Nat_reprFast(v___x_3967_);
                v___x_3969_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3969_, 0, v___x_3968_);
                v___x_3970_ = l_Lean_MessageData_ofFormat(v___x_3969_);
                v___x_3971_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3971_, 0, v___x_3966_);
                crate::leanh::lean_ctor_set(v___x_3971_, 1, v___x_3970_);
                v___x_3972_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Doc_checkPostponed___closed__6_once),
                    _init_l_Lean_Doc_checkPostponed___closed__6,
                );
                v___x_3973_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3973_, 0, v___x_3971_);
                crate::leanh::lean_ctor_set(v___x_3973_, 1, v___x_3972_);
                v_sz_3974_ = lean_array_size(v_a_3963_);
                v___x_3975_ = 0usize;
                crate::leanh::lean_inc_ref(v_a_3963_);
                v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6(v_sz_3974_, v___x_3975_, v_a_3963_);
                v___x_3977_ = lean_array_get_size(v___x_3976_);
                v___x_3978_ = lean_nat_dec_lt(v___x_3964_, v___x_3977_);
                if v___x_3978_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3976_);
                    v___y_3944_ = v___x_3964_;
                    v___y_3945_ = v_a_3963_;
                    v___y_3946_ = v___x_3965_;
                    v___y_3947_ = v___x_3973_;
                    v___y_3948_ = v___x_3964_;
                    state = 2;
                    continue;
                } else {
                    v___x_3979_ = lean_usize_of_nat(v___x_3977_);
                    v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(v___x_3976_, v___x_3979_, v___x_3975_, v___x_3964_);
                    crate::leanh::lean_dec_ref(v___x_3976_);
                    v___y_3944_ = v___x_3964_;
                    v___y_3945_ = v_a_3963_;
                    v___y_3946_ = v___x_3965_;
                    v___y_3947_ = v___x_3973_;
                    v___y_3948_ = v___x_3980_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_importedEntries_3996_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                crate::leanh::lean_inc_ref(v_importedEntries_3996_);
                v_state_3997_ = crate::leanh::lean_ctor_get(v___x_3993_, 1);
                crate::leanh::lean_inc(v_state_3997_);
                crate::leanh::lean_dec(v___x_3993_);
                v_sz_3998_ = lean_array_size(v_importedEntries_3996_);
                v___x_3999_ = 0usize;
                v___x_4000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8(v_importedEntries_3996_, v_sz_3998_, v___x_3999_, v_a_3995_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
                crate::leanh::lean_dec_ref(v_importedEntries_3996_);
                if crate::leanh::lean_obj_tag(v___x_4000_) == 0 {
                    v_a_4001_ = crate::leanh::lean_ctor_get(v___x_4000_, 0);
                    crate::leanh::lean_inc(v_a_4001_);
                    crate::leanh::lean_dec_ref_known(v___x_4000_, 1);
                    v___x_4002_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9(v_a_4001_, v_state_3997_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
                    if crate::leanh::lean_obj_tag(v___x_4002_) == 0 {
                        v_a_4003_ = crate::leanh::lean_ctor_get(v___x_4002_, 0);
                        crate::leanh::lean_inc(v_a_4003_);
                        crate::leanh::lean_dec_ref_known(v___x_4002_, 1);
                        v_a_4004_ = crate::leanh::lean_ctor_get(v_a_4003_, 0);
                        crate::leanh::lean_inc(v_a_4004_);
                        crate::leanh::lean_dec(v_a_4003_);
                        v_a_3963_ = v_a_4004_;
                        state = 3;
                        continue;
                    } else {
                        v_a_4005_ = crate::leanh::lean_ctor_get(v___x_4002_, 0);
                        v_isSharedCheck_4012_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4002_)) as u8;
                        if v_isSharedCheck_4012_ == 0 {
                            v___x_4007_ = v___x_4002_;
                            v_isShared_4008_ = v_isSharedCheck_4012_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4005_);
                            crate::leanh::lean_dec(v___x_4002_);
                            v___x_4007_ = crate::leanh::lean_box(0);
                            v_isShared_4008_ = v_isSharedCheck_4012_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_state_3997_);
                    v_a_4013_ = crate::leanh::lean_ctor_get(v___x_4000_, 0);
                    v_isSharedCheck_4020_ = (!crate::leanh::lean_is_exclusive(v___x_4000_)) as u8;
                    if v_isSharedCheck_4020_ == 0 {
                        v___x_4015_ = v___x_4000_;
                        v_isShared_4016_ = v_isSharedCheck_4020_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4013_);
                        crate::leanh::lean_dec(v___x_4000_);
                        v___x_4015_ = crate::leanh::lean_box(0);
                        v_isShared_4016_ = v_isSharedCheck_4020_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4008_ == 0 {
                    v___x_4010_ = v___x_4007_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
                    v___x_4010_ = v_reuseFailAlloc_4011_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4010_;
            }
            7 => {
                if v_isShared_4016_ == 0 {
                    v___x_4018_ = v___x_4015_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4018_;
            }
            9 => {
                if v_isShared_4025_ == 0 {
                    v___x_4027_ = v___x_4024_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4028_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
                    v___x_4027_ = v_reuseFailAlloc_4028_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4027_;
            }
            11 => {
                v_ref_4034_ = crate::leanh::lean_ctor_get(v_a_3924_, 5);
                v___x_4035_ = lean_io_error_to_string(v_a_4030_);
                v___x_4036_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4036_, 0, v___x_4035_);
                v___x_4037_ = l_Lean_MessageData_ofFormat(v___x_4036_);
                crate::leanh::lean_inc(v_ref_4034_);
                v___x_4038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4038_, 0, v_ref_4034_);
                crate::leanh::lean_ctor_set(v___x_4038_, 1, v___x_4037_);
                if v_isShared_4033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4032_, 0, v___x_4038_);
                    v___x_4040_ = v___x_4032_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
                    v___x_4040_ = v_reuseFailAlloc_4041_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_checkPostponed___boxed(
    mut v_a_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
    mut v_a_4048_: *mut crate::leanh::LeanObject,
    mut v_a_4049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4050_ = l_Lean_Doc_checkPostponed(
        v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_,
    );
    crate::leanh::lean_dec(v_a_4048_);
    crate::leanh::lean_dec_ref(v_a_4047_);
    crate::leanh::lean_dec(v_a_4046_);
    crate::leanh::lean_dec_ref(v_a_4045_);
    crate::leanh::lean_dec(v_a_4044_);
    crate::leanh::lean_dec_ref(v_a_4043_);
    return v_res_4050_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5(
    mut v_ref_4051_: *mut crate::leanh::LeanObject,
    mut v_msgData_4052_: *mut crate::leanh::LeanObject,
    mut v_severity_4053_: u8,
    mut v_isSilent_4054_: u8,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___y_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(v_ref_4051_, v_msgData_4052_, v_severity_4053_, v_isSilent_4054_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
    return v___x_4062_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___boxed(
    mut v_ref_4063_: *mut crate::leanh::LeanObject,
    mut v_msgData_4064_: *mut crate::leanh::LeanObject,
    mut v_severity_4065_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
    mut v___y_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4074_: u8 = 0;
    let mut v_isSilent_boxed_4075_: u8 = 0;
    let mut v_res_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4074_ = (crate::leanh::lean_unbox(v_severity_4065_) as u8);
    v_isSilent_boxed_4075_ = (crate::leanh::lean_unbox(v_isSilent_4066_) as u8);
    v_res_4076_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5(v_ref_4063_, v_msgData_4064_, v_severity_boxed_4074_, v_isSilent_boxed_4075_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
    crate::leanh::lean_dec(v___y_4072_);
    crate::leanh::lean_dec_ref(v___y_4071_);
    crate::leanh::lean_dec(v___y_4070_);
    crate::leanh::lean_dec_ref(v___y_4069_);
    crate::leanh::lean_dec(v___y_4068_);
    crate::leanh::lean_dec_ref(v___y_4067_);
    crate::leanh::lean_dec(v_ref_4063_);
    return v_res_4076_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Doc_instToExprPostponedImport = _init_l_Lean_Doc_instToExprPostponedImport();
    crate::leanh::lean_mark_persistent(l_Lean_Doc_instToExprPostponedImport);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DocString_Builtin_Postponed(
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
pub unsafe fn initialize_Lean_Elab_DocString_Builtin_Postponed(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
}

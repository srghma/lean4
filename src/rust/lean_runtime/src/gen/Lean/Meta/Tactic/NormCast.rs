// Lean compiler output
// Module: Lean.Meta.Tactic.NormCast
// Imports: Lean.Meta.Tactic.Simp.Attr Lean.Meta.CoeAttr
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNatLit_x3f, l_Lean_Syntax_isNone, l_Lean_Syntax_isStrLit_x3f,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_sort___override,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
};
use crate::r#gen::Lean::Meta::CoeAttr::{
    initialize_Lean_Meta_CoeAttr, l_Lean_Meta_getCoeFnInfo_x3f___redArg,
    runtime_initialize_Lean_Meta_CoeAttr,
};
use crate::r#gen::Lean::Meta::CongrTheorems::l_Lean_Meta_mkCongrSimp_x3f;
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::{
    initialize_Lean_Meta_Tactic_Simp_Attr, l_Lean_Meta_registerSimpAttr,
    runtime_initialize_Lean_Meta_Tactic_Simp_Attr,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_addSimpTheorem, l_Lean_Meta_instInhabitedSimpEntry_default, l_Lean_Meta_mkSimpExt,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_instInhabitedScopedEnvExtension_default___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_NormCast_instReprLabel_repr___closed__0_value: LeanStringObject<30> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 78, 111, 114, 109, 67, 97, 115, 116, 46,
            76, 97, 98, 101, 108, 46, 101, 108, 105, 109, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_instReprLabel_repr___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_instReprLabel_repr___closed__2_value: LeanStringObject<30> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 78, 111, 114, 109, 67, 97, 115, 116, 46,
            76, 97, 98, 101, 108, 46, 109, 111, 118, 101, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_instReprLabel_repr___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_instReprLabel_repr___closed__4_value: LeanStringObject<32> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 78, 111, 114, 109, 67, 97, 115, 116, 46,
            76, 97, 98, 101, 108, 46, 115, 113, 117, 97, 115, 104, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_instReprLabel_repr___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel_repr___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_NormCast_instReprLabel_repr___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_NormCast_instReprLabel___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_NormCast_instReprLabel_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_NormCast_instReprLabel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_NormCast_instReprLabel: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_instReprLabel___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_NormCast_instInhabitedLabel_default: u8 = 0;
pub static mut l_Lean_Meta_NormCast_instInhabitedLabel: u8 = 0;
static mut l_Lean_Meta_NormCast_getSimpArgs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_NormCast_getSimpArgs___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_NormCast_getSimpArgs___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_NormCast_getSimpArgs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_getSimpArgs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__0_value: LeanStringObject<125> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 125,
        m_capacity: 125,
        m_length: 124,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 96, 110, 111, 114, 109, 95, 99, 97, 115, 116, 96,
            32, 115, 113, 117, 97, 115, 104, 32, 108, 101, 109, 109, 97, 58, 32, 84, 104, 101, 32,
            114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 109, 117,
            115, 116, 32, 104, 97, 118, 101, 32, 102, 101, 119, 101, 114, 32, 99, 111, 101, 32,
            102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 105, 110, 32, 104, 101, 97, 100, 32,
            112, 111, 115, 105, 116, 105, 111, 110, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32,
            108, 101, 102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__2_value: LeanStringObject<80> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 80,
        m_capacity: 80,
        m_length: 79,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 96, 110, 111, 114, 109, 95, 99, 97, 115, 116, 96,
            32, 108, 101, 109, 109, 97, 58, 32, 84, 104, 101, 32, 114, 105, 103, 104, 116, 45, 104,
            97, 110, 100, 32, 115, 105, 100, 101, 32, 99, 97, 110, 110, 111, 116, 32, 115, 116, 97,
            114, 116, 32, 119, 105, 116, 104, 32, 97, 32, 99, 111, 101, 32, 102, 117, 110, 99, 116,
            105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__4_value: LeanStringObject<57> =
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
            99, 111, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 97, 114, 101, 32,
            114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 117, 115, 105, 110, 103, 32, 116,
            104, 101, 32, 96, 91, 99, 111, 101, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116,
            101, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__7_value: LeanStringObject<87> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 87,
        m_capacity: 87,
        m_length: 86,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 96, 110, 111, 114, 109, 95, 99, 97, 115, 116, 96,
            32, 108, 101, 109, 109, 97, 58, 32, 65, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110,
            101, 32, 99, 111, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 109, 117, 115,
            116, 32, 97, 112, 112, 101, 97, 114, 32, 105, 110, 32, 116, 104, 101, 32, 108, 101,
            102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__9_value: LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__9_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__11_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [73, 102, 102, 0],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__11_value)
                as *mut LeanObject,
            9917798623386220051 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_NormCast_classifyType___lam__0___closed__13_value: LeanStringObject<66> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 66,
        m_capacity: 66,
        m_length: 65,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 96, 110, 111, 114, 109, 95, 99, 97, 115, 116, 96,
            32, 108, 101, 109, 109, 97, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 110,
            32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 111, 114, 32, 105, 102, 102, 44, 32, 98,
            117, 116, 32, 102, 111, 117, 110, 100, 0,
        ],
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_NormCast_classifyType___lam__0___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_NormCast_classifyType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_NormCast_classifyType___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_NormCast_classifyType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_NormCast_classifyType___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [112, 117, 115, 104, 95, 99, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,4764961446274960781 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanStringObject<110> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 110, m_capacity: 110, m_length: 109, m_data: [84, 104, 101, 32, 96, 112, 117, 115, 104, 95, 99, 97, 115, 116, 96, 32, 115, 105, 109, 112, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 117, 115, 101, 115, 32, 96, 110, 111, 114, 109, 95, 99, 97, 115, 116, 96, 32, 108, 101, 109, 109, 97, 115, 32, 116, 111, 32, 109, 111, 118, 101, 32, 99, 97, 115, 116, 115, 32, 116, 111, 119, 97, 114, 100, 32, 116, 104, 101, 32, 108, 101, 97, 102, 32, 110, 111, 100, 101, 115, 32, 111, 102, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 114, 109, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 117, 115, 104, 67, 97, 115, 116, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,8320990086402145376 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,9742163610051219255 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_NormCast_instInhabitedNormCastExtension: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [110, 111, 114, 109, 67, 97, 115, 116, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,8320990086402145376 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject,11452230133256069293 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [117, 112, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject,12298694990734487511 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 119, 110, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject,7898352899929208865 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 113, 117, 97, 115, 104, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject,17760035944850579050 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 105, 109, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 111, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 78, 111, 114, 109, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<118> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 118, m_capacity: 118, m_length: 117, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 78, 111, 114, 109, 67, 97, 115, 116, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 78, 111, 114, 109, 67, 97, 115, 116, 46, 105, 110, 105, 116, 70, 110, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 78, 111, 114, 109, 67, 97, 115, 116, 46, 49, 49, 49, 53, 54, 51, 57, 52, 48, 49, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 50, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 111, 114, 109, 67, 97, 115, 116, 76, 97, 98, 101, 108, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,7057945283777486837 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,11888402484136347104 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,18445426737760335001 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,18127077607718791241 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,16909865055707097415 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,2080301092182656630 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,268164492338863175 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,17184750147493404090 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,7566866690765466686 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,7535127072843090467 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,2717582210836462485 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,((( 1115639401 as usize) << 1) | 1) as *mut LeanObject,4282508740204375221 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,7925680605179555878 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,6658885075544115546 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,12647632092175954243 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 114, 109, 95, 99, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanClosureObject<5> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*5) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 5, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,10284954155394180171 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 102, 111, 114, 32, 110, 111, 114, 109, 95, 99, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_NormCast_Label_ctorIdx(mut v_x_1935_: u8) -> *mut LeanObject {
    match v_x_1935_ {
        0 => {
            let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
            v___x_1936_ = lean_unsigned_to_nat(0);
            return v___x_1936_;
        }
        1 => {
            let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
            v___x_1937_ = lean_unsigned_to_nat(1);
            return v___x_1937_;
        }
        _ => {
            let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
            v___x_1938_ = lean_unsigned_to_nat(2);
            return v___x_1938_;
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_Label_ctorIdx___boxed(
    mut v_x_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1940_: u8 = 0;
    let mut v_res_1941_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1940_ = (lean_unbox(v_x_1939_) as u8);
    v_res_1941_ = l_Lean_Meta_NormCast_Label_ctorIdx(v_x_boxed_1940_);
    return v_res_1941_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_toCtorIdx(mut v_x_1942_: u8) -> *mut LeanObject {
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Lean_Meta_NormCast_Label_ctorIdx(v_x_1942_);
    return v___x_1943_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_toCtorIdx___boxed(
    mut v_x_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1945_: u8 = 0;
    let mut v_res_1946_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1945_ = (lean_unbox(v_x_1944_) as u8);
    v_res_1946_ = l_Lean_Meta_NormCast_Label_toCtorIdx(v_x_4__boxed_1945_);
    return v_res_1946_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_ctorElim___redArg(
    mut v_k_1947_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1947_);
    return v_k_1947_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_ctorElim___redArg___boxed(
    mut v_k_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Lean_Meta_NormCast_Label_ctorElim___redArg(v_k_1948_);
    lean_dec(v_k_1948_);
    return v_res_1949_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_ctorElim(
    mut v_motive_1950_: *mut LeanObject,
    mut v_ctorIdx_1951_: *mut LeanObject,
    mut v_t_1952_: u8,
    mut v_h_1953_: *mut LeanObject,
    mut v_k_1954_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1954_);
    return v_k_1954_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_ctorElim___boxed(
    mut v_motive_1955_: *mut LeanObject,
    mut v_ctorIdx_1956_: *mut LeanObject,
    mut v_t_1957_: *mut LeanObject,
    mut v_h_1958_: *mut LeanObject,
    mut v_k_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1960_: u8 = 0;
    let mut v_res_1961_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1960_ = (lean_unbox(v_t_1957_) as u8);
    v_res_1961_ = l_Lean_Meta_NormCast_Label_ctorElim(
        v_motive_1955_,
        v_ctorIdx_1956_,
        v_t_boxed_1960_,
        v_h_1958_,
        v_k_1959_,
    );
    lean_dec(v_k_1959_);
    lean_dec(v_ctorIdx_1956_);
    return v_res_1961_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_elim_elim___redArg(
    mut v_elim_1962_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_elim_1962_);
    return v_elim_1962_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_elim_elim___redArg___boxed(
    mut v_elim_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1964_: *mut LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_Meta_NormCast_Label_elim_elim___redArg(v_elim_1963_);
    lean_dec(v_elim_1963_);
    return v_res_1964_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_elim_elim(
    mut v_motive_1965_: *mut LeanObject,
    mut v_t_1966_: u8,
    mut v_h_1967_: *mut LeanObject,
    mut v_elim_1968_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_elim_1968_);
    return v_elim_1968_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_elim_elim___boxed(
    mut v_motive_1969_: *mut LeanObject,
    mut v_t_1970_: *mut LeanObject,
    mut v_h_1971_: *mut LeanObject,
    mut v_elim_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1973_: u8 = 0;
    let mut v_res_1974_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1973_ = (lean_unbox(v_t_1970_) as u8);
    v_res_1974_ = l_Lean_Meta_NormCast_Label_elim_elim(
        v_motive_1969_,
        v_t_boxed_1973_,
        v_h_1971_,
        v_elim_1972_,
    );
    lean_dec(v_elim_1972_);
    return v_res_1974_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_move_elim___redArg(
    mut v_move_1975_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_move_1975_);
    return v_move_1975_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_move_elim___redArg___boxed(
    mut v_move_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Lean_Meta_NormCast_Label_move_elim___redArg(v_move_1976_);
    lean_dec(v_move_1976_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_move_elim(
    mut v_motive_1978_: *mut LeanObject,
    mut v_t_1979_: u8,
    mut v_h_1980_: *mut LeanObject,
    mut v_move_1981_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_move_1981_);
    return v_move_1981_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_move_elim___boxed(
    mut v_motive_1982_: *mut LeanObject,
    mut v_t_1983_: *mut LeanObject,
    mut v_h_1984_: *mut LeanObject,
    mut v_move_1985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1986_: u8 = 0;
    let mut v_res_1987_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1986_ = (lean_unbox(v_t_1983_) as u8);
    v_res_1987_ = l_Lean_Meta_NormCast_Label_move_elim(
        v_motive_1982_,
        v_t_boxed_1986_,
        v_h_1984_,
        v_move_1985_,
    );
    lean_dec(v_move_1985_);
    return v_res_1987_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_squash_elim___redArg(
    mut v_squash_1988_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_squash_1988_);
    return v_squash_1988_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_squash_elim___redArg___boxed(
    mut v_squash_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1990_: *mut LeanObject = core::ptr::null_mut();
    v_res_1990_ = l_Lean_Meta_NormCast_Label_squash_elim___redArg(v_squash_1989_);
    lean_dec(v_squash_1989_);
    return v_res_1990_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_squash_elim(
    mut v_motive_1991_: *mut LeanObject,
    mut v_t_1992_: u8,
    mut v_h_1993_: *mut LeanObject,
    mut v_squash_1994_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_squash_1994_);
    return v_squash_1994_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_squash_elim___boxed(
    mut v_motive_1995_: *mut LeanObject,
    mut v_t_1996_: *mut LeanObject,
    mut v_h_1997_: *mut LeanObject,
    mut v_squash_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1999_: u8 = 0;
    let mut v_res_2000_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1999_ = (lean_unbox(v_t_1996_) as u8);
    v_res_2000_ = l_Lean_Meta_NormCast_Label_squash_elim(
        v_motive_1995_,
        v_t_boxed_1999_,
        v_h_1997_,
        v_squash_1998_,
    );
    lean_dec(v_squash_1998_);
    return v_res_2000_;
}
pub unsafe fn l_Lean_Meta_NormCast_Label_ofNat(mut v_n_2001_: *mut LeanObject) -> u8 {
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    v___x_2002_ = lean_unsigned_to_nat(0);
    v___x_2003_ = lean_nat_dec_le(v_n_2001_, v___x_2002_);
    if v___x_2003_ == 0 {
        let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: u8 = 0;
        v___x_2004_ = lean_unsigned_to_nat(1);
        v___x_2005_ = lean_nat_dec_le(v_n_2001_, v___x_2004_);
        if v___x_2005_ == 0 {
            let mut v___x_2006_: u8 = 0;
            v___x_2006_ = 2;
            return v___x_2006_;
        } else {
            let mut v___x_2007_: u8 = 0;
            v___x_2007_ = 1;
            return v___x_2007_;
        }
    } else {
        let mut v___x_2008_: u8 = 0;
        v___x_2008_ = 0;
        return v___x_2008_;
    }
}
pub unsafe fn l_Lean_Meta_NormCast_Label_ofNat___boxed(
    mut v_n_2009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2010_: u8 = 0;
    let mut v_r_2011_: *mut LeanObject = core::ptr::null_mut();
    v_res_2010_ = l_Lean_Meta_NormCast_Label_ofNat(v_n_2009_);
    lean_dec(v_n_2009_);
    v_r_2011_ = lean_box((v_res_2010_) as usize);
    return v_r_2011_;
}
pub unsafe fn l_Lean_Meta_NormCast_instDecidableEqLabel(
    mut v_x_2012_: u8,
    mut v_y_2013_: u8,
) -> u8 {
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    v___x_2014_ = l_Lean_Meta_NormCast_Label_ctorIdx(v_x_2012_);
    v___x_2015_ = l_Lean_Meta_NormCast_Label_ctorIdx(v_y_2013_);
    v___x_2016_ = lean_nat_dec_eq(v___x_2014_, v___x_2015_);
    lean_dec(v___x_2015_);
    lean_dec(v___x_2014_);
    return v___x_2016_;
}
pub unsafe fn l_Lean_Meta_NormCast_instDecidableEqLabel___boxed(
    mut v_x_2017_: *mut LeanObject,
    mut v_y_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_2019_: u8 = 0;
    let mut v_y_14__boxed_2020_: u8 = 0;
    let mut v_res_2021_: u8 = 0;
    let mut v_r_2022_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_2019_ = (lean_unbox(v_x_2017_) as u8);
    v_y_14__boxed_2020_ = (lean_unbox(v_y_2018_) as u8);
    v_res_2021_ =
        l_Lean_Meta_NormCast_instDecidableEqLabel(v_x_13__boxed_2019_, v_y_14__boxed_2020_);
    v_r_2022_ = lean_box((v_res_2021_) as usize);
    return v_r_2022_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6() -> *mut LeanObject {
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    v___x_2032_ = lean_unsigned_to_nat(2);
    v___x_2033_ = lean_nat_to_int(v___x_2032_);
    return v___x_2033_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7() -> *mut LeanObject {
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v___x_2034_ = lean_unsigned_to_nat(1);
    v___x_2035_ = lean_nat_to_int(v___x_2034_);
    return v___x_2035_;
}
pub unsafe fn l_Lean_Meta_NormCast_instReprLabel_repr(
    mut v_x_2036_: u8,
    mut v_prec_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2036_ {
                0 => {
                    v___x_2059_ = lean_unsigned_to_nat(1024);
                    v___x_2060_ = lean_nat_dec_le(v___x_2059_, v_prec_2037_);
                    if v___x_2060_ == 0 {
                        v___x_2061_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6,
                        );
                        v___y_2039_ = v___x_2061_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2062_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7,
                        );
                        v___y_2039_ = v___x_2062_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2063_ = lean_unsigned_to_nat(1024);
                    v___x_2064_ = lean_nat_dec_le(v___x_2063_, v_prec_2037_);
                    if v___x_2064_ == 0 {
                        v___x_2065_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6,
                        );
                        v___y_2046_ = v___x_2065_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2066_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7,
                        );
                        v___y_2046_ = v___x_2066_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_2067_ = lean_unsigned_to_nat(1024);
                    v___x_2068_ = lean_nat_dec_le(v___x_2067_, v_prec_2037_);
                    if v___x_2068_ == 0 {
                        v___x_2069_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6,
                        );
                        v___y_2053_ = v___x_2069_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2070_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7,
                        );
                        v___y_2053_ = v___x_2070_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2040_ = l_Lean_Meta_NormCast_instReprLabel_repr___closed__1;
                lean_inc(v___y_2039_);
                v___x_2041_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2041_, 0, v___y_2039_);
                lean_ctor_set(v___x_2041_, 1, v___x_2040_);
                v___x_2042_ = 0;
                v___x_2043_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2043_, 0, v___x_2041_);
                lean_ctor_set_uint8(
                    v___x_2043_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2042_,
                );
                v___x_2044_ = l_Repr_addAppParen(v___x_2043_, v_prec_2037_);
                return v___x_2044_;
            }
            2 => {
                v___x_2047_ = l_Lean_Meta_NormCast_instReprLabel_repr___closed__3;
                lean_inc(v___y_2046_);
                v___x_2048_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2048_, 0, v___y_2046_);
                lean_ctor_set(v___x_2048_, 1, v___x_2047_);
                v___x_2049_ = 0;
                v___x_2050_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2050_, 0, v___x_2048_);
                lean_ctor_set_uint8(
                    v___x_2050_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2049_,
                );
                v___x_2051_ = l_Repr_addAppParen(v___x_2050_, v_prec_2037_);
                return v___x_2051_;
            }
            3 => {
                v___x_2054_ = l_Lean_Meta_NormCast_instReprLabel_repr___closed__5;
                lean_inc(v___y_2053_);
                v___x_2055_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2055_, 0, v___y_2053_);
                lean_ctor_set(v___x_2055_, 1, v___x_2054_);
                v___x_2056_ = 0;
                v___x_2057_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2057_, 0, v___x_2055_);
                lean_ctor_set_uint8(
                    v___x_2057_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2056_,
                );
                v___x_2058_ = l_Repr_addAppParen(v___x_2057_, v_prec_2037_);
                return v___x_2058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_instReprLabel_repr___boxed(
    mut v_x_2071_: *mut LeanObject,
    mut v_prec_2072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_177__boxed_2073_: u8 = 0;
    let mut v_res_2074_: *mut LeanObject = core::ptr::null_mut();
    v_x_177__boxed_2073_ = (lean_unbox(v_x_2071_) as u8);
    v_res_2074_ = l_Lean_Meta_NormCast_instReprLabel_repr(v_x_177__boxed_2073_, v_prec_2072_);
    lean_dec(v_prec_2072_);
    return v_res_2074_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instInhabitedLabel_default() -> u8 {
    let mut v___x_2077_: u8 = 0;
    v___x_2077_ = 0;
    return v___x_2077_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instInhabitedLabel() -> u8 {
    let mut v___x_2078_: u8 = 0;
    v___x_2078_ = 0;
    return v___x_2078_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(
    mut v_as_2079_: *mut LeanObject,
    mut v_sz_2080_: usize,
    mut v_i_2081_: usize,
    mut v_b_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: usize = 0;
    let mut v___x_2087_: usize = 0;
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v_array_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: u8 = 0;
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v_a_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2122_: u8 = 0;
    let mut v_unused_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2089_ = lean_usize_dec_lt(v_i_2081_, v_sz_2080_);
                if v___x_2089_ == 0 {
                    v___x_2090_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2090_, 0, v_b_2082_);
                    return v___x_2090_;
                } else {
                    v_snd_2091_ = lean_ctor_get(v_b_2082_, 1);
                    v_fst_2092_ = lean_ctor_get(v_b_2082_, 0);
                    v_isSharedCheck_2126_ = (!lean_is_exclusive(v_b_2082_)) as u8;
                    if v_isSharedCheck_2126_ == 0 {
                        v___x_2094_ = v_b_2082_;
                        v_isShared_2095_ = v_isSharedCheck_2126_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_2091_);
                        lean_inc(v_fst_2092_);
                        lean_dec(v_b_2082_);
                        v___x_2094_ = lean_box(0);
                        v_isShared_2095_ = v_isSharedCheck_2126_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2086_ = 1usize;
                v___x_2087_ = lean_usize_add(v_i_2081_, v___x_2086_);
                v_i_2081_ = v___x_2087_;
                v_b_2082_ = v_a_2085_;
                state = 0;
                continue;
            }
            2 => {
                v_array_2096_ = lean_ctor_get(v_snd_2091_, 0);
                v_start_2097_ = lean_ctor_get(v_snd_2091_, 1);
                v_stop_2098_ = lean_ctor_get(v_snd_2091_, 2);
                v___x_2099_ = lean_nat_dec_lt(v_start_2097_, v_stop_2098_);
                if v___x_2099_ == 0 {
                    if v_isShared_2095_ == 0 {
                        v___x_2101_ = v___x_2094_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_fst_2092_);
                        lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_snd_2091_);
                        v___x_2101_ = v_reuseFailAlloc_2103_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_2098_);
                    lean_inc(v_start_2097_);
                    lean_inc_ref(v_array_2096_);
                    v_isSharedCheck_2122_ = (!lean_is_exclusive(v_snd_2091_)) as u8;
                    if v_isSharedCheck_2122_ == 0 {
                        v_unused_2123_ = lean_ctor_get(v_snd_2091_, 2);
                        lean_dec(v_unused_2123_);
                        v_unused_2124_ = lean_ctor_get(v_snd_2091_, 1);
                        lean_dec(v_unused_2124_);
                        v_unused_2125_ = lean_ctor_get(v_snd_2091_, 0);
                        lean_dec(v_unused_2125_);
                        v___x_2105_ = v_snd_2091_;
                        v_isShared_2106_ = v_isSharedCheck_2122_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_snd_2091_);
                        v___x_2105_ = lean_box(0);
                        v_isShared_2106_ = v_isSharedCheck_2122_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2102_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2102_, 0, v___x_2101_);
                return v___x_2102_;
            }
            4 => {
                v___x_2107_ = lean_array_fget(v_array_2096_, v_start_2097_);
                v___x_2108_ = lean_unsigned_to_nat(1);
                v___x_2109_ = lean_nat_add(v_start_2097_, v___x_2108_);
                lean_dec(v_start_2097_);
                if v_isShared_2106_ == 0 {
                    lean_ctor_set(v___x_2105_, 1, v___x_2109_);
                    v___x_2111_ = v___x_2105_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_array_2096_);
                    lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2109_);
                    lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_stop_2098_);
                    v___x_2111_ = v_reuseFailAlloc_2121_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2112_ = (lean_unbox(v___x_2107_) as u8);
                lean_dec(v___x_2107_);
                if v___x_2112_ == 2 {
                    v_a_2113_ = lean_array_uget_borrowed(v_as_2079_, v_i_2081_);
                    lean_inc(v_a_2113_);
                    v___x_2114_ = lean_array_push(v_fst_2092_, v_a_2113_);
                    if v_isShared_2095_ == 0 {
                        lean_ctor_set(v___x_2094_, 1, v___x_2111_);
                        lean_ctor_set(v___x_2094_, 0, v___x_2114_);
                        v___x_2116_ = v___x_2094_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
                        lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2111_);
                        v___x_2116_ = v_reuseFailAlloc_2117_;
                        state = 6;
                        continue;
                    }
                } else {
                    if v_isShared_2095_ == 0 {
                        lean_ctor_set(v___x_2094_, 1, v___x_2111_);
                        v___x_2119_ = v___x_2094_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_fst_2092_);
                        lean_ctor_set(v_reuseFailAlloc_2120_, 1, v___x_2111_);
                        v___x_2119_ = v_reuseFailAlloc_2120_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v_a_2085_ = v___x_2116_;
                state = 1;
                continue;
            }
            7 => {
                v_a_2085_ = v___x_2119_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg___boxed(
    mut v_as_2127_: *mut LeanObject,
    mut v_sz_2128_: *mut LeanObject,
    mut v_i_2129_: *mut LeanObject,
    mut v_b_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2132_: usize = 0;
    let mut v_i_boxed_2133_: usize = 0;
    let mut v_res_2134_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2132_ = lean_unbox_usize(v_sz_2128_);
    lean_dec(v_sz_2128_);
    v_i_boxed_2133_ = lean_unbox_usize(v_i_2129_);
    lean_dec(v_i_2129_);
    v_res_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v_as_2127_, v_sz_boxed_2132_, v_i_boxed_2133_, v_b_2130_);
    lean_dec_ref(v_as_2127_);
    return v_res_2134_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0() -> *mut LeanObject {
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2136_: *mut LeanObject = core::ptr::null_mut();
    v___x_2135_ = lean_box(0);
    v_dummy_2136_ = l_Lean_Expr_sort___override(v___x_2135_);
    return v_dummy_2136_;
}
pub unsafe fn l_Lean_Meta_NormCast_getSimpArgs(
    mut v_e_2139_: *mut LeanObject,
    mut v_a_2140_: *mut LeanObject,
    mut v_a_2141_: *mut LeanObject,
    mut v_a_2142_: *mut LeanObject,
    mut v_a_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v_dummy_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argKinds_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2175_: usize = 0;
    let mut v___x_2176_: usize = 0;
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v_fst_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v_a_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_isSharedCheck_2195_: u8 = 0;
    let mut v_a_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2145_ = l_Lean_Expr_getAppFn(v_e_2139_);
                v___x_2146_ = 1;
                v___x_2147_ = lean_box(0);
                v___x_2148_ = l_Lean_Meta_mkCongrSimp_x3f(
                    v___x_2145_,
                    v___x_2146_,
                    v___x_2147_,
                    v_a_2140_,
                    v_a_2141_,
                    v_a_2142_,
                    v_a_2143_,
                );
                if lean_obj_tag(v___x_2148_) == 0 {
                    v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
                    v_isSharedCheck_2195_ = (!lean_is_exclusive(v___x_2148_)) as u8;
                    if v_isSharedCheck_2195_ == 0 {
                        v___x_2151_ = v___x_2148_;
                        v_isShared_2152_ = v_isSharedCheck_2195_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2149_);
                        lean_dec(v___x_2148_);
                        v___x_2151_ = lean_box(0);
                        v_isShared_2152_ = v_isSharedCheck_2195_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2139_);
                    v_a_2196_ = lean_ctor_get(v___x_2148_, 0);
                    v_isSharedCheck_2203_ = (!lean_is_exclusive(v___x_2148_)) as u8;
                    if v_isSharedCheck_2203_ == 0 {
                        v___x_2198_ = v___x_2148_;
                        v_isShared_2199_ = v_isSharedCheck_2203_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2196_);
                        lean_dec(v___x_2148_);
                        v___x_2198_ = lean_box(0);
                        v_isShared_2199_ = v_isSharedCheck_2203_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2149_) == 0 {
                    v_dummy_2153_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_NormCast_getSimpArgs___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Meta_NormCast_getSimpArgs___closed__0_once),
                        _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0,
                    );
                    v_nargs_2154_ = l_Lean_Expr_getAppNumArgs(v_e_2139_);
                    lean_inc(v_nargs_2154_);
                    v___x_2155_ = lean_mk_array(v_nargs_2154_, v_dummy_2153_);
                    v___x_2156_ = lean_unsigned_to_nat(1);
                    v___x_2157_ = lean_nat_sub(v_nargs_2154_, v___x_2156_);
                    lean_dec(v_nargs_2154_);
                    v___x_2158_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_2139_,
                        v___x_2155_,
                        v___x_2157_,
                    );
                    if v_isShared_2152_ == 0 {
                        lean_ctor_set(v___x_2151_, 0, v___x_2158_);
                        v___x_2160_ = v___x_2151_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
                        v___x_2160_ = v_reuseFailAlloc_2161_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2151_);
                    v_val_2162_ = lean_ctor_get(v_a_2149_, 0);
                    lean_inc(v_val_2162_);
                    lean_dec_ref_known(v_a_2149_, 1);
                    v_argKinds_2163_ = lean_ctor_get(v_val_2162_, 2);
                    lean_inc_ref(v_argKinds_2163_);
                    lean_dec(v_val_2162_);
                    v___x_2164_ = lean_unsigned_to_nat(0);
                    v___x_2165_ = l_Lean_Meta_NormCast_getSimpArgs___closed__1;
                    v___x_2166_ = lean_array_get_size(v_argKinds_2163_);
                    v___x_2167_ =
                        l_Array_toSubarray___redArg(v_argKinds_2163_, v___x_2164_, v___x_2166_);
                    v_dummy_2168_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_NormCast_getSimpArgs___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Meta_NormCast_getSimpArgs___closed__0_once),
                        _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0,
                    );
                    v_nargs_2169_ = l_Lean_Expr_getAppNumArgs(v_e_2139_);
                    lean_inc(v_nargs_2169_);
                    v___x_2170_ = lean_mk_array(v_nargs_2169_, v_dummy_2168_);
                    v___x_2171_ = lean_unsigned_to_nat(1);
                    v___x_2172_ = lean_nat_sub(v_nargs_2169_, v___x_2171_);
                    lean_dec(v_nargs_2169_);
                    v___x_2173_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_2139_,
                        v___x_2170_,
                        v___x_2172_,
                    );
                    v___x_2174_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2174_, 0, v___x_2165_);
                    lean_ctor_set(v___x_2174_, 1, v___x_2167_);
                    v_sz_2175_ = lean_array_size(v___x_2173_);
                    v___x_2176_ = 0usize;
                    v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v___x_2173_, v_sz_2175_, v___x_2176_, v___x_2174_);
                    lean_dec_ref(v___x_2173_);
                    if lean_obj_tag(v___x_2177_) == 0 {
                        v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
                        v_isSharedCheck_2186_ = (!lean_is_exclusive(v___x_2177_)) as u8;
                        if v_isSharedCheck_2186_ == 0 {
                            v___x_2180_ = v___x_2177_;
                            v_isShared_2181_ = v_isSharedCheck_2186_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2178_);
                            lean_dec(v___x_2177_);
                            v___x_2180_ = lean_box(0);
                            v_isShared_2181_ = v_isSharedCheck_2186_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2187_ = lean_ctor_get(v___x_2177_, 0);
                        v_isSharedCheck_2194_ = (!lean_is_exclusive(v___x_2177_)) as u8;
                        if v_isSharedCheck_2194_ == 0 {
                            v___x_2189_ = v___x_2177_;
                            v_isShared_2190_ = v_isSharedCheck_2194_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2187_);
                            lean_dec(v___x_2177_);
                            v___x_2189_ = lean_box(0);
                            v_isShared_2190_ = v_isSharedCheck_2194_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2160_;
            }
            3 => {
                v_fst_2182_ = lean_ctor_get(v_a_2178_, 0);
                lean_inc(v_fst_2182_);
                lean_dec(v_a_2178_);
                if v_isShared_2181_ == 0 {
                    lean_ctor_set(v___x_2180_, 0, v_fst_2182_);
                    v___x_2184_ = v___x_2180_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_fst_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2184_;
            }
            5 => {
                if v_isShared_2190_ == 0 {
                    v___x_2192_ = v___x_2189_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2192_;
            }
            7 => {
                if v_isShared_2199_ == 0 {
                    v___x_2201_ = v___x_2198_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
                    v___x_2201_ = v_reuseFailAlloc_2202_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_getSimpArgs___boxed(
    mut v_e_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
    mut v_a_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ =
        l_Lean_Meta_NormCast_getSimpArgs(v_e_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
    lean_dec(v_a_2208_);
    lean_dec_ref(v_a_2207_);
    lean_dec(v_a_2206_);
    lean_dec_ref(v_a_2205_);
    return v_res_2210_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0(
    mut v_as_2211_: *mut LeanObject,
    mut v_sz_2212_: usize,
    mut v_i_2213_: usize,
    mut v_b_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
    mut v___y_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v_as_2211_, v_sz_2212_, v_i_2213_, v_b_2214_);
    return v___x_2220_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___boxed(
    mut v_as_2221_: *mut LeanObject,
    mut v_sz_2222_: *mut LeanObject,
    mut v_i_2223_: *mut LeanObject,
    mut v_b_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2230_: usize = 0;
    let mut v_i_boxed_2231_: usize = 0;
    let mut v_res_2232_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2230_ = lean_unbox_usize(v_sz_2222_);
    lean_dec(v_sz_2222_);
    v_i_boxed_2231_ = lean_unbox_usize(v_i_2223_);
    lean_dec(v_i_2223_);
    v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0(v_as_2221_, v_sz_boxed_2230_, v_i_boxed_2231_, v_b_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
    lean_dec(v___y_2228_);
    lean_dec_ref(v___y_2227_);
    lean_dec(v___y_2226_);
    lean_dec_ref(v___y_2225_);
    lean_dec_ref(v_as_2221_);
    return v_res_2232_;
}
pub unsafe fn l_Lean_Meta_NormCast_countHeadCoes___redArg(
    mut v_e_2233_: *mut LeanObject,
    mut v_a_2234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numArgs_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_coercee_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v_a_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2239_ = l_Lean_Expr_getAppFn(v_e_2233_);
                if lean_obj_tag(v___x_2239_) == 4 {
                    v_declName_2240_ = lean_ctor_get(v___x_2239_, 0);
                    lean_inc(v_declName_2240_);
                    lean_dec_ref_known(v___x_2239_, 2);
                    v___x_2241_ =
                        l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_2240_, v_a_2234_);
                    lean_dec(v_declName_2240_);
                    if lean_obj_tag(v___x_2241_) == 0 {
                        v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
                        lean_inc(v_a_2242_);
                        lean_dec_ref_known(v___x_2241_, 1);
                        if lean_obj_tag(v_a_2242_) == 1 {
                            v_val_2243_ = lean_ctor_get(v_a_2242_, 0);
                            lean_inc(v_val_2243_);
                            lean_dec_ref_known(v_a_2242_, 1);
                            v_numArgs_2244_ = lean_ctor_get(v_val_2243_, 0);
                            lean_inc(v_numArgs_2244_);
                            v_coercee_2245_ = lean_ctor_get(v_val_2243_, 1);
                            lean_inc(v_coercee_2245_);
                            lean_dec(v_val_2243_);
                            v___x_2246_ = l_Lean_Expr_getAppNumArgs(v_e_2233_);
                            v___x_2247_ = lean_nat_dec_le(v_numArgs_2244_, v___x_2246_);
                            lean_dec(v_numArgs_2244_);
                            if v___x_2247_ == 0 {
                                lean_dec(v___x_2246_);
                                lean_dec(v_coercee_2245_);
                                state = 1;
                                continue;
                            } else {
                                v___x_2248_ = lean_nat_sub(v___x_2246_, v_coercee_2245_);
                                lean_dec(v_coercee_2245_);
                                lean_dec(v___x_2246_);
                                v___x_2249_ = lean_unsigned_to_nat(1);
                                v___x_2250_ = lean_nat_sub(v___x_2248_, v___x_2249_);
                                lean_dec(v___x_2248_);
                                v___x_2251_ = l_Lean_Expr_getRevArg_x21(v_e_2233_, v___x_2250_);
                                v___x_2252_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(
                                    v___x_2251_,
                                    v_a_2234_,
                                );
                                lean_dec_ref(v___x_2251_);
                                if lean_obj_tag(v___x_2252_) == 0 {
                                    v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
                                    v_isSharedCheck_2261_ = (!lean_is_exclusive(v___x_2252_)) as u8;
                                    if v_isSharedCheck_2261_ == 0 {
                                        v___x_2255_ = v___x_2252_;
                                        v_isShared_2256_ = v_isSharedCheck_2261_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2253_);
                                        lean_dec(v___x_2252_);
                                        v___x_2255_ = lean_box(0);
                                        v_isShared_2256_ = v_isSharedCheck_2261_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    return v___x_2252_;
                                }
                            }
                        } else {
                            lean_dec(v_a_2242_);
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2262_ = lean_ctor_get(v___x_2241_, 0);
                        v_isSharedCheck_2269_ = (!lean_is_exclusive(v___x_2241_)) as u8;
                        if v_isSharedCheck_2269_ == 0 {
                            v___x_2264_ = v___x_2241_;
                            v_isShared_2265_ = v_isSharedCheck_2269_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2262_);
                            lean_dec(v___x_2241_);
                            v___x_2264_ = lean_box(0);
                            v_isShared_2265_ = v_isSharedCheck_2269_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2239_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2237_ = lean_unsigned_to_nat(0);
                v___x_2238_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2238_, 0, v___x_2237_);
                return v___x_2238_;
            }
            2 => {
                v___x_2257_ = lean_nat_add(v_a_2253_, v___x_2249_);
                lean_dec(v_a_2253_);
                if v_isShared_2256_ == 0 {
                    lean_ctor_set(v___x_2255_, 0, v___x_2257_);
                    v___x_2259_ = v___x_2255_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
                    v___x_2259_ = v_reuseFailAlloc_2260_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2259_;
            }
            4 => {
                if v_isShared_2265_ == 0 {
                    v___x_2267_ = v___x_2264_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
                    v___x_2267_ = v_reuseFailAlloc_2268_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_countHeadCoes___redArg___boxed(
    mut v_e_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2273_: *mut LeanObject = core::ptr::null_mut();
    v_res_2273_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_2270_, v_a_2271_);
    lean_dec(v_a_2271_);
    lean_dec_ref(v_e_2270_);
    return v_res_2273_;
}
pub unsafe fn l_Lean_Meta_NormCast_countHeadCoes(
    mut v_e_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_a_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    v___x_2280_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_2274_, v_a_2278_);
    return v___x_2280_;
}
pub unsafe fn l_Lean_Meta_NormCast_countHeadCoes___boxed(
    mut v_e_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2287_: *mut LeanObject = core::ptr::null_mut();
    v_res_2287_ =
        l_Lean_Meta_NormCast_countHeadCoes(v_e_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
    lean_dec(v_a_2285_);
    lean_dec_ref(v_a_2284_);
    lean_dec(v_a_2283_);
    lean_dec_ref(v_a_2282_);
    lean_dec_ref(v_e_2281_);
    return v_res_2287_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0(
    mut v_k_2288_: *mut LeanObject,
    mut v_b_2289_: *mut LeanObject,
    mut v_c_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
    mut v___y_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2294_);
    lean_inc_ref(v___y_2293_);
    lean_inc(v___y_2292_);
    lean_inc_ref(v___y_2291_);
    v___x_2296_ = lean_apply_7(
        v_k_2288_,
        v_b_2289_,
        v_c_2290_,
        v___y_2291_,
        v___y_2292_,
        v___y_2293_,
        v___y_2294_,
        lean_box(0),
    );
    return v___x_2296_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed(
    mut v_k_2297_: *mut LeanObject,
    mut v_b_2298_: *mut LeanObject,
    mut v_c_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2305_: *mut LeanObject = core::ptr::null_mut();
    v_res_2305_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0(
            v_k_2297_,
            v_b_2298_,
            v_c_2299_,
            v___y_2300_,
            v___y_2301_,
            v___y_2302_,
            v___y_2303_,
        );
    lean_dec(v___y_2303_);
    lean_dec_ref(v___y_2302_);
    lean_dec(v___y_2301_);
    lean_dec_ref(v___y_2300_);
    return v_res_2305_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(
    mut v_e_2306_: *mut LeanObject,
    mut v_k_2307_: *mut LeanObject,
    mut v_cleanupAnnotations_2308_: u8,
    mut v___y_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: u8 = 0;
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2326_: u8 = 0;
    let mut v_a_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2330_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2314_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2314_, 0, v_k_2307_);
                v___x_2315_ = 1;
                v___x_2316_ = 0;
                v___x_2317_ = lean_box(0);
                v___x_2318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
                    v_e_2306_,
                    v___x_2315_,
                    v___x_2316_,
                    v___x_2315_,
                    v___x_2316_,
                    v___x_2317_,
                    v___f_2314_,
                    v_cleanupAnnotations_2308_,
                    v___y_2309_,
                    v___y_2310_,
                    v___y_2311_,
                    v___y_2312_,
                );
                if lean_obj_tag(v___x_2318_) == 0 {
                    v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2326_ = (!lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2326_ == 0 {
                        v___x_2321_ = v___x_2318_;
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2319_);
                        lean_dec(v___x_2318_);
                        v___x_2321_ = lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2327_ = lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2334_ = (!lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2334_ == 0 {
                        v___x_2329_ = v___x_2318_;
                        v_isShared_2330_ = v_isSharedCheck_2334_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2327_);
                        lean_dec(v___x_2318_);
                        v___x_2329_ = lean_box(0);
                        v_isShared_2330_ = v_isSharedCheck_2334_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2322_ == 0 {
                    v___x_2324_ = v___x_2321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
                    v___x_2324_ = v_reuseFailAlloc_2325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2324_;
            }
            3 => {
                if v_isShared_2330_ == 0 {
                    v___x_2332_ = v___x_2329_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
                    v___x_2332_ = v_reuseFailAlloc_2333_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___boxed(
    mut v_e_2335_: *mut LeanObject,
    mut v_k_2336_: *mut LeanObject,
    mut v_cleanupAnnotations_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2343_: u8 = 0;
    let mut v_res_2344_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2343_ = (lean_unbox(v_cleanupAnnotations_2337_) as u8);
    v_res_2344_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(
            v_e_2335_,
            v_k_2336_,
            v_cleanupAnnotations_boxed_2343_,
            v___y_2338_,
            v___y_2339_,
            v___y_2340_,
            v___y_2341_,
        );
    lean_dec(v___y_2341_);
    lean_dec_ref(v___y_2340_);
    lean_dec(v___y_2339_);
    lean_dec_ref(v___y_2338_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3(
    mut v_00_u03b1_2345_: *mut LeanObject,
    mut v_e_2346_: *mut LeanObject,
    mut v_k_2347_: *mut LeanObject,
    mut v_cleanupAnnotations_2348_: u8,
    mut v___y_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    v___x_2354_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(
            v_e_2346_,
            v_k_2347_,
            v_cleanupAnnotations_2348_,
            v___y_2349_,
            v___y_2350_,
            v___y_2351_,
            v___y_2352_,
        );
    return v___x_2354_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___boxed(
    mut v_00_u03b1_2355_: *mut LeanObject,
    mut v_e_2356_: *mut LeanObject,
    mut v_k_2357_: *mut LeanObject,
    mut v_cleanupAnnotations_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2364_: u8 = 0;
    let mut v_res_2365_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2364_ = (lean_unbox(v_cleanupAnnotations_2358_) as u8);
    v_res_2365_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3(
        v_00_u03b1_2355_,
        v_e_2356_,
        v_k_2357_,
        v_cleanupAnnotations_boxed_2364_,
        v___y_2359_,
        v___y_2360_,
        v___y_2361_,
        v___y_2362_,
    );
    lean_dec(v___y_2362_);
    lean_dec_ref(v___y_2361_);
    lean_dec(v___y_2360_);
    lean_dec_ref(v___y_2359_);
    return v_res_2365_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(
    mut v_as_2366_: *mut LeanObject,
    mut v_i_2367_: usize,
    mut v_stop_2368_: usize,
    mut v_b_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2370_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: usize = 0;
    let mut v___x_2374_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2370_ = lean_usize_dec_eq(v_i_2367_, v_stop_2368_);
                if v___x_2370_ == 0 {
                    v___x_2371_ = lean_array_uget_borrowed(v_as_2366_, v_i_2367_);
                    v___x_2372_ = lean_nat_add(v_b_2369_, v___x_2371_);
                    lean_dec(v_b_2369_);
                    v___x_2373_ = 1usize;
                    v___x_2374_ = lean_usize_add(v_i_2367_, v___x_2373_);
                    v_i_2367_ = v___x_2374_;
                    v_b_2369_ = v___x_2372_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2369_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1___boxed(
    mut v_as_2376_: *mut LeanObject,
    mut v_i_2377_: *mut LeanObject,
    mut v_stop_2378_: *mut LeanObject,
    mut v_b_2379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2380_: usize = 0;
    let mut v_stop_boxed_2381_: usize = 0;
    let mut v_res_2382_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2380_ = lean_unbox_usize(v_i_2377_);
    lean_dec(v_i_2377_);
    v_stop_boxed_2381_ = lean_unbox_usize(v_stop_2378_);
    lean_dec(v_stop_2378_);
    v_res_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_as_2376_, v_i_boxed_2380_, v_stop_boxed_2381_, v_b_2379_);
    lean_dec_ref(v_as_2376_);
    return v_res_2382_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(
    mut v_sz_2383_: usize,
    mut v_i_2384_: usize,
    mut v_bs_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: usize = 0;
    let mut v___x_2399_: usize = 0;
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2391_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
                if v___x_2391_ == 0 {
                    v___x_2392_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2392_, 0, v_bs_2385_);
                    return v___x_2392_;
                } else {
                    v_v_2393_ = lean_array_uget_borrowed(v_bs_2385_, v_i_2384_);
                    lean_inc(v_v_2393_);
                    v___x_2394_ = l_Lean_Meta_NormCast_countCoes(
                        v_v_2393_,
                        v___y_2386_,
                        v___y_2387_,
                        v___y_2388_,
                        v___y_2389_,
                    );
                    if lean_obj_tag(v___x_2394_) == 0 {
                        v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
                        lean_inc(v_a_2395_);
                        lean_dec_ref_known(v___x_2394_, 1);
                        v___x_2396_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2397_ = lean_array_uset(v_bs_2385_, v_i_2384_, v___x_2396_);
                        v___x_2398_ = 1usize;
                        v___x_2399_ = lean_usize_add(v_i_2384_, v___x_2398_);
                        v___x_2400_ = lean_array_uset(v_bs_x27_2397_, v_i_2384_, v_a_2395_);
                        v_i_2384_ = v___x_2399_;
                        v_bs_2385_ = v___x_2400_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2385_);
                        v_a_2402_ = lean_ctor_get(v___x_2394_, 0);
                        v_isSharedCheck_2409_ = (!lean_is_exclusive(v___x_2394_)) as u8;
                        if v_isSharedCheck_2409_ == 0 {
                            v___x_2404_ = v___x_2394_;
                            v_isShared_2405_ = v_isSharedCheck_2409_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2402_);
                            lean_dec(v___x_2394_);
                            v___x_2404_ = lean_box(0);
                            v_isShared_2405_ = v_isSharedCheck_2409_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2405_ == 0 {
                    v___x_2407_ = v___x_2404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
                    v___x_2407_ = v_reuseFailAlloc_2408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2407_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(
    mut v_upperBound_2410_: *mut LeanObject,
    mut v___x_2411_: *mut LeanObject,
    mut v_e_2412_: *mut LeanObject,
    mut v_a_2413_: *mut LeanObject,
    mut v_b_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2420_ = lean_nat_dec_lt(v_a_2413_, v_upperBound_2410_);
                if v___x_2420_ == 0 {
                    lean_dec(v_a_2413_);
                    v___x_2421_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2421_, 0, v_b_2414_);
                    return v___x_2421_;
                } else {
                    v___x_2422_ = lean_nat_sub(v___x_2411_, v_a_2413_);
                    v___x_2423_ = lean_unsigned_to_nat(1);
                    v___x_2424_ = lean_nat_sub(v___x_2422_, v___x_2423_);
                    lean_dec(v___x_2422_);
                    v___x_2425_ = l_Lean_Expr_getRevArg_x21(v_e_2412_, v___x_2424_);
                    v___x_2426_ = l_Lean_Meta_NormCast_countCoes(
                        v___x_2425_,
                        v___y_2415_,
                        v___y_2416_,
                        v___y_2417_,
                        v___y_2418_,
                    );
                    if lean_obj_tag(v___x_2426_) == 0 {
                        v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
                        lean_inc(v_a_2427_);
                        lean_dec_ref_known(v___x_2426_, 1);
                        v___x_2428_ = lean_nat_add(v_b_2414_, v_a_2427_);
                        lean_dec(v_a_2427_);
                        lean_dec(v_b_2414_);
                        v___x_2429_ = lean_nat_add(v_a_2413_, v___x_2423_);
                        lean_dec(v_a_2413_);
                        v_a_2413_ = v___x_2429_;
                        v_b_2414_ = v___x_2428_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_b_2414_);
                        lean_dec(v_a_2413_);
                        return v___x_2426_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_countCoes___lam__0(
    mut v_x_2431_: *mut LeanObject,
    mut v_e_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
    mut v___y_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2441_: usize = 0;
    let mut v___x_2442_: usize = 0;
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: usize = 0;
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: usize = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut v_a_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2472_: u8 = 0;
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v_a_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numArgs_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_coercee_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: u8 = 0;
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2485_ = l_Lean_Expr_getAppFn(v_e_2432_);
                if lean_obj_tag(v___x_2485_) == 4 {
                    v_declName_2486_ = lean_ctor_get(v___x_2485_, 0);
                    lean_inc(v_declName_2486_);
                    lean_dec_ref_known(v___x_2485_, 2);
                    v___x_2487_ =
                        l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_2486_, v___y_2436_);
                    lean_dec(v_declName_2486_);
                    if lean_obj_tag(v___x_2487_) == 0 {
                        v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
                        lean_inc(v_a_2488_);
                        lean_dec_ref_known(v___x_2487_, 1);
                        if lean_obj_tag(v_a_2488_) == 1 {
                            v_val_2489_ = lean_ctor_get(v_a_2488_, 0);
                            lean_inc(v_val_2489_);
                            lean_dec_ref_known(v_a_2488_, 1);
                            v_numArgs_2490_ = lean_ctor_get(v_val_2489_, 0);
                            lean_inc(v_numArgs_2490_);
                            v_coercee_2491_ = lean_ctor_get(v_val_2489_, 1);
                            lean_inc(v_coercee_2491_);
                            lean_dec(v_val_2489_);
                            v___x_2492_ = l_Lean_Expr_getAppNumArgs(v_e_2432_);
                            v___x_2493_ = lean_nat_dec_le(v_numArgs_2490_, v___x_2492_);
                            if v___x_2493_ == 0 {
                                lean_dec(v___x_2492_);
                                lean_dec(v_coercee_2491_);
                                lean_dec(v_numArgs_2490_);
                                state = 1;
                                continue;
                            } else {
                                v___x_2494_ = lean_nat_sub(v___x_2492_, v_coercee_2491_);
                                lean_dec(v_coercee_2491_);
                                v___x_2495_ = lean_unsigned_to_nat(1);
                                v___x_2496_ = lean_nat_sub(v___x_2494_, v___x_2495_);
                                lean_dec(v___x_2494_);
                                v___x_2497_ = l_Lean_Expr_getRevArg_x21(v_e_2432_, v___x_2496_);
                                v___x_2498_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(
                                    v___x_2497_,
                                    v___y_2436_,
                                );
                                lean_dec_ref(v___x_2497_);
                                if lean_obj_tag(v___x_2498_) == 0 {
                                    v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
                                    lean_inc(v_a_2499_);
                                    lean_dec_ref_known(v___x_2498_, 1);
                                    v___x_2500_ = lean_nat_add(v_a_2499_, v___x_2495_);
                                    lean_dec(v_a_2499_);
                                    v___x_2501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v___x_2492_, v___x_2492_, v_e_2432_, v_numArgs_2490_, v___x_2500_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
                                    lean_dec_ref(v_e_2432_);
                                    lean_dec(v___x_2492_);
                                    return v___x_2501_;
                                } else {
                                    lean_dec(v___x_2492_);
                                    lean_dec(v_numArgs_2490_);
                                    lean_dec_ref(v_e_2432_);
                                    return v___x_2498_;
                                }
                            }
                        } else {
                            lean_dec(v_a_2488_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_2432_);
                        v_a_2502_ = lean_ctor_get(v___x_2487_, 0);
                        v_isSharedCheck_2509_ = (!lean_is_exclusive(v___x_2487_)) as u8;
                        if v_isSharedCheck_2509_ == 0 {
                            v___x_2504_ = v___x_2487_;
                            v_isShared_2505_ = v_isSharedCheck_2509_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2502_);
                            lean_dec(v___x_2487_);
                            v___x_2504_ = lean_box(0);
                            v_isShared_2505_ = v_isSharedCheck_2509_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2485_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2439_ = l_Lean_Meta_NormCast_getSimpArgs(
                    v_e_2432_,
                    v___y_2433_,
                    v___y_2434_,
                    v___y_2435_,
                    v___y_2436_,
                );
                if lean_obj_tag(v___x_2439_) == 0 {
                    v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
                    lean_inc(v_a_2440_);
                    lean_dec_ref_known(v___x_2439_, 1);
                    v_sz_2441_ = lean_array_size(v_a_2440_);
                    v___x_2442_ = 0usize;
                    v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(v_sz_2441_, v___x_2442_, v_a_2440_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
                    if lean_obj_tag(v___x_2443_) == 0 {
                        v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
                        v_isSharedCheck_2468_ = (!lean_is_exclusive(v___x_2443_)) as u8;
                        if v_isSharedCheck_2468_ == 0 {
                            v___x_2446_ = v___x_2443_;
                            v_isShared_2447_ = v_isSharedCheck_2468_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2444_);
                            lean_dec(v___x_2443_);
                            v___x_2446_ = lean_box(0);
                            v_isShared_2447_ = v_isSharedCheck_2468_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2469_ = lean_ctor_get(v___x_2443_, 0);
                        v_isSharedCheck_2476_ = (!lean_is_exclusive(v___x_2443_)) as u8;
                        if v_isSharedCheck_2476_ == 0 {
                            v___x_2471_ = v___x_2443_;
                            v_isShared_2472_ = v_isSharedCheck_2476_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2469_);
                            lean_dec(v___x_2443_);
                            v___x_2471_ = lean_box(0);
                            v_isShared_2472_ = v_isSharedCheck_2476_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_2477_ = lean_ctor_get(v___x_2439_, 0);
                    v_isSharedCheck_2484_ = (!lean_is_exclusive(v___x_2439_)) as u8;
                    if v_isSharedCheck_2484_ == 0 {
                        v___x_2479_ = v___x_2439_;
                        v_isShared_2480_ = v_isSharedCheck_2484_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2477_);
                        lean_dec(v___x_2439_);
                        v___x_2479_ = lean_box(0);
                        v_isShared_2480_ = v_isSharedCheck_2484_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2448_ = lean_unsigned_to_nat(0);
                v___x_2449_ = lean_array_get_size(v_a_2444_);
                v___x_2450_ = lean_nat_dec_lt(v___x_2448_, v___x_2449_);
                if v___x_2450_ == 0 {
                    lean_dec(v_a_2444_);
                    if v_isShared_2447_ == 0 {
                        lean_ctor_set(v___x_2446_, 0, v___x_2448_);
                        v___x_2452_ = v___x_2446_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2448_);
                        v___x_2452_ = v_reuseFailAlloc_2453_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2454_ = lean_nat_dec_le(v___x_2449_, v___x_2449_);
                    if v___x_2454_ == 0 {
                        if v___x_2450_ == 0 {
                            lean_dec(v_a_2444_);
                            if v_isShared_2447_ == 0 {
                                lean_ctor_set(v___x_2446_, 0, v___x_2448_);
                                v___x_2456_ = v___x_2446_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2448_);
                                v___x_2456_ = v_reuseFailAlloc_2457_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_2458_ = lean_usize_of_nat(v___x_2449_);
                            v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_a_2444_, v___x_2442_, v___x_2458_, v___x_2448_);
                            lean_dec(v_a_2444_);
                            if v_isShared_2447_ == 0 {
                                lean_ctor_set(v___x_2446_, 0, v___x_2459_);
                                v___x_2461_ = v___x_2446_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
                                v___x_2461_ = v_reuseFailAlloc_2462_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_2463_ = lean_usize_of_nat(v___x_2449_);
                        v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_a_2444_, v___x_2442_, v___x_2463_, v___x_2448_);
                        lean_dec(v_a_2444_);
                        if v_isShared_2447_ == 0 {
                            lean_ctor_set(v___x_2446_, 0, v___x_2464_);
                            v___x_2466_ = v___x_2446_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
                            v___x_2466_ = v_reuseFailAlloc_2467_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_2452_;
            }
            4 => {
                return v___x_2456_;
            }
            5 => {
                return v___x_2461_;
            }
            6 => {
                return v___x_2466_;
            }
            7 => {
                if v_isShared_2472_ == 0 {
                    v___x_2474_ = v___x_2471_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
                    v___x_2474_ = v_reuseFailAlloc_2475_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2474_;
            }
            9 => {
                if v_isShared_2480_ == 0 {
                    v___x_2482_ = v___x_2479_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
                    v___x_2482_ = v_reuseFailAlloc_2483_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2482_;
            }
            11 => {
                if v_isShared_2505_ == 0 {
                    v___x_2507_ = v___x_2504_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
                    v___x_2507_ = v_reuseFailAlloc_2508_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_countCoes___lam__0___boxed(
    mut v_x_2510_: *mut LeanObject,
    mut v_e_2511_: *mut LeanObject,
    mut v___y_2512_: *mut LeanObject,
    mut v___y_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
    mut v___y_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2517_: *mut LeanObject = core::ptr::null_mut();
    v_res_2517_ = l_Lean_Meta_NormCast_countCoes___lam__0(
        v_x_2510_,
        v_e_2511_,
        v___y_2512_,
        v___y_2513_,
        v___y_2514_,
        v___y_2515_,
    );
    lean_dec(v___y_2515_);
    lean_dec_ref(v___y_2514_);
    lean_dec(v___y_2513_);
    lean_dec_ref(v___y_2512_);
    lean_dec_ref(v_x_2510_);
    return v_res_2517_;
}
pub unsafe fn l_Lean_Meta_NormCast_countCoes(
    mut v_e_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v_a_2520_: *mut LeanObject,
    mut v_a_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u8 = 0;
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    v___f_2524_ = lean_alloc_closure(
        l_Lean_Meta_NormCast_countCoes___lam__0___boxed as *mut core::ffi::c_void,
        7,
        0,
    );
    v___x_2525_ = 0;
    v___x_2526_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(
            v_e_2518_,
            v___f_2524_,
            v___x_2525_,
            v_a_2519_,
            v_a_2520_,
            v_a_2521_,
            v_a_2522_,
        );
    return v___x_2526_;
}
pub unsafe fn l_Lean_Meta_NormCast_countCoes___boxed(
    mut v_e_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
    mut v_a_2529_: *mut LeanObject,
    mut v_a_2530_: *mut LeanObject,
    mut v_a_2531_: *mut LeanObject,
    mut v_a_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2533_: *mut LeanObject = core::ptr::null_mut();
    v_res_2533_ =
        l_Lean_Meta_NormCast_countCoes(v_e_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
    lean_dec(v_a_2531_);
    lean_dec_ref(v_a_2530_);
    lean_dec(v_a_2529_);
    lean_dec_ref(v_a_2528_);
    return v_res_2533_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg___boxed(
    mut v_upperBound_2534_: *mut LeanObject,
    mut v___x_2535_: *mut LeanObject,
    mut v_e_2536_: *mut LeanObject,
    mut v_a_2537_: *mut LeanObject,
    mut v_b_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
    mut v___y_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2544_: *mut LeanObject = core::ptr::null_mut();
    v_res_2544_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(
            v_upperBound_2534_,
            v___x_2535_,
            v_e_2536_,
            v_a_2537_,
            v_b_2538_,
            v___y_2539_,
            v___y_2540_,
            v___y_2541_,
            v___y_2542_,
        );
    lean_dec(v___y_2542_);
    lean_dec_ref(v___y_2541_);
    lean_dec(v___y_2540_);
    lean_dec_ref(v___y_2539_);
    lean_dec_ref(v_e_2536_);
    lean_dec(v___x_2535_);
    lean_dec(v_upperBound_2534_);
    return v_res_2544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0___boxed(
    mut v_sz_2545_: *mut LeanObject,
    mut v_i_2546_: *mut LeanObject,
    mut v_bs_2547_: *mut LeanObject,
    mut v___y_2548_: *mut LeanObject,
    mut v___y_2549_: *mut LeanObject,
    mut v___y_2550_: *mut LeanObject,
    mut v___y_2551_: *mut LeanObject,
    mut v___y_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2553_: usize = 0;
    let mut v_i_boxed_2554_: usize = 0;
    let mut v_res_2555_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2553_ = lean_unbox_usize(v_sz_2545_);
    lean_dec(v_sz_2545_);
    v_i_boxed_2554_ = lean_unbox_usize(v_i_2546_);
    lean_dec(v_i_2546_);
    v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(v_sz_boxed_2553_, v_i_boxed_2554_, v_bs_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
    lean_dec(v___y_2551_);
    lean_dec_ref(v___y_2550_);
    lean_dec(v___y_2549_);
    lean_dec_ref(v___y_2548_);
    return v_res_2555_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(
    mut v_upperBound_2556_: *mut LeanObject,
    mut v___x_2557_: *mut LeanObject,
    mut v_e_2558_: *mut LeanObject,
    mut v_inst_2559_: *mut LeanObject,
    mut v_R_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
    mut v_b_2562_: *mut LeanObject,
    mut v_c_2563_: *mut LeanObject,
    mut v___y_2564_: *mut LeanObject,
    mut v___y_2565_: *mut LeanObject,
    mut v___y_2566_: *mut LeanObject,
    mut v___y_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    v___x_2569_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(
            v_upperBound_2556_,
            v___x_2557_,
            v_e_2558_,
            v_a_2561_,
            v_b_2562_,
            v___y_2564_,
            v___y_2565_,
            v___y_2566_,
            v___y_2567_,
        );
    return v___x_2569_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___boxed(
    mut v_upperBound_2570_: *mut LeanObject,
    mut v___x_2571_: *mut LeanObject,
    mut v_e_2572_: *mut LeanObject,
    mut v_inst_2573_: *mut LeanObject,
    mut v_R_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
    mut v_b_2576_: *mut LeanObject,
    mut v_c_2577_: *mut LeanObject,
    mut v___y_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
    mut v___y_2581_: *mut LeanObject,
    mut v___y_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2583_: *mut LeanObject = core::ptr::null_mut();
    v_res_2583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(
        v_upperBound_2570_,
        v___x_2571_,
        v_e_2572_,
        v_inst_2573_,
        v_R_2574_,
        v_a_2575_,
        v_b_2576_,
        v_c_2577_,
        v___y_2578_,
        v___y_2579_,
        v___y_2580_,
        v___y_2581_,
    );
    lean_dec(v___y_2581_);
    lean_dec_ref(v___y_2580_);
    lean_dec(v___y_2579_);
    lean_dec_ref(v___y_2578_);
    lean_dec_ref(v_e_2572_);
    lean_dec(v___x_2571_);
    lean_dec(v_upperBound_2570_);
    return v_res_2583_;
}
pub unsafe fn l_Lean_Meta_NormCast_countInternalCoes(
    mut v_e_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
    mut v_a_2586_: *mut LeanObject,
    mut v_a_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2584_);
                v___x_2590_ = l_Lean_Meta_NormCast_countCoes(
                    v_e_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_,
                );
                if lean_obj_tag(v___x_2590_) == 0 {
                    v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
                    lean_inc(v_a_2591_);
                    lean_dec_ref_known(v___x_2590_, 1);
                    v___x_2592_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_2584_, v_a_2588_);
                    lean_dec_ref(v_e_2584_);
                    if lean_obj_tag(v___x_2592_) == 0 {
                        v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
                        v_isSharedCheck_2601_ = (!lean_is_exclusive(v___x_2592_)) as u8;
                        if v_isSharedCheck_2601_ == 0 {
                            v___x_2595_ = v___x_2592_;
                            v_isShared_2596_ = v_isSharedCheck_2601_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2593_);
                            lean_dec(v___x_2592_);
                            v___x_2595_ = lean_box(0);
                            v_isShared_2596_ = v_isSharedCheck_2601_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2591_);
                        return v___x_2592_;
                    }
                } else {
                    lean_dec_ref(v_e_2584_);
                    return v___x_2590_;
                }
            }
            1 => {
                v___x_2597_ = lean_nat_sub(v_a_2591_, v_a_2593_);
                lean_dec(v_a_2593_);
                lean_dec(v_a_2591_);
                if v_isShared_2596_ == 0 {
                    lean_ctor_set(v___x_2595_, 0, v___x_2597_);
                    v___x_2599_ = v___x_2595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
                    v___x_2599_ = v_reuseFailAlloc_2600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_countInternalCoes___boxed(
    mut v_e_2602_: *mut LeanObject,
    mut v_a_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2608_: *mut LeanObject = core::ptr::null_mut();
    v_res_2608_ = l_Lean_Meta_NormCast_countInternalCoes(
        v_e_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_,
    );
    lean_dec(v_a_2606_);
    lean_dec_ref(v_a_2605_);
    lean_dec(v_a_2604_);
    lean_dec_ref(v_a_2603_);
    return v_res_2608_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(
    mut v_type_2609_: *mut LeanObject,
    mut v_k_2610_: *mut LeanObject,
    mut v_cleanupAnnotations_2611_: u8,
    mut v_whnfType_2612_: u8,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v_a_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2618_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2618_, 0, v_k_2610_);
                v___x_2619_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_2609_,
                    v___f_2618_,
                    v_cleanupAnnotations_2611_,
                    v_whnfType_2612_,
                    v___y_2613_,
                    v___y_2614_,
                    v___y_2615_,
                    v___y_2616_,
                );
                if lean_obj_tag(v___x_2619_) == 0 {
                    v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
                    v_isSharedCheck_2627_ = (!lean_is_exclusive(v___x_2619_)) as u8;
                    if v_isSharedCheck_2627_ == 0 {
                        v___x_2622_ = v___x_2619_;
                        v_isShared_2623_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2620_);
                        lean_dec(v___x_2619_);
                        v___x_2622_ = lean_box(0);
                        v_isShared_2623_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2628_ = lean_ctor_get(v___x_2619_, 0);
                    v_isSharedCheck_2635_ = (!lean_is_exclusive(v___x_2619_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2630_ = v___x_2619_;
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2628_);
                        lean_dec(v___x_2619_);
                        v___x_2630_ = lean_box(0);
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2623_ == 0 {
                    v___x_2625_ = v___x_2622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
                    v___x_2625_ = v_reuseFailAlloc_2626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2625_;
            }
            3 => {
                if v_isShared_2631_ == 0 {
                    v___x_2633_ = v___x_2630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
                    v___x_2633_ = v_reuseFailAlloc_2634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg___boxed(
    mut v_type_2636_: *mut LeanObject,
    mut v_k_2637_: *mut LeanObject,
    mut v_cleanupAnnotations_2638_: *mut LeanObject,
    mut v_whnfType_2639_: *mut LeanObject,
    mut v___y_2640_: *mut LeanObject,
    mut v___y_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
    mut v___y_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2645_: u8 = 0;
    let mut v_whnfType_boxed_2646_: u8 = 0;
    let mut v_res_2647_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2645_ = (lean_unbox(v_cleanupAnnotations_2638_) as u8);
    v_whnfType_boxed_2646_ = (lean_unbox(v_whnfType_2639_) as u8);
    v_res_2647_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_2636_, v_k_2637_, v_cleanupAnnotations_boxed_2645_, v_whnfType_boxed_2646_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
    lean_dec(v___y_2643_);
    lean_dec_ref(v___y_2642_);
    lean_dec(v___y_2641_);
    lean_dec_ref(v___y_2640_);
    return v_res_2647_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(
    mut v_00_u03b1_2648_: *mut LeanObject,
    mut v_type_2649_: *mut LeanObject,
    mut v_k_2650_: *mut LeanObject,
    mut v_cleanupAnnotations_2651_: u8,
    mut v_whnfType_2652_: u8,
    mut v___y_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_2649_, v_k_2650_, v_cleanupAnnotations_2651_, v_whnfType_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___boxed(
    mut v_00_u03b1_2659_: *mut LeanObject,
    mut v_type_2660_: *mut LeanObject,
    mut v_k_2661_: *mut LeanObject,
    mut v_cleanupAnnotations_2662_: *mut LeanObject,
    mut v_whnfType_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
    mut v___y_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2669_: u8 = 0;
    let mut v_whnfType_boxed_2670_: u8 = 0;
    let mut v_res_2671_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2669_ = (lean_unbox(v_cleanupAnnotations_2662_) as u8);
    v_whnfType_boxed_2670_ = (lean_unbox(v_whnfType_2663_) as u8);
    v_res_2671_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(
            v_00_u03b1_2659_,
            v_type_2660_,
            v_k_2661_,
            v_cleanupAnnotations_boxed_2669_,
            v_whnfType_boxed_2670_,
            v___y_2664_,
            v___y_2665_,
            v___y_2666_,
            v___y_2667_,
        );
    lean_dec(v___y_2667_);
    lean_dec_ref(v___y_2666_);
    lean_dec(v___y_2665_);
    lean_dec_ref(v___y_2664_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(
    mut v_msgData_2672_: *mut LeanObject,
    mut v___y_2673_: *mut LeanObject,
    mut v___y_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    v___x_2678_ = lean_st_ref_get(v___y_2676_);
    v_env_2679_ = lean_ctor_get(v___x_2678_, 0);
    lean_inc_ref(v_env_2679_);
    lean_dec(v___x_2678_);
    v___x_2680_ = lean_st_ref_get(v___y_2674_);
    v_mctx_2681_ = lean_ctor_get(v___x_2680_, 0);
    lean_inc_ref(v_mctx_2681_);
    lean_dec(v___x_2680_);
    v_lctx_2682_ = lean_ctor_get(v___y_2673_, 2);
    v_options_2683_ = lean_ctor_get(v___y_2675_, 2);
    lean_inc_ref(v_options_2683_);
    lean_inc_ref(v_lctx_2682_);
    v___x_2684_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2684_, 0, v_env_2679_);
    lean_ctor_set(v___x_2684_, 1, v_mctx_2681_);
    lean_ctor_set(v___x_2684_, 2, v_lctx_2682_);
    lean_ctor_set(v___x_2684_, 3, v_options_2683_);
    v___x_2685_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2685_, 0, v___x_2684_);
    lean_ctor_set(v___x_2685_, 1, v_msgData_2672_);
    v___x_2686_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2686_, 0, v___x_2685_);
    return v___x_2686_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0___boxed(
    mut v_msgData_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2693_: *mut LeanObject = core::ptr::null_mut();
    v_res_2693_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msgData_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
    lean_dec(v___y_2691_);
    lean_dec_ref(v___y_2690_);
    lean_dec(v___y_2689_);
    lean_dec_ref(v___y_2688_);
    return v_res_2693_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(
    mut v_msg_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2700_ = lean_ctor_get(v___y_2697_, 5);
                v___x_2701_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
                v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
                v_isSharedCheck_2710_ = (!lean_is_exclusive(v___x_2701_)) as u8;
                if v_isSharedCheck_2710_ == 0 {
                    v___x_2704_ = v___x_2701_;
                    v_isShared_2705_ = v_isSharedCheck_2710_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2702_);
                    lean_dec(v___x_2701_);
                    v___x_2704_ = lean_box(0);
                    v_isShared_2705_ = v_isSharedCheck_2710_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2700_);
                v___x_2706_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2706_, 0, v_ref_2700_);
                lean_ctor_set(v___x_2706_, 1, v_a_2702_);
                if v_isShared_2705_ == 0 {
                    lean_ctor_set_tag(v___x_2704_, 1);
                    lean_ctor_set(v___x_2704_, 0, v___x_2706_);
                    v___x_2708_ = v___x_2704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
                    v___x_2708_ = v_reuseFailAlloc_2709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg___boxed(
    mut v_msg_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
    mut v___y_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2717_: *mut LeanObject = core::ptr::null_mut();
    v_res_2717_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(
        v_msg_2711_,
        v___y_2712_,
        v___y_2713_,
        v___y_2714_,
        v___y_2715_,
    );
    lean_dec(v___y_2715_);
    lean_dec_ref(v___y_2714_);
    lean_dec(v___y_2713_);
    lean_dec_ref(v___y_2712_);
    return v_res_2717_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    v___x_2719_ = l_Lean_Meta_NormCast_classifyType___lam__0___closed__0;
    v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
    return v___x_2720_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    v___x_2722_ = l_Lean_Meta_NormCast_classifyType___lam__0___closed__2;
    v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
    return v___x_2723_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    v___x_2725_ = l_Lean_Meta_NormCast_classifyType___lam__0___closed__4;
    v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
    return v___x_2726_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    v___x_2727_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_NormCast_classifyType___lam__0___closed__5_once),
        _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5,
    );
    v___x_2728_ = l_Lean_MessageData_note(v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_Meta_NormCast_classifyType___lam__0___closed__7;
    v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
    return v___x_2731_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14() -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    v___x_2739_ = l_Lean_Meta_NormCast_classifyType___lam__0___closed__13;
    v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
    return v___x_2740_;
}
pub unsafe fn l_Lean_Meta_NormCast_classifyType___lam__0(
    mut v_x_2741_: *mut LeanObject,
    mut v_ty_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
    mut v___y_2745_: *mut LeanObject,
    mut v___y_2746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2811_: u8 = 0;
    let mut v_a_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut v_a_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2823_: u8 = 0;
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2827_: u8 = 0;
    let mut v_a_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_fst_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: u8 = 0;
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2746_);
                lean_inc_ref(v___y_2745_);
                lean_inc(v___y_2744_);
                lean_inc_ref(v___y_2743_);
                v___x_2758_ = lean_whnf(
                    v_ty_2742_,
                    v___y_2743_,
                    v___y_2744_,
                    v___y_2745_,
                    v___y_2746_,
                );
                if lean_obj_tag(v___x_2758_) == 0 {
                    v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
                    lean_inc(v_a_2759_);
                    lean_dec_ref_known(v___x_2758_, 1);
                    v___x_2869_ = l_Lean_Meta_NormCast_classifyType___lam__0___closed__10;
                    v___x_2870_ = lean_unsigned_to_nat(3);
                    v___x_2871_ = l_Lean_Expr_isAppOfArity(v_a_2759_, v___x_2869_, v___x_2870_);
                    if v___x_2871_ == 0 {
                        v___x_2872_ = l_Lean_Meta_NormCast_classifyType___lam__0___closed__12;
                        v___x_2873_ = lean_unsigned_to_nat(2);
                        v___x_2874_ = l_Lean_Expr_isAppOfArity(v_a_2759_, v___x_2872_, v___x_2873_);
                        if v___x_2874_ == 0 {
                            v___x_2875_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_NormCast_classifyType___lam__0___closed__14
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_NormCast_classifyType___lam__0___closed__14_once
                                ),
                                _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14,
                            );
                            v___x_2876_ = l_Lean_indentExpr(v_a_2759_);
                            v___x_2877_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2877_, 0, v___x_2875_);
                            lean_ctor_set(v___x_2877_, 1, v___x_2876_);
                            v___x_2878_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_2877_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
                            v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
                            v_isSharedCheck_2886_ = (!lean_is_exclusive(v___x_2878_)) as u8;
                            if v_isSharedCheck_2886_ == 0 {
                                v___x_2881_ = v___x_2878_;
                                v_isShared_2882_ = v_isSharedCheck_2886_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_2879_);
                                lean_dec(v___x_2878_);
                                v___x_2881_ = lean_box(0);
                                v_isShared_2882_ = v_isSharedCheck_2886_;
                                state = 19;
                                continue;
                            }
                        } else {
                            v___x_2887_ = l_Lean_Expr_getAppNumArgs(v_a_2759_);
                            v___x_2888_ = lean_unsigned_to_nat(1);
                            v___x_2889_ = lean_nat_sub(v___x_2887_, v___x_2888_);
                            lean_dec(v___x_2887_);
                            lean_inc(v___x_2889_);
                            v___x_2890_ = l_Lean_Expr_getRevArg_x21(v_a_2759_, v___x_2889_);
                            v___x_2891_ = lean_nat_sub(v___x_2889_, v___x_2888_);
                            lean_dec(v___x_2889_);
                            v___x_2892_ = l_Lean_Expr_getRevArg_x21(v_a_2759_, v___x_2891_);
                            v_fst_2837_ = v___x_2890_;
                            v_snd_2838_ = v___x_2892_;
                            v___y_2839_ = v___y_2743_;
                            v___y_2840_ = v___y_2744_;
                            v___y_2841_ = v___y_2745_;
                            v___y_2842_ = v___y_2746_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_2893_ = lean_unsigned_to_nat(1);
                        v___x_2894_ = l_Lean_Expr_getAppNumArgs(v_a_2759_);
                        v___x_2895_ = lean_nat_sub(v___x_2894_, v___x_2893_);
                        v___x_2896_ = lean_nat_sub(v___x_2895_, v___x_2893_);
                        lean_dec(v___x_2895_);
                        v___x_2897_ = l_Lean_Expr_getRevArg_x21(v_a_2759_, v___x_2896_);
                        v___x_2898_ = lean_unsigned_to_nat(2);
                        v___x_2899_ = lean_nat_sub(v___x_2894_, v___x_2898_);
                        lean_dec(v___x_2894_);
                        v___x_2900_ = lean_nat_sub(v___x_2899_, v___x_2893_);
                        lean_dec(v___x_2899_);
                        v___x_2901_ = l_Lean_Expr_getRevArg_x21(v_a_2759_, v___x_2900_);
                        v_fst_2837_ = v___x_2897_;
                        v_snd_2838_ = v___x_2901_;
                        v___y_2839_ = v___y_2743_;
                        v___y_2840_ = v___y_2744_;
                        v___y_2841_ = v___y_2745_;
                        v___y_2842_ = v___y_2746_;
                        state = 14;
                        continue;
                    }
                } else {
                    v_a_2902_ = lean_ctor_get(v___x_2758_, 0);
                    v_isSharedCheck_2909_ = (!lean_is_exclusive(v___x_2758_)) as u8;
                    if v_isSharedCheck_2909_ == 0 {
                        v___x_2904_ = v___x_2758_;
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_2902_);
                        lean_dec(v___x_2758_);
                        v___x_2904_ = lean_box(0);
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2751_ = lean_nat_dec_eq(v___y_2750_, v___y_2749_);
                lean_dec(v___y_2750_);
                if v___x_2751_ == 0 {
                    v___x_2752_ = 1;
                    v___x_2753_ = lean_box((v___x_2752_) as usize);
                    v___x_2754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2754_, 0, v___x_2753_);
                    return v___x_2754_;
                } else {
                    v___x_2755_ = 2;
                    v___x_2756_ = lean_box((v___x_2755_) as usize);
                    v___x_2757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2757_, 0, v___x_2756_);
                    return v___x_2757_;
                }
            }
            2 => {
                v___x_2768_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_2762_, v___y_2767_);
                lean_dec_ref(v___y_2762_);
                if lean_obj_tag(v___x_2768_) == 0 {
                    v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
                    lean_inc(v_a_2769_);
                    lean_dec_ref_known(v___x_2768_, 1);
                    v___x_2770_ =
                        l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_2761_, v___y_2767_);
                    if lean_obj_tag(v___x_2770_) == 0 {
                        v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
                        lean_inc(v_a_2771_);
                        lean_dec_ref_known(v___x_2770_, 1);
                        lean_inc_ref(v___y_2761_);
                        v___x_2772_ = l_Lean_Meta_NormCast_countInternalCoes(
                            v___y_2761_,
                            v___y_2764_,
                            v___y_2765_,
                            v___y_2766_,
                            v___y_2767_,
                        );
                        if lean_obj_tag(v___x_2772_) == 0 {
                            v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
                            v_isSharedCheck_2811_ = (!lean_is_exclusive(v___x_2772_)) as u8;
                            if v_isSharedCheck_2811_ == 0 {
                                v___x_2775_ = v___x_2772_;
                                v_isShared_2776_ = v_isSharedCheck_2811_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2773_);
                                lean_dec(v___x_2772_);
                                v___x_2775_ = lean_box(0);
                                v_isShared_2776_ = v_isSharedCheck_2811_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2771_);
                            lean_dec(v_a_2769_);
                            lean_dec_ref(v___y_2761_);
                            lean_dec(v_a_2759_);
                            v_a_2812_ = lean_ctor_get(v___x_2772_, 0);
                            v_isSharedCheck_2819_ = (!lean_is_exclusive(v___x_2772_)) as u8;
                            if v_isSharedCheck_2819_ == 0 {
                                v___x_2814_ = v___x_2772_;
                                v_isShared_2815_ = v_isSharedCheck_2819_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2812_);
                                lean_dec(v___x_2772_);
                                v___x_2814_ = lean_box(0);
                                v_isShared_2815_ = v_isSharedCheck_2819_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2769_);
                        lean_dec_ref(v___y_2761_);
                        lean_dec(v_a_2759_);
                        v_a_2820_ = lean_ctor_get(v___x_2770_, 0);
                        v_isSharedCheck_2827_ = (!lean_is_exclusive(v___x_2770_)) as u8;
                        if v_isSharedCheck_2827_ == 0 {
                            v___x_2822_ = v___x_2770_;
                            v_isShared_2823_ = v_isSharedCheck_2827_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2820_);
                            lean_dec(v___x_2770_);
                            v___x_2822_ = lean_box(0);
                            v_isShared_2823_ = v_isSharedCheck_2827_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2761_);
                    lean_dec(v_a_2759_);
                    v_a_2828_ = lean_ctor_get(v___x_2768_, 0);
                    v_isSharedCheck_2835_ = (!lean_is_exclusive(v___x_2768_)) as u8;
                    if v_isSharedCheck_2835_ == 0 {
                        v___x_2830_ = v___x_2768_;
                        v_isShared_2831_ = v_isSharedCheck_2835_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2828_);
                        lean_dec(v___x_2768_);
                        v___x_2830_ = lean_box(0);
                        v_isShared_2831_ = v_isSharedCheck_2835_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2777_ = lean_unsigned_to_nat(0);
                v___x_2778_ = lean_nat_dec_eq(v_a_2769_, v___x_2777_);
                if v___x_2778_ == 0 {
                    v___x_2779_ = lean_unsigned_to_nat(1);
                    v___x_2780_ = lean_nat_dec_eq(v_a_2769_, v___x_2779_);
                    if v___x_2780_ == 0 {
                        lean_dec(v_a_2773_);
                        lean_dec_ref(v___y_2761_);
                        v___x_2781_ = lean_nat_dec_lt(v_a_2771_, v_a_2769_);
                        lean_dec(v_a_2769_);
                        lean_dec(v_a_2771_);
                        if v___x_2781_ == 0 {
                            lean_del_object(v___x_2775_);
                            v___x_2782_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_NormCast_classifyType___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_NormCast_classifyType___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1,
                            );
                            v___x_2783_ = l_Lean_indentExpr(v_a_2759_);
                            v___x_2784_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2784_, 0, v___x_2782_);
                            lean_ctor_set(v___x_2784_, 1, v___x_2783_);
                            lean_inc_ref(v___y_2763_);
                            v___x_2785_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2785_, 0, v___x_2784_);
                            lean_ctor_set(v___x_2785_, 1, v___y_2763_);
                            v___x_2786_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_2785_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
                            return v___x_2786_;
                        } else {
                            lean_dec(v_a_2759_);
                            v___x_2787_ = 2;
                            v___x_2788_ = lean_box((v___x_2787_) as usize);
                            if v_isShared_2776_ == 0 {
                                lean_ctor_set(v___x_2775_, 0, v___x_2788_);
                                v___x_2790_ = v___x_2775_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
                                v___x_2790_ = v_reuseFailAlloc_2791_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_2775_);
                        lean_dec(v_a_2769_);
                        lean_dec(v_a_2759_);
                        v___x_2792_ = lean_nat_dec_eq(v_a_2771_, v___x_2777_);
                        lean_dec(v_a_2771_);
                        if v___x_2792_ == 0 {
                            lean_dec(v_a_2773_);
                            v___x_2793_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_NormCast_classifyType___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_NormCast_classifyType___lam__0___closed__3_once
                                ),
                                _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3,
                            );
                            v___x_2794_ = l_Lean_indentExpr(v___y_2761_);
                            v___x_2795_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2795_, 0, v___x_2793_);
                            lean_ctor_set(v___x_2795_, 1, v___x_2794_);
                            lean_inc_ref(v___y_2763_);
                            v___x_2796_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                            lean_ctor_set(v___x_2796_, 1, v___y_2763_);
                            v___x_2797_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_2796_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
                            v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
                            v_isSharedCheck_2805_ = (!lean_is_exclusive(v___x_2797_)) as u8;
                            if v_isSharedCheck_2805_ == 0 {
                                v___x_2800_ = v___x_2797_;
                                v_isShared_2801_ = v_isSharedCheck_2805_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2798_);
                                lean_dec(v___x_2797_);
                                v___x_2800_ = lean_box(0);
                                v_isShared_2801_ = v_isSharedCheck_2805_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___y_2761_);
                            v___y_2749_ = v___x_2777_;
                            v___y_2750_ = v_a_2773_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2773_);
                    lean_dec(v_a_2771_);
                    lean_dec(v_a_2769_);
                    lean_dec_ref(v___y_2761_);
                    lean_dec(v_a_2759_);
                    v___x_2806_ = 0;
                    v___x_2807_ = lean_box((v___x_2806_) as usize);
                    if v_isShared_2776_ == 0 {
                        lean_ctor_set(v___x_2775_, 0, v___x_2807_);
                        v___x_2809_ = v___x_2775_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
                        v___x_2809_ = v_reuseFailAlloc_2810_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2790_;
            }
            5 => {
                if v_isShared_2801_ == 0 {
                    v___x_2803_ = v___x_2800_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2803_;
            }
            7 => {
                return v___x_2809_;
            }
            8 => {
                if v_isShared_2815_ == 0 {
                    v___x_2817_ = v___x_2814_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
                    v___x_2817_ = v_reuseFailAlloc_2818_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2817_;
            }
            10 => {
                if v_isShared_2823_ == 0 {
                    v___x_2825_ = v___x_2822_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
                    v___x_2825_ = v_reuseFailAlloc_2826_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2825_;
            }
            12 => {
                if v_isShared_2831_ == 0 {
                    v___x_2833_ = v___x_2830_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
                    v___x_2833_ = v_reuseFailAlloc_2834_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2833_;
            }
            14 => {
                lean_inc_ref(v_fst_2837_);
                v___x_2843_ = l_Lean_Meta_NormCast_countCoes(
                    v_fst_2837_,
                    v___y_2839_,
                    v___y_2840_,
                    v___y_2841_,
                    v___y_2842_,
                );
                if lean_obj_tag(v___x_2843_) == 0 {
                    v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
                    lean_inc(v_a_2844_);
                    lean_dec_ref_known(v___x_2843_, 1);
                    v___x_2845_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_NormCast_classifyType___lam__0___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_NormCast_classifyType___lam__0___closed__6_once
                        ),
                        _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6,
                    );
                    v___x_2846_ = lean_unsigned_to_nat(0);
                    v___x_2847_ = lean_nat_dec_eq(v_a_2844_, v___x_2846_);
                    lean_dec(v_a_2844_);
                    if v___x_2847_ == 0 {
                        v___y_2761_ = v_snd_2838_;
                        v___y_2762_ = v_fst_2837_;
                        v___y_2763_ = v___x_2845_;
                        v___y_2764_ = v___y_2839_;
                        v___y_2765_ = v___y_2840_;
                        v___y_2766_ = v___y_2841_;
                        v___y_2767_ = v___y_2842_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_snd_2838_);
                        lean_dec(v_a_2759_);
                        v___x_2848_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_classifyType___lam__0___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_NormCast_classifyType___lam__0___closed__8_once
                            ),
                            _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8,
                        );
                        v___x_2849_ = l_Lean_indentExpr(v_fst_2837_);
                        v___x_2850_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2850_, 0, v___x_2848_);
                        lean_ctor_set(v___x_2850_, 1, v___x_2849_);
                        v___x_2851_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2851_, 0, v___x_2850_);
                        lean_ctor_set(v___x_2851_, 1, v___x_2845_);
                        v___x_2852_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_2851_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
                        v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
                        v_isSharedCheck_2860_ = (!lean_is_exclusive(v___x_2852_)) as u8;
                        if v_isSharedCheck_2860_ == 0 {
                            v___x_2855_ = v___x_2852_;
                            v_isShared_2856_ = v_isSharedCheck_2860_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_2853_);
                            lean_dec(v___x_2852_);
                            v___x_2855_ = lean_box(0);
                            v_isShared_2856_ = v_isSharedCheck_2860_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_snd_2838_);
                    lean_dec_ref(v_fst_2837_);
                    lean_dec(v_a_2759_);
                    v_a_2861_ = lean_ctor_get(v___x_2843_, 0);
                    v_isSharedCheck_2868_ = (!lean_is_exclusive(v___x_2843_)) as u8;
                    if v_isSharedCheck_2868_ == 0 {
                        v___x_2863_ = v___x_2843_;
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_2861_);
                        lean_dec(v___x_2843_);
                        v___x_2863_ = lean_box(0);
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2856_ == 0 {
                    v___x_2858_ = v___x_2855_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
                    v___x_2858_ = v_reuseFailAlloc_2859_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2858_;
            }
            17 => {
                if v_isShared_2864_ == 0 {
                    v___x_2866_ = v___x_2863_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2866_;
            }
            19 => {
                if v_isShared_2882_ == 0 {
                    v___x_2884_ = v___x_2881_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
                    v___x_2884_ = v_reuseFailAlloc_2885_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2884_;
            }
            21 => {
                if v_isShared_2905_ == 0 {
                    v___x_2907_ = v___x_2904_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_classifyType___lam__0___boxed(
    mut v_x_2910_: *mut LeanObject,
    mut v_ty_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
    mut v___y_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2917_: *mut LeanObject = core::ptr::null_mut();
    v_res_2917_ = l_Lean_Meta_NormCast_classifyType___lam__0(
        v_x_2910_,
        v_ty_2911_,
        v___y_2912_,
        v___y_2913_,
        v___y_2914_,
        v___y_2915_,
    );
    lean_dec(v___y_2915_);
    lean_dec_ref(v___y_2914_);
    lean_dec(v___y_2913_);
    lean_dec_ref(v___y_2912_);
    lean_dec_ref(v_x_2910_);
    return v_res_2917_;
}
pub unsafe fn l_Lean_Meta_NormCast_classifyType(
    mut v_ty_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    v___f_2925_ = l_Lean_Meta_NormCast_classifyType___closed__0;
    v___x_2926_ = 0;
    v___x_2927_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_ty_2919_, v___f_2925_, v___x_2926_, v___x_2926_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
    return v___x_2927_;
}
pub unsafe fn l_Lean_Meta_NormCast_classifyType___boxed(
    mut v_ty_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2934_: *mut LeanObject = core::ptr::null_mut();
    v_res_2934_ =
        l_Lean_Meta_NormCast_classifyType(v_ty_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
    lean_dec(v_a_2932_);
    lean_dec_ref(v_a_2931_);
    lean_dec(v_a_2930_);
    lean_dec_ref(v_a_2929_);
    return v_res_2934_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(
    mut v_00_u03b1_2935_: *mut LeanObject,
    mut v_msg_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
    mut v___y_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    v___x_2942_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(
        v_msg_2936_,
        v___y_2937_,
        v___y_2938_,
        v___y_2939_,
        v___y_2940_,
    );
    return v___x_2942_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___boxed(
    mut v_00_u03b1_2943_: *mut LeanObject,
    mut v_msg_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(
        v_00_u03b1_2943_,
        v_msg_2944_,
        v___y_2945_,
        v___y_2946_,
        v___y_2947_,
        v___y_2948_,
    );
    lean_dec(v___y_2948_);
    lean_dec_ref(v___y_2947_);
    lean_dec(v___y_2946_);
    lean_dec_ref(v___y_2945_);
    return v_res_2950_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    v___x_2965_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_;
    v___x_2966_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_;
    v___x_2967_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_;
    v___x_2968_ = l_Lean_Meta_registerSimpAttr(v___x_2965_, v___x_2966_, v___x_2967_);
    return v___x_2968_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2____boxed(
    mut v_a_2969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2970_: *mut LeanObject = core::ptr::null_mut();
    v_res_2970_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_();
    return v_res_2970_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    v___x_2971_ = l_Lean_Meta_instInhabitedSimpEntry_default;
    v___x_2972_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v___x_2971_);
    return v___x_2972_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1()
-> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    v___x_2973_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0_once
        ),
        _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0,
    );
    v___x_2974_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2974_, 0, v___x_2973_);
    lean_ctor_set(v___x_2974_, 1, v___x_2973_);
    lean_ctor_set(v___x_2974_, 2, v___x_2973_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default() -> *mut LeanObject
{
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    v___x_2975_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1_once
        ),
        _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1,
    );
    return v___x_2975_;
}
pub unsafe fn _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension() -> *mut LeanObject {
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___x_2976_ = l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default;
    return v___x_2976_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    v___x_2986_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
    v___x_2987_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
    v___x_2988_ = l_Lean_Name_append(v___x_2987_, v___x_2986_);
    return v___x_2988_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    v___x_2992_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
    v___x_2993_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
    v___x_2994_ = l_Lean_Name_append(v___x_2993_, v___x_2992_);
    return v___x_2994_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    v___x_2998_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
    v___x_2999_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
    v___x_3000_ = l_Lean_Name_append(v___x_2999_, v___x_2998_);
    return v___x_3000_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_a_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3026_: u8 = 0;
    let mut v_a_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut v_a_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3002_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
                v___x_3003_ = l_Lean_Meta_mkSimpExt(v___x_3002_);
                if lean_obj_tag(v___x_3003_) == 0 {
                    v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
                    lean_inc(v_a_3004_);
                    lean_dec_ref_known(v___x_3003_, 1);
                    v___x_3005_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
                    v___x_3006_ = l_Lean_Meta_mkSimpExt(v___x_3005_);
                    if lean_obj_tag(v___x_3006_) == 0 {
                        v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
                        lean_inc(v_a_3007_);
                        lean_dec_ref_known(v___x_3006_, 1);
                        v___x_3008_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
                        v___x_3009_ = l_Lean_Meta_mkSimpExt(v___x_3008_);
                        if lean_obj_tag(v___x_3009_) == 0 {
                            v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
                            v_isSharedCheck_3018_ = (!lean_is_exclusive(v___x_3009_)) as u8;
                            if v_isSharedCheck_3018_ == 0 {
                                v___x_3012_ = v___x_3009_;
                                v_isShared_3013_ = v_isSharedCheck_3018_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3010_);
                                lean_dec(v___x_3009_);
                                v___x_3012_ = lean_box(0);
                                v_isShared_3013_ = v_isSharedCheck_3018_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3007_);
                            lean_dec(v_a_3004_);
                            v_a_3019_ = lean_ctor_get(v___x_3009_, 0);
                            v_isSharedCheck_3026_ = (!lean_is_exclusive(v___x_3009_)) as u8;
                            if v_isSharedCheck_3026_ == 0 {
                                v___x_3021_ = v___x_3009_;
                                v_isShared_3022_ = v_isSharedCheck_3026_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3019_);
                                lean_dec(v___x_3009_);
                                v___x_3021_ = lean_box(0);
                                v_isShared_3022_ = v_isSharedCheck_3026_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3004_);
                        v_a_3027_ = lean_ctor_get(v___x_3006_, 0);
                        v_isSharedCheck_3034_ = (!lean_is_exclusive(v___x_3006_)) as u8;
                        if v_isSharedCheck_3034_ == 0 {
                            v___x_3029_ = v___x_3006_;
                            v_isShared_3030_ = v_isSharedCheck_3034_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3027_);
                            lean_dec(v___x_3006_);
                            v___x_3029_ = lean_box(0);
                            v_isShared_3030_ = v_isSharedCheck_3034_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_3035_ = lean_ctor_get(v___x_3003_, 0);
                    v_isSharedCheck_3042_ = (!lean_is_exclusive(v___x_3003_)) as u8;
                    if v_isSharedCheck_3042_ == 0 {
                        v___x_3037_ = v___x_3003_;
                        v_isShared_3038_ = v_isSharedCheck_3042_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3035_);
                        lean_dec(v___x_3003_);
                        v___x_3037_ = lean_box(0);
                        v_isShared_3038_ = v_isSharedCheck_3042_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3014_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3014_, 0, v_a_3004_);
                lean_ctor_set(v___x_3014_, 1, v_a_3007_);
                lean_ctor_set(v___x_3014_, 2, v_a_3010_);
                if v_isShared_3013_ == 0 {
                    lean_ctor_set(v___x_3012_, 0, v___x_3014_);
                    v___x_3016_ = v___x_3012_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
                    v___x_3016_ = v_reuseFailAlloc_3017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3016_;
            }
            3 => {
                if v_isShared_3022_ == 0 {
                    v___x_3024_ = v___x_3021_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
                    v___x_3024_ = v_reuseFailAlloc_3025_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3024_;
            }
            5 => {
                if v_isShared_3030_ == 0 {
                    v___x_3032_ = v___x_3029_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
                    v___x_3032_ = v_reuseFailAlloc_3033_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3032_;
            }
            7 => {
                if v_isShared_3038_ == 0 {
                    v___x_3040_ = v___x_3037_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
                    v___x_3040_ = v_reuseFailAlloc_3041_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2____boxed(
    mut v_a_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3044_: *mut LeanObject = core::ptr::null_mut();
    v_res_3044_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_();
    return v_res_3044_;
}
pub unsafe fn l_Lean_Meta_NormCast_addElim(
    mut v_decl_3045_: *mut LeanObject,
    mut v_kind_3046_: u8,
    mut v_prio_3047_: *mut LeanObject,
    mut v_a_3048_: *mut LeanObject,
    mut v_a_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_up_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    v___x_3053_ = l_Lean_Meta_NormCast_normCastExt;
    v_up_3054_ = lean_ctor_get(v___x_3053_, 0);
    v___x_3055_ = 1;
    v___x_3056_ = 0;
    lean_inc_ref(v_up_3054_);
    v___x_3057_ = l_Lean_Meta_addSimpTheorem(
        v_up_3054_,
        v_decl_3045_,
        v___x_3055_,
        v___x_3056_,
        v_kind_3046_,
        v_prio_3047_,
        v_a_3048_,
        v_a_3049_,
        v_a_3050_,
        v_a_3051_,
    );
    return v___x_3057_;
}
pub unsafe fn l_Lean_Meta_NormCast_addElim___boxed(
    mut v_decl_3058_: *mut LeanObject,
    mut v_kind_3059_: *mut LeanObject,
    mut v_prio_3060_: *mut LeanObject,
    mut v_a_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3066_: u8 = 0;
    let mut v_res_3067_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3066_ = (lean_unbox(v_kind_3059_) as u8);
    v_res_3067_ = l_Lean_Meta_NormCast_addElim(
        v_decl_3058_,
        v_kind_boxed_3066_,
        v_prio_3060_,
        v_a_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
    );
    lean_dec(v_a_3064_);
    lean_dec_ref(v_a_3063_);
    lean_dec(v_a_3062_);
    lean_dec_ref(v_a_3061_);
    return v_res_3067_;
}
pub unsafe fn l_Lean_Meta_NormCast_addMove(
    mut v_decl_3068_: *mut LeanObject,
    mut v_kind_3069_: u8,
    mut v_prio_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_a_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: u8 = 0;
    let mut v___x_3078_: u8 = 0;
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    v___x_3076_ = l_Lean_Meta_NormCast_pushCastExt;
    v___x_3077_ = 1;
    v___x_3078_ = 0;
    lean_inc(v_prio_3070_);
    lean_inc(v_decl_3068_);
    v___x_3079_ = l_Lean_Meta_addSimpTheorem(
        v___x_3076_,
        v_decl_3068_,
        v___x_3077_,
        v___x_3078_,
        v_kind_3069_,
        v_prio_3070_,
        v_a_3071_,
        v_a_3072_,
        v_a_3073_,
        v_a_3074_,
    );
    if lean_obj_tag(v___x_3079_) == 0 {
        let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
        let mut v_up_3081_: *mut LeanObject = core::ptr::null_mut();
        let mut v_down_3082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3079_, 1);
        v___x_3080_ = l_Lean_Meta_NormCast_normCastExt;
        v_up_3081_ = lean_ctor_get(v___x_3080_, 0);
        v_down_3082_ = lean_ctor_get(v___x_3080_, 1);
        lean_inc(v_prio_3070_);
        lean_inc(v_decl_3068_);
        lean_inc_ref(v_up_3081_);
        v___x_3083_ = l_Lean_Meta_addSimpTheorem(
            v_up_3081_,
            v_decl_3068_,
            v___x_3077_,
            v___x_3077_,
            v_kind_3069_,
            v_prio_3070_,
            v_a_3071_,
            v_a_3072_,
            v_a_3073_,
            v_a_3074_,
        );
        if lean_obj_tag(v___x_3083_) == 0 {
            let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_3083_, 1);
            lean_inc_ref(v_down_3082_);
            v___x_3084_ = l_Lean_Meta_addSimpTheorem(
                v_down_3082_,
                v_decl_3068_,
                v___x_3077_,
                v___x_3078_,
                v_kind_3069_,
                v_prio_3070_,
                v_a_3071_,
                v_a_3072_,
                v_a_3073_,
                v_a_3074_,
            );
            return v___x_3084_;
        } else {
            lean_dec(v_prio_3070_);
            lean_dec(v_decl_3068_);
            return v___x_3083_;
        }
    } else {
        lean_dec(v_prio_3070_);
        lean_dec(v_decl_3068_);
        return v___x_3079_;
    }
}
pub unsafe fn l_Lean_Meta_NormCast_addMove___boxed(
    mut v_decl_3085_: *mut LeanObject,
    mut v_kind_3086_: *mut LeanObject,
    mut v_prio_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3093_: u8 = 0;
    let mut v_res_3094_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3093_ = (lean_unbox(v_kind_3086_) as u8);
    v_res_3094_ = l_Lean_Meta_NormCast_addMove(
        v_decl_3085_,
        v_kind_boxed_3093_,
        v_prio_3087_,
        v_a_3088_,
        v_a_3089_,
        v_a_3090_,
        v_a_3091_,
    );
    lean_dec(v_a_3091_);
    lean_dec_ref(v_a_3090_);
    lean_dec(v_a_3089_);
    lean_dec_ref(v_a_3088_);
    return v_res_3094_;
}
pub unsafe fn l_Lean_Meta_NormCast_addSquash(
    mut v_decl_3095_: *mut LeanObject,
    mut v_kind_3096_: u8,
    mut v_prio_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
    mut v_a_3100_: *mut LeanObject,
    mut v_a_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    v___x_3103_ = l_Lean_Meta_NormCast_pushCastExt;
    v___x_3104_ = 1;
    v___x_3105_ = 0;
    lean_inc(v_prio_3097_);
    lean_inc(v_decl_3095_);
    v___x_3106_ = l_Lean_Meta_addSimpTheorem(
        v___x_3103_,
        v_decl_3095_,
        v___x_3104_,
        v___x_3105_,
        v_kind_3096_,
        v_prio_3097_,
        v_a_3098_,
        v_a_3099_,
        v_a_3100_,
        v_a_3101_,
    );
    if lean_obj_tag(v___x_3106_) == 0 {
        let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
        let mut v_down_3108_: *mut LeanObject = core::ptr::null_mut();
        let mut v_squash_3109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3106_, 1);
        v___x_3107_ = l_Lean_Meta_NormCast_normCastExt;
        v_down_3108_ = lean_ctor_get(v___x_3107_, 1);
        v_squash_3109_ = lean_ctor_get(v___x_3107_, 2);
        lean_inc(v_prio_3097_);
        lean_inc(v_decl_3095_);
        lean_inc_ref(v_squash_3109_);
        v___x_3110_ = l_Lean_Meta_addSimpTheorem(
            v_squash_3109_,
            v_decl_3095_,
            v___x_3104_,
            v___x_3105_,
            v_kind_3096_,
            v_prio_3097_,
            v_a_3098_,
            v_a_3099_,
            v_a_3100_,
            v_a_3101_,
        );
        if lean_obj_tag(v___x_3110_) == 0 {
            let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_3110_, 1);
            lean_inc_ref(v_down_3108_);
            v___x_3111_ = l_Lean_Meta_addSimpTheorem(
                v_down_3108_,
                v_decl_3095_,
                v___x_3104_,
                v___x_3105_,
                v_kind_3096_,
                v_prio_3097_,
                v_a_3098_,
                v_a_3099_,
                v_a_3100_,
                v_a_3101_,
            );
            return v___x_3111_;
        } else {
            lean_dec(v_prio_3097_);
            lean_dec(v_decl_3095_);
            return v___x_3110_;
        }
    } else {
        lean_dec(v_prio_3097_);
        lean_dec(v_decl_3095_);
        return v___x_3106_;
    }
}
pub unsafe fn l_Lean_Meta_NormCast_addSquash___boxed(
    mut v_decl_3112_: *mut LeanObject,
    mut v_kind_3113_: *mut LeanObject,
    mut v_prio_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
    mut v_a_3117_: *mut LeanObject,
    mut v_a_3118_: *mut LeanObject,
    mut v_a_3119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3120_: u8 = 0;
    let mut v_res_3121_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3120_ = (lean_unbox(v_kind_3113_) as u8);
    v_res_3121_ = l_Lean_Meta_NormCast_addSquash(
        v_decl_3112_,
        v_kind_boxed_3120_,
        v_prio_3114_,
        v_a_3115_,
        v_a_3116_,
        v_a_3117_,
        v_a_3118_,
    );
    lean_dec(v_a_3118_);
    lean_dec_ref(v_a_3117_);
    lean_dec(v_a_3116_);
    lean_dec_ref(v_a_3115_);
    return v_res_3121_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    v___x_3122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3122_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    v___x_3123_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_3124_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3124_, 0, v___x_3123_);
    return v___x_3124_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    v___x_3125_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3126_ = lean_unsigned_to_nat(0);
    v___x_3127_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3127_, 0, v___x_3126_);
    lean_ctor_set(v___x_3127_, 1, v___x_3126_);
    lean_ctor_set(v___x_3127_, 2, v___x_3126_);
    lean_ctor_set(v___x_3127_, 3, v___x_3126_);
    lean_ctor_set(v___x_3127_, 4, v___x_3125_);
    lean_ctor_set(v___x_3127_, 5, v___x_3125_);
    lean_ctor_set(v___x_3127_, 6, v___x_3125_);
    lean_ctor_set(v___x_3127_, 7, v___x_3125_);
    lean_ctor_set(v___x_3127_, 8, v___x_3125_);
    lean_ctor_set(v___x_3127_, 9, v___x_3125_);
    return v___x_3127_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    v___x_3128_ = lean_unsigned_to_nat(32);
    v___x_3129_ = lean_mk_empty_array_with_capacity(v___x_3128_);
    v___x_3130_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3130_, 0, v___x_3129_);
    return v___x_3130_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3131_: usize = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    v___x_3131_ = 5usize;
    v___x_3132_ = lean_unsigned_to_nat(0);
    v___x_3133_ = lean_unsigned_to_nat(32);
    v___x_3134_ = lean_mk_empty_array_with_capacity(v___x_3133_);
    v___x_3135_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_3136_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3136_, 0, v___x_3135_);
    lean_ctor_set(v___x_3136_, 1, v___x_3134_);
    lean_ctor_set(v___x_3136_, 2, v___x_3132_);
    lean_ctor_set(v___x_3136_, 3, v___x_3132_);
    lean_ctor_set_usize(v___x_3136_, 4, v___x_3131_);
    return v___x_3136_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    v___x_3137_ = lean_box(1);
    v___x_3138_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_3139_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3140_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3140_, 0, v___x_3139_);
    lean_ctor_set(v___x_3140_, 1, v___x_3138_);
    lean_ctor_set(v___x_3140_, 2, v___x_3137_);
    return v___x_3140_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_3143_ = l_Lean_stringToMessageData(v___x_3142_);
    return v___x_3143_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    v___x_3145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_3146_ = l_Lean_stringToMessageData(v___x_3145_);
    return v___x_3146_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    v___x_3148_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_3149_ = l_Lean_stringToMessageData(v___x_3148_);
    return v___x_3149_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    v___x_3151_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_3152_ = l_Lean_stringToMessageData(v___x_3151_);
    return v___x_3152_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    v___x_3154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_3155_ = l_Lean_stringToMessageData(v___x_3154_);
    return v___x_3155_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    v___x_3157_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_3158_ = l_Lean_stringToMessageData(v___x_3157_);
    return v___x_3158_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    v___x_3160_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_3161_ = l_Lean_stringToMessageData(v___x_3160_);
    return v___x_3161_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_3162_: *mut LeanObject,
    mut v_declHint_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v_isExporting_3169_: u8 = 0;
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3166_ = lean_st_ref_get(v___y_3164_);
                v_env_3167_ = lean_ctor_get(v___x_3166_, 0);
                lean_inc_ref(v_env_3167_);
                lean_dec(v___x_3166_);
                v___x_3168_ = l_Lean_Name_isAnonymous(v_declHint_3163_);
                if v___x_3168_ == 0 {
                    v_isExporting_3169_ = lean_ctor_get_uint8(
                        v_env_3167_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3169_ == 0 {
                        lean_dec_ref(v_env_3167_);
                        lean_dec(v_declHint_3163_);
                        v___x_3170_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3170_, 0, v_msg_3162_);
                        return v___x_3170_;
                    } else {
                        lean_inc_ref(v_env_3167_);
                        v___x_3171_ = l_Lean_Environment_setExporting(v_env_3167_, v___x_3168_);
                        lean_inc(v_declHint_3163_);
                        lean_inc_ref(v___x_3171_);
                        v___x_3172_ = l_Lean_Environment_contains(
                            v___x_3171_,
                            v_declHint_3163_,
                            v_isExporting_3169_,
                        );
                        if v___x_3172_ == 0 {
                            lean_dec_ref(v___x_3171_);
                            lean_dec_ref(v_env_3167_);
                            lean_dec(v_declHint_3163_);
                            v___x_3173_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3173_, 0, v_msg_3162_);
                            return v___x_3173_;
                        } else {
                            v___x_3174_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_3175_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_3176_ = l_Lean_Options_empty;
                            v___x_3177_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3177_, 0, v___x_3171_);
                            lean_ctor_set(v___x_3177_, 1, v___x_3174_);
                            lean_ctor_set(v___x_3177_, 2, v___x_3175_);
                            lean_ctor_set(v___x_3177_, 3, v___x_3176_);
                            lean_inc(v_declHint_3163_);
                            v___x_3178_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3163_, v___x_3168_);
                            v_c_3179_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3179_, 0, v___x_3177_);
                            lean_ctor_set(v_c_3179_, 1, v___x_3178_);
                            v___x_3180_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3167_,
                                v_declHint_3163_,
                            );
                            if lean_obj_tag(v___x_3180_) == 0 {
                                lean_dec_ref(v_env_3167_);
                                lean_dec(v_declHint_3163_);
                                v___x_3181_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_3182_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3182_, 0, v___x_3181_);
                                lean_ctor_set(v___x_3182_, 1, v_c_3179_);
                                v___x_3183_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_3184_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3184_, 0, v___x_3182_);
                                lean_ctor_set(v___x_3184_, 1, v___x_3183_);
                                v___x_3185_ = l_Lean_MessageData_note(v___x_3184_);
                                v___x_3186_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3186_, 0, v_msg_3162_);
                                lean_ctor_set(v___x_3186_, 1, v___x_3185_);
                                v___x_3187_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3187_, 0, v___x_3186_);
                                return v___x_3187_;
                            } else {
                                v_val_3188_ = lean_ctor_get(v___x_3180_, 0);
                                v_isSharedCheck_3223_ = (!lean_is_exclusive(v___x_3180_)) as u8;
                                if v_isSharedCheck_3223_ == 0 {
                                    v___x_3190_ = v___x_3180_;
                                    v_isShared_3191_ = v_isSharedCheck_3223_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3188_);
                                    lean_dec(v___x_3180_);
                                    v___x_3190_ = lean_box(0);
                                    v_isShared_3191_ = v_isSharedCheck_3223_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3167_);
                    lean_dec(v_declHint_3163_);
                    v___x_3224_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3224_, 0, v_msg_3162_);
                    return v___x_3224_;
                }
            }
            1 => {
                v___x_3192_ = lean_box(0);
                v___x_3193_ = l_Lean_Environment_header(v_env_3167_);
                lean_dec_ref(v_env_3167_);
                v___x_3194_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3193_);
                v_mod_3195_ = lean_array_get(v___x_3192_, v___x_3194_, v_val_3188_);
                lean_dec(v_val_3188_);
                lean_dec_ref(v___x_3194_);
                v___x_3196_ = l_Lean_isPrivateName(v_declHint_3163_);
                lean_dec(v_declHint_3163_);
                if v___x_3196_ == 0 {
                    v___x_3197_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_3198_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3198_, 0, v___x_3197_);
                    lean_ctor_set(v___x_3198_, 1, v_c_3179_);
                    v___x_3199_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_3200_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3200_, 0, v___x_3198_);
                    lean_ctor_set(v___x_3200_, 1, v___x_3199_);
                    v___x_3201_ = l_Lean_MessageData_ofName(v_mod_3195_);
                    v___x_3202_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3202_, 0, v___x_3200_);
                    lean_ctor_set(v___x_3202_, 1, v___x_3201_);
                    v___x_3203_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_3204_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3204_, 0, v___x_3202_);
                    lean_ctor_set(v___x_3204_, 1, v___x_3203_);
                    v___x_3205_ = l_Lean_MessageData_note(v___x_3204_);
                    v___x_3206_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3206_, 0, v_msg_3162_);
                    lean_ctor_set(v___x_3206_, 1, v___x_3205_);
                    if v_isShared_3191_ == 0 {
                        lean_ctor_set_tag(v___x_3190_, 0);
                        lean_ctor_set(v___x_3190_, 0, v___x_3206_);
                        v___x_3208_ = v___x_3190_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
                        v___x_3208_ = v_reuseFailAlloc_3209_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3210_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_3211_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                    lean_ctor_set(v___x_3211_, 1, v_c_3179_);
                    v___x_3212_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_3213_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3213_, 0, v___x_3211_);
                    lean_ctor_set(v___x_3213_, 1, v___x_3212_);
                    v___x_3214_ = l_Lean_MessageData_ofName(v_mod_3195_);
                    v___x_3215_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3215_, 0, v___x_3213_);
                    lean_ctor_set(v___x_3215_, 1, v___x_3214_);
                    v___x_3216_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_3217_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3217_, 0, v___x_3215_);
                    lean_ctor_set(v___x_3217_, 1, v___x_3216_);
                    v___x_3218_ = l_Lean_MessageData_note(v___x_3217_);
                    v___x_3219_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3219_, 0, v_msg_3162_);
                    lean_ctor_set(v___x_3219_, 1, v___x_3218_);
                    if v_isShared_3191_ == 0 {
                        lean_ctor_set_tag(v___x_3190_, 0);
                        lean_ctor_set(v___x_3190_, 0, v___x_3219_);
                        v___x_3221_ = v___x_3190_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
                        v___x_3221_ = v_reuseFailAlloc_3222_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3208_;
            }
            3 => {
                return v___x_3221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_3225_: *mut LeanObject,
    mut v_declHint_3226_: *mut LeanObject,
    mut v___y_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3229_: *mut LeanObject = core::ptr::null_mut();
    v_res_3229_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3225_, v_declHint_3226_, v___y_3227_);
    lean_dec(v___y_3227_);
    return v_res_3229_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_3230_: *mut LeanObject,
    mut v_declHint_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3241_: u8 = 0;
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3237_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3230_, v_declHint_3231_, v___y_3235_);
                v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
                v_isSharedCheck_3247_ = (!lean_is_exclusive(v___x_3237_)) as u8;
                if v_isSharedCheck_3247_ == 0 {
                    v___x_3240_ = v___x_3237_;
                    v_isShared_3241_ = v_isSharedCheck_3247_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3238_);
                    lean_dec(v___x_3237_);
                    v___x_3240_ = lean_box(0);
                    v_isShared_3241_ = v_isSharedCheck_3247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3242_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3243_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3243_, 0, v___x_3242_);
                lean_ctor_set(v___x_3243_, 1, v_a_3238_);
                if v_isShared_3241_ == 0 {
                    lean_ctor_set(v___x_3240_, 0, v___x_3243_);
                    v___x_3245_ = v___x_3240_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_3248_: *mut LeanObject,
    mut v_declHint_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
    mut v___y_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3255_: *mut LeanObject = core::ptr::null_mut();
    v_res_3255_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3248_, v_declHint_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
    lean_dec(v___y_3253_);
    lean_dec_ref(v___y_3252_);
    lean_dec(v___y_3251_);
    lean_dec_ref(v___y_3250_);
    return v_res_3255_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_3256_: *mut LeanObject,
    mut v_msg_3257_: *mut LeanObject,
    mut v___y_3258_: *mut LeanObject,
    mut v___y_3259_: *mut LeanObject,
    mut v___y_3260_: *mut LeanObject,
    mut v___y_3261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3275_: u8 = 0;
    let mut v_cancelTk_x3f_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3277_: u8 = 0;
    let mut v_inheritedTraceOptions_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3263_ = lean_ctor_get(v___y_3260_, 0);
    v_fileMap_3264_ = lean_ctor_get(v___y_3260_, 1);
    v_options_3265_ = lean_ctor_get(v___y_3260_, 2);
    v_currRecDepth_3266_ = lean_ctor_get(v___y_3260_, 3);
    v_maxRecDepth_3267_ = lean_ctor_get(v___y_3260_, 4);
    v_ref_3268_ = lean_ctor_get(v___y_3260_, 5);
    v_currNamespace_3269_ = lean_ctor_get(v___y_3260_, 6);
    v_openDecls_3270_ = lean_ctor_get(v___y_3260_, 7);
    v_initHeartbeats_3271_ = lean_ctor_get(v___y_3260_, 8);
    v_maxHeartbeats_3272_ = lean_ctor_get(v___y_3260_, 9);
    v_quotContext_3273_ = lean_ctor_get(v___y_3260_, 10);
    v_currMacroScope_3274_ = lean_ctor_get(v___y_3260_, 11);
    v_diag_3275_ = lean_ctor_get_uint8(
        v___y_3260_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3276_ = lean_ctor_get(v___y_3260_, 12);
    v_suppressElabErrors_3277_ = lean_ctor_get_uint8(
        v___y_3260_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3278_ = lean_ctor_get(v___y_3260_, 13);
    v_ref_3279_ = l_Lean_replaceRef(v_ref_3256_, v_ref_3268_);
    lean_inc_ref(v_inheritedTraceOptions_3278_);
    lean_inc(v_cancelTk_x3f_3276_);
    lean_inc(v_currMacroScope_3274_);
    lean_inc(v_quotContext_3273_);
    lean_inc(v_maxHeartbeats_3272_);
    lean_inc(v_initHeartbeats_3271_);
    lean_inc(v_openDecls_3270_);
    lean_inc(v_currNamespace_3269_);
    lean_inc(v_maxRecDepth_3267_);
    lean_inc(v_currRecDepth_3266_);
    lean_inc_ref(v_options_3265_);
    lean_inc_ref(v_fileMap_3264_);
    lean_inc_ref(v_fileName_3263_);
    v___x_3280_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3280_, 0, v_fileName_3263_);
    lean_ctor_set(v___x_3280_, 1, v_fileMap_3264_);
    lean_ctor_set(v___x_3280_, 2, v_options_3265_);
    lean_ctor_set(v___x_3280_, 3, v_currRecDepth_3266_);
    lean_ctor_set(v___x_3280_, 4, v_maxRecDepth_3267_);
    lean_ctor_set(v___x_3280_, 5, v_ref_3279_);
    lean_ctor_set(v___x_3280_, 6, v_currNamespace_3269_);
    lean_ctor_set(v___x_3280_, 7, v_openDecls_3270_);
    lean_ctor_set(v___x_3280_, 8, v_initHeartbeats_3271_);
    lean_ctor_set(v___x_3280_, 9, v_maxHeartbeats_3272_);
    lean_ctor_set(v___x_3280_, 10, v_quotContext_3273_);
    lean_ctor_set(v___x_3280_, 11, v_currMacroScope_3274_);
    lean_ctor_set(v___x_3280_, 12, v_cancelTk_x3f_3276_);
    lean_ctor_set(v___x_3280_, 13, v_inheritedTraceOptions_3278_);
    lean_ctor_set_uint8(
        v___x_3280_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3275_,
    );
    lean_ctor_set_uint8(
        v___x_3280_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3277_,
    );
    v___x_3281_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(
        v_msg_3257_,
        v___y_3258_,
        v___y_3259_,
        v___x_3280_,
        v___y_3261_,
    );
    lean_dec_ref_known(v___x_3280_, 14);
    return v___x_3281_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_3282_: *mut LeanObject,
    mut v_msg_3283_: *mut LeanObject,
    mut v___y_3284_: *mut LeanObject,
    mut v___y_3285_: *mut LeanObject,
    mut v___y_3286_: *mut LeanObject,
    mut v___y_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3289_: *mut LeanObject = core::ptr::null_mut();
    v_res_3289_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3282_, v_msg_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
    lean_dec(v___y_3287_);
    lean_dec_ref(v___y_3286_);
    lean_dec(v___y_3285_);
    lean_dec_ref(v___y_3284_);
    lean_dec(v_ref_3282_);
    return v_res_3289_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_3290_: *mut LeanObject,
    mut v_msg_3291_: *mut LeanObject,
    mut v_declHint_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
    mut v___y_3294_: *mut LeanObject,
    mut v___y_3295_: *mut LeanObject,
    mut v___y_3296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    v___x_3298_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3291_, v_declHint_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
    v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
    lean_inc(v_a_3299_);
    lean_dec_ref(v___x_3298_);
    v___x_3300_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3290_, v_a_3299_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
    return v___x_3300_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_3301_: *mut LeanObject,
    mut v_msg_3302_: *mut LeanObject,
    mut v_declHint_3303_: *mut LeanObject,
    mut v___y_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3309_: *mut LeanObject = core::ptr::null_mut();
    v_res_3309_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3301_, v_msg_3302_, v_declHint_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
    lean_dec(v___y_3307_);
    lean_dec_ref(v___y_3306_);
    lean_dec(v___y_3305_);
    lean_dec_ref(v___y_3304_);
    lean_dec(v_ref_3301_);
    return v_res_3309_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
    return v___x_3312_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3316_: *mut LeanObject,
    mut v_constName_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    v___x_3323_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3324_ = 0;
    lean_inc(v_constName_3317_);
    v___x_3325_ = l_Lean_MessageData_ofConstName(v_constName_3317_, v___x_3324_);
    v___x_3326_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3326_, 0, v___x_3323_);
    lean_ctor_set(v___x_3326_, 1, v___x_3325_);
    v___x_3327_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3328_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3328_, 0, v___x_3326_);
    lean_ctor_set(v___x_3328_, 1, v___x_3327_);
    v___x_3329_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3316_, v___x_3328_, v_constName_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
    return v___x_3329_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3330_: *mut LeanObject,
    mut v_constName_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3337_: *mut LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_3330_, v_constName_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
    lean_dec(v___y_3335_);
    lean_dec_ref(v___y_3334_);
    lean_dec(v___y_3333_);
    lean_dec_ref(v___y_3332_);
    lean_dec(v_ref_3330_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(
    mut v_constName_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3344_ = lean_ctor_get(v___y_3341_, 5);
    v___x_3345_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_3344_, v_constName_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
    return v___x_3345_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg___boxed(
    mut v_constName_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3352_: *mut LeanObject = core::ptr::null_mut();
    v_res_3352_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
    lean_dec(v___y_3350_);
    lean_dec_ref(v___y_3349_);
    lean_dec(v___y_3348_);
    lean_dec_ref(v___y_3347_);
    return v_res_3352_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(
    mut v_constName_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: u8 = 0;
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3359_ = lean_st_ref_get(v___y_3357_);
                v_env_3360_ = lean_ctor_get(v___x_3359_, 0);
                lean_inc_ref(v_env_3360_);
                lean_dec(v___x_3359_);
                v___x_3361_ = 0;
                lean_inc(v_constName_3353_);
                v___x_3362_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_3360_,
                    v_constName_3353_,
                    v___x_3361_,
                );
                if lean_obj_tag(v___x_3362_) == 0 {
                    v___x_3363_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
                    return v___x_3363_;
                } else {
                    lean_dec(v_constName_3353_);
                    v_val_3364_ = lean_ctor_get(v___x_3362_, 0);
                    v_isSharedCheck_3371_ = (!lean_is_exclusive(v___x_3362_)) as u8;
                    if v_isSharedCheck_3371_ == 0 {
                        v___x_3366_ = v___x_3362_;
                        v_isShared_3367_ = v_isSharedCheck_3371_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3364_);
                        lean_dec(v___x_3362_);
                        v___x_3366_ = lean_box(0);
                        v_isShared_3367_ = v_isSharedCheck_3371_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3367_ == 0 {
                    lean_ctor_set_tag(v___x_3366_, 0);
                    v___x_3369_ = v___x_3366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_val_3364_);
                    v___x_3369_ = v_reuseFailAlloc_3370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0___boxed(
    mut v_constName_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3378_: *mut LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(
        v_constName_3372_,
        v___y_3373_,
        v___y_3374_,
        v___y_3375_,
        v___y_3376_,
    );
    lean_dec(v___y_3376_);
    lean_dec_ref(v___y_3375_);
    lean_dec(v___y_3374_);
    lean_dec_ref(v___y_3373_);
    return v_res_3378_;
}
pub unsafe fn l_Lean_Meta_NormCast_addInfer(
    mut v_decl_3379_: *mut LeanObject,
    mut v_kind_3380_: u8,
    mut v_prio_3381_: *mut LeanObject,
    mut v_a_3382_: *mut LeanObject,
    mut v_a_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut v_a_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_decl_3379_);
                v___x_3387_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(
                    v_decl_3379_,
                    v_a_3382_,
                    v_a_3383_,
                    v_a_3384_,
                    v_a_3385_,
                );
                if lean_obj_tag(v___x_3387_) == 0 {
                    v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
                    lean_inc(v_a_3388_);
                    lean_dec_ref_known(v___x_3387_, 1);
                    v_type_3389_ = lean_ctor_get(v_a_3388_, 2);
                    lean_inc_ref(v_type_3389_);
                    lean_dec(v_a_3388_);
                    v___x_3390_ = l_Lean_Meta_NormCast_classifyType(
                        v_type_3389_,
                        v_a_3382_,
                        v_a_3383_,
                        v_a_3384_,
                        v_a_3385_,
                    );
                    if lean_obj_tag(v___x_3390_) == 0 {
                        v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
                        lean_inc(v_a_3391_);
                        lean_dec_ref_known(v___x_3390_, 1);
                        v___x_3392_ = (lean_unbox(v_a_3391_) as u8);
                        lean_dec(v_a_3391_);
                        match v___x_3392_ {
                            0 => {
                                v___x_3393_ = l_Lean_Meta_NormCast_addElim(
                                    v_decl_3379_,
                                    v_kind_3380_,
                                    v_prio_3381_,
                                    v_a_3382_,
                                    v_a_3383_,
                                    v_a_3384_,
                                    v_a_3385_,
                                );
                                return v___x_3393_;
                            }
                            1 => {
                                v___x_3394_ = l_Lean_Meta_NormCast_addMove(
                                    v_decl_3379_,
                                    v_kind_3380_,
                                    v_prio_3381_,
                                    v_a_3382_,
                                    v_a_3383_,
                                    v_a_3384_,
                                    v_a_3385_,
                                );
                                return v___x_3394_;
                            }
                            _ => {
                                v___x_3395_ = l_Lean_Meta_NormCast_addSquash(
                                    v_decl_3379_,
                                    v_kind_3380_,
                                    v_prio_3381_,
                                    v_a_3382_,
                                    v_a_3383_,
                                    v_a_3384_,
                                    v_a_3385_,
                                );
                                return v___x_3395_;
                            }
                        }
                    } else {
                        lean_dec(v_prio_3381_);
                        lean_dec(v_decl_3379_);
                        v_a_3396_ = lean_ctor_get(v___x_3390_, 0);
                        v_isSharedCheck_3403_ = (!lean_is_exclusive(v___x_3390_)) as u8;
                        if v_isSharedCheck_3403_ == 0 {
                            v___x_3398_ = v___x_3390_;
                            v_isShared_3399_ = v_isSharedCheck_3403_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3396_);
                            lean_dec(v___x_3390_);
                            v___x_3398_ = lean_box(0);
                            v_isShared_3399_ = v_isSharedCheck_3403_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_prio_3381_);
                    lean_dec(v_decl_3379_);
                    v_a_3404_ = lean_ctor_get(v___x_3387_, 0);
                    v_isSharedCheck_3411_ = (!lean_is_exclusive(v___x_3387_)) as u8;
                    if v_isSharedCheck_3411_ == 0 {
                        v___x_3406_ = v___x_3387_;
                        v_isShared_3407_ = v_isSharedCheck_3411_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3404_);
                        lean_dec(v___x_3387_);
                        v___x_3406_ = lean_box(0);
                        v_isShared_3407_ = v_isSharedCheck_3411_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3399_ == 0 {
                    v___x_3401_ = v___x_3398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
                    v___x_3401_ = v_reuseFailAlloc_3402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3401_;
            }
            3 => {
                if v_isShared_3407_ == 0 {
                    v___x_3409_ = v___x_3406_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
                    v___x_3409_ = v_reuseFailAlloc_3410_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_NormCast_addInfer___boxed(
    mut v_decl_3412_: *mut LeanObject,
    mut v_kind_3413_: *mut LeanObject,
    mut v_prio_3414_: *mut LeanObject,
    mut v_a_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3420_: u8 = 0;
    let mut v_res_3421_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3420_ = (lean_unbox(v_kind_3413_) as u8);
    v_res_3421_ = l_Lean_Meta_NormCast_addInfer(
        v_decl_3412_,
        v_kind_boxed_3420_,
        v_prio_3414_,
        v_a_3415_,
        v_a_3416_,
        v_a_3417_,
        v_a_3418_,
    );
    lean_dec(v_a_3418_);
    lean_dec_ref(v_a_3417_);
    lean_dec(v_a_3416_);
    lean_dec_ref(v_a_3415_);
    return v_res_3421_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(
    mut v_00_u03b1_3422_: *mut LeanObject,
    mut v_constName_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
    mut v___y_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
    mut v___y_3427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    v___x_3429_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
    return v___x_3429_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___boxed(
    mut v_00_u03b1_3430_: *mut LeanObject,
    mut v_constName_3431_: *mut LeanObject,
    mut v___y_3432_: *mut LeanObject,
    mut v___y_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3437_: *mut LeanObject = core::ptr::null_mut();
    v_res_3437_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(v_00_u03b1_3430_, v_constName_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
    lean_dec(v___y_3435_);
    lean_dec_ref(v___y_3434_);
    lean_dec(v___y_3433_);
    lean_dec_ref(v___y_3432_);
    return v_res_3437_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3438_: *mut LeanObject,
    mut v_ref_3439_: *mut LeanObject,
    mut v_constName_3440_: *mut LeanObject,
    mut v___y_3441_: *mut LeanObject,
    mut v___y_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3446_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_3439_, v_constName_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
    return v___x_3446_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3447_: *mut LeanObject,
    mut v_ref_3448_: *mut LeanObject,
    mut v_constName_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3455_: *mut LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(v_00_u03b1_3447_, v_ref_3448_, v_constName_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
    lean_dec(v___y_3453_);
    lean_dec_ref(v___y_3452_);
    lean_dec(v___y_3451_);
    lean_dec_ref(v___y_3450_);
    lean_dec(v_ref_3448_);
    return v_res_3455_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3456_: *mut LeanObject,
    mut v_ref_3457_: *mut LeanObject,
    mut v_msg_3458_: *mut LeanObject,
    mut v_declHint_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
    mut v___y_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    v___x_3465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3457_, v_msg_3458_, v_declHint_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
    return v___x_3465_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_3466_: *mut LeanObject,
    mut v_ref_3467_: *mut LeanObject,
    mut v_msg_3468_: *mut LeanObject,
    mut v_declHint_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3475_: *mut LeanObject = core::ptr::null_mut();
    v_res_3475_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3466_, v_ref_3467_, v_msg_3468_, v_declHint_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
    lean_dec(v___y_3473_);
    lean_dec_ref(v___y_3472_);
    lean_dec(v___y_3471_);
    lean_dec_ref(v___y_3470_);
    lean_dec(v_ref_3467_);
    return v_res_3475_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3476_: *mut LeanObject,
    mut v_declHint_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    v___x_3483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3476_, v_declHint_3477_, v___y_3481_);
    return v___x_3483_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3484_: *mut LeanObject,
    mut v_declHint_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
    mut v___y_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3491_: *mut LeanObject = core::ptr::null_mut();
    v_res_3491_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3484_, v_declHint_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
    lean_dec(v___y_3489_);
    lean_dec_ref(v___y_3488_);
    lean_dec(v___y_3487_);
    lean_dec_ref(v___y_3486_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_3492_: *mut LeanObject,
    mut v_ref_3493_: *mut LeanObject,
    mut v_msg_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    v___x_3500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3493_, v_msg_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
    return v___x_3500_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_3501_: *mut LeanObject,
    mut v_ref_3502_: *mut LeanObject,
    mut v_msg_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
    mut v___y_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3509_: *mut LeanObject = core::ptr::null_mut();
    v_res_3509_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3501_, v_ref_3502_, v_msg_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
    lean_dec(v___y_3507_);
    lean_dec_ref(v___y_3506_);
    lean_dec(v___y_3505_);
    lean_dec_ref(v___y_3504_);
    lean_dec(v_ref_3502_);
    return v_res_3509_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(
    mut v_msg_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281__overap_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    v___f_3517_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0;
    v___x_1281__overap_3518_ = lean_panic_fn_borrowed(v___f_3517_, v_msg_3511_);
    lean_inc(v___y_3515_);
    lean_inc_ref(v___y_3514_);
    lean_inc(v___y_3513_);
    lean_inc_ref(v___y_3512_);
    v___x_3519_ = lean_apply_5(
        v___x_1281__overap_3518_,
        v___y_3512_,
        v___y_3513_,
        v___y_3514_,
        v___y_3515_,
        lean_box(0),
    );
    return v___x_3519_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___boxed(
    mut v_msg_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3526_: *mut LeanObject = core::ptr::null_mut();
    v_res_3526_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v_msg_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
    lean_dec(v___y_3524_);
    lean_dec_ref(v___y_3523_);
    lean_dec(v___y_3522_);
    lean_dec_ref(v___y_3521_);
    return v_res_3526_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    v___x_3532_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3533_ = lean_unsigned_to_nat(11);
    v___x_3534_ = lean_unsigned_to_nat(165);
    v___x_3535_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3536_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3537_ = l_mkPanicMessageWithDecl(
        v___x_3536_,
        v___x_3535_,
        v___x_3534_,
        v___x_3533_,
        v___x_3532_,
    );
    return v___x_3537_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    v___x_3538_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3539_ = lean_unsigned_to_nat(71);
    v___x_3540_ = lean_unsigned_to_nat(158);
    v___x_3541_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3542_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3543_ = l_mkPanicMessageWithDecl(
        v___x_3542_,
        v___x_3541_,
        v___x_3540_,
        v___x_3539_,
        v___x_3538_,
    );
    return v___x_3543_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(
    mut v_decl_3544_: *mut LeanObject,
    mut v_kind_3545_: u8,
    mut v_stx_3546_: *mut LeanObject,
    mut v___x_3547_: *mut LeanObject,
    mut v___x_3548_: *mut LeanObject,
    mut v___x_3549_: *mut LeanObject,
    mut v_x_3550_: *mut LeanObject,
    mut v_label_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3585_ = l_Lean_Syntax_getArg(v_stx_3546_, v___x_3547_);
                v___x_3586_ = l_Lean_Syntax_isNone(v___x_3585_);
                if v___x_3586_ == 0 {
                    lean_inc(v___x_3585_);
                    v___x_3587_ = l_Lean_Syntax_matchesNull(v___x_3585_, v___x_3548_);
                    if v___x_3587_ == 0 {
                        lean_dec(v___x_3585_);
                        lean_dec(v_decl_3544_);
                        v___x_3588_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                        v___x_3589_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_3588_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
                        return v___x_3589_;
                    } else {
                        v_prio_3590_ = l_Lean_Syntax_getArg(v___x_3585_, v___x_3549_);
                        lean_dec(v___x_3585_);
                        v___x_3591_ = l_Lean_Syntax_isNatLit_x3f(v_prio_3590_);
                        lean_dec(v_prio_3590_);
                        if lean_obj_tag(v___x_3591_) == 0 {
                            v___y_3580_ = v___y_3552_;
                            v___y_3581_ = v___y_3553_;
                            v___y_3582_ = v___y_3555_;
                            v___y_3583_ = v___y_3554_;
                            state = 2;
                            continue;
                        } else {
                            v_val_3592_ = lean_ctor_get(v___x_3591_, 0);
                            lean_inc(v_val_3592_);
                            lean_dec_ref_known(v___x_3591_, 1);
                            v___y_3558_ = v___y_3552_;
                            v___y_3559_ = v___y_3555_;
                            v___y_3560_ = v___y_3553_;
                            v___y_3561_ = v___y_3554_;
                            v___y_3562_ = v_val_3592_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3585_);
                    v___y_3580_ = v___y_3552_;
                    v___y_3581_ = v___y_3553_;
                    v___y_3582_ = v___y_3555_;
                    v___y_3583_ = v___y_3554_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_label_3551_) == 0 {
                    v___x_3563_ = l_Lean_Meta_NormCast_addInfer(
                        v_decl_3544_,
                        v_kind_3545_,
                        v___y_3562_,
                        v___y_3558_,
                        v___y_3560_,
                        v___y_3561_,
                        v___y_3559_,
                    );
                    return v___x_3563_;
                } else {
                    v_val_3564_ = lean_ctor_get(v_label_3551_, 0);
                    v___x_3565_ = l_Lean_Syntax_isStrLit_x3f(v_val_3564_);
                    if lean_obj_tag(v___x_3565_) == 0 {
                        v___x_3566_ = l_Lean_Meta_NormCast_addInfer(
                            v_decl_3544_,
                            v_kind_3545_,
                            v___y_3562_,
                            v___y_3558_,
                            v___y_3560_,
                            v___y_3561_,
                            v___y_3559_,
                        );
                        return v___x_3566_;
                    } else {
                        v_val_3567_ = lean_ctor_get(v___x_3565_, 0);
                        lean_inc(v_val_3567_);
                        lean_dec_ref_known(v___x_3565_, 1);
                        v___x_3568_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
                        v___x_3569_ = lean_string_dec_eq(v_val_3567_, v___x_3568_);
                        if v___x_3569_ == 0 {
                            v___x_3570_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
                            v___x_3571_ = lean_string_dec_eq(v_val_3567_, v___x_3570_);
                            if v___x_3571_ == 0 {
                                v___x_3572_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
                                v___x_3573_ = lean_string_dec_eq(v_val_3567_, v___x_3572_);
                                lean_dec(v_val_3567_);
                                if v___x_3573_ == 0 {
                                    lean_dec(v___y_3562_);
                                    lean_dec(v_decl_3544_);
                                    v___x_3574_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                                    v___x_3575_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_3574_, v___y_3558_, v___y_3560_, v___y_3561_, v___y_3559_);
                                    return v___x_3575_;
                                } else {
                                    v___x_3576_ = l_Lean_Meta_NormCast_addSquash(
                                        v_decl_3544_,
                                        v_kind_3545_,
                                        v___y_3562_,
                                        v___y_3558_,
                                        v___y_3560_,
                                        v___y_3561_,
                                        v___y_3559_,
                                    );
                                    return v___x_3576_;
                                }
                            } else {
                                lean_dec(v_val_3567_);
                                v___x_3577_ = l_Lean_Meta_NormCast_addMove(
                                    v_decl_3544_,
                                    v_kind_3545_,
                                    v___y_3562_,
                                    v___y_3558_,
                                    v___y_3560_,
                                    v___y_3561_,
                                    v___y_3559_,
                                );
                                return v___x_3577_;
                            }
                        } else {
                            lean_dec(v_val_3567_);
                            v___x_3578_ = l_Lean_Meta_NormCast_addElim(
                                v_decl_3544_,
                                v_kind_3545_,
                                v___y_3562_,
                                v___y_3558_,
                                v___y_3560_,
                                v___y_3561_,
                                v___y_3559_,
                            );
                            return v___x_3578_;
                        }
                    }
                }
            }
            2 => {
                v___x_3584_ = lean_unsigned_to_nat(1000);
                v___y_3558_ = v___y_3580_;
                v___y_3559_ = v___y_3582_;
                v___y_3560_ = v___y_3581_;
                v___y_3561_ = v___y_3583_;
                v___y_3562_ = v___x_3584_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(
    mut v_decl_3593_: *mut LeanObject,
    mut v_kind_3594_: *mut LeanObject,
    mut v_stx_3595_: *mut LeanObject,
    mut v___x_3596_: *mut LeanObject,
    mut v___x_3597_: *mut LeanObject,
    mut v___x_3598_: *mut LeanObject,
    mut v_x_3599_: *mut LeanObject,
    mut v_label_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
    mut v___y_3603_: *mut LeanObject,
    mut v___y_3604_: *mut LeanObject,
    mut v___y_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3606_: u8 = 0;
    let mut v_res_3607_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3606_ = (lean_unbox(v_kind_3594_) as u8);
    v_res_3607_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_3593_, v_kind_boxed_3606_, v_stx_3595_, v___x_3596_, v___x_3597_, v___x_3598_, v_x_3599_, v_label_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
    lean_dec(v___y_3604_);
    lean_dec_ref(v___y_3603_);
    lean_dec(v___y_3602_);
    lean_dec_ref(v___y_3601_);
    lean_dec(v_label_3600_);
    lean_dec(v___x_3598_);
    lean_dec(v___x_3597_);
    lean_dec(v___x_3596_);
    lean_dec(v_stx_3595_);
    return v_res_3607_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: u64 = 0;
    v___x_3614_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3614_);
    return v___x_3615_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3616_: u64 = 0;
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    v___x_3616_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
    v___x_3617_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3618_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_3618_, 0, v___x_3617_);
    lean_ctor_set_uint64(
        v___x_3618_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3616_,
    );
    return v___x_3618_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    v___x_3619_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3619_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    v___x_3620_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
    v___x_3621_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3621_, 0, v___x_3620_);
    return v___x_3621_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    v___x_3622_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
    v___x_3623_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3623_, 0, v___x_3622_);
    lean_ctor_set(v___x_3623_, 1, v___x_3622_);
    lean_ctor_set(v___x_3623_, 2, v___x_3622_);
    lean_ctor_set(v___x_3623_, 3, v___x_3622_);
    lean_ctor_set(v___x_3623_, 4, v___x_3622_);
    lean_ctor_set(v___x_3623_, 5, v___x_3622_);
    return v___x_3623_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    v___x_3624_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
    v___x_3625_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3625_, 0, v___x_3624_);
    lean_ctor_set(v___x_3625_, 1, v___x_3624_);
    lean_ctor_set(v___x_3625_, 2, v___x_3624_);
    lean_ctor_set(v___x_3625_, 3, v___x_3624_);
    lean_ctor_set(v___x_3625_, 4, v___x_3624_);
    return v___x_3625_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(
    mut v___x_3629_: *mut LeanObject,
    mut v___x_3630_: *mut LeanObject,
    mut v___x_3631_: *mut LeanObject,
    mut v___x_3632_: *mut LeanObject,
    mut v___x_3633_: *mut LeanObject,
    mut v_decl_3634_: *mut LeanObject,
    mut v_stx_3635_: *mut LeanObject,
    mut v_kind_3636_: u8,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3640_: u8 = 0;
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: usize = 0;
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    let mut v___x_3679_: u8 = 0;
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_label_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: u8 = 0;
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3640_ = 1;
                v___x_3641_ = 0;
                v___x_3642_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                v___x_3643_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                v___x_3644_ = lean_unsigned_to_nat(32);
                v___x_3645_ = lean_mk_empty_array_with_capacity(v___x_3644_);
                v___x_3646_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                v___x_3647_ = 5usize;
                lean_inc_n(v___x_3629_, 7);
                v___x_3648_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_3648_, 0, v___x_3646_);
                lean_ctor_set(v___x_3648_, 1, v___x_3645_);
                lean_ctor_set(v___x_3648_, 2, v___x_3629_);
                lean_ctor_set(v___x_3648_, 3, v___x_3629_);
                lean_ctor_set_usize(v___x_3648_, 4, v___x_3647_);
                v___x_3649_ = lean_box(1);
                lean_inc_ref(v___x_3648_);
                v___x_3650_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3650_, 0, v___x_3643_);
                lean_ctor_set(v___x_3650_, 1, v___x_3648_);
                lean_ctor_set(v___x_3650_, 2, v___x_3649_);
                v___x_3651_ = lean_mk_empty_array_with_capacity(v___x_3629_);
                v___x_3652_ = lean_box(0);
                lean_inc(v___x_3630_);
                v___x_3653_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_3653_, 0, v___x_3642_);
                lean_ctor_set(v___x_3653_, 1, v___x_3630_);
                lean_ctor_set(v___x_3653_, 2, v___x_3650_);
                lean_ctor_set(v___x_3653_, 3, v___x_3651_);
                lean_ctor_set(v___x_3653_, 4, v___x_3652_);
                lean_ctor_set(v___x_3653_, 5, v___x_3629_);
                lean_ctor_set(v___x_3653_, 6, v___x_3652_);
                lean_ctor_set_uint8(
                    v___x_3653_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_3641_,
                );
                lean_ctor_set_uint8(
                    v___x_3653_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_3641_,
                );
                lean_ctor_set_uint8(
                    v___x_3653_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_3641_,
                );
                lean_ctor_set_uint8(
                    v___x_3653_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_3640_,
                );
                v___x_3654_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_3654_, 0, v___x_3629_);
                lean_ctor_set(v___x_3654_, 1, v___x_3629_);
                lean_ctor_set(v___x_3654_, 2, v___x_3629_);
                lean_ctor_set(v___x_3654_, 3, v___x_3629_);
                lean_ctor_set(v___x_3654_, 4, v___x_3643_);
                lean_ctor_set(v___x_3654_, 5, v___x_3643_);
                lean_ctor_set(v___x_3654_, 6, v___x_3643_);
                lean_ctor_set(v___x_3654_, 7, v___x_3643_);
                lean_ctor_set(v___x_3654_, 8, v___x_3643_);
                lean_ctor_set(v___x_3654_, 9, v___x_3643_);
                v___x_3655_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                v___x_3656_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                v___x_3657_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3657_, 0, v___x_3654_);
                lean_ctor_set(v___x_3657_, 1, v___x_3655_);
                lean_ctor_set(v___x_3657_, 2, v___x_3630_);
                lean_ctor_set(v___x_3657_, 3, v___x_3648_);
                lean_ctor_set(v___x_3657_, 4, v___x_3656_);
                v___x_3658_ = lean_st_mk_ref(v___x_3657_);
                v___x_3670_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
                v___x_3671_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
                lean_inc_ref(v___x_3631_);
                v___x_3672_ =
                    l_Lean_Name_mkStr4(v___x_3631_, v___x_3670_, v___x_3671_, v___x_3632_);
                lean_inc(v_stx_3635_);
                v___x_3673_ = l_Lean_Syntax_isOfKind(v_stx_3635_, v___x_3672_);
                lean_dec(v___x_3672_);
                if v___x_3673_ == 0 {
                    lean_dec(v_stx_3635_);
                    lean_dec(v_decl_3634_);
                    lean_dec_ref(v___x_3631_);
                    lean_dec(v___x_3629_);
                    v___x_3674_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                    v___x_3675_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_3674_, v___x_3653_, v___x_3658_, v___y_3637_, v___y_3638_);
                    lean_dec_ref_known(v___x_3653_, 7);
                    v___y_3660_ = v___x_3675_;
                    state = 1;
                    continue;
                } else {
                    v___x_3676_ = lean_unsigned_to_nat(1);
                    v___x_3677_ = l_Lean_Syntax_getArg(v_stx_3635_, v___x_3676_);
                    v___x_3678_ = l_Lean_Syntax_isNone(v___x_3677_);
                    if v___x_3678_ == 0 {
                        lean_inc(v___x_3677_);
                        v___x_3679_ = l_Lean_Syntax_matchesNull(v___x_3677_, v___x_3676_);
                        if v___x_3679_ == 0 {
                            lean_dec(v___x_3677_);
                            lean_dec(v_stx_3635_);
                            lean_dec(v_decl_3634_);
                            lean_dec_ref(v___x_3631_);
                            lean_dec(v___x_3629_);
                            v___x_3680_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                            v___x_3681_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_3680_, v___x_3653_, v___x_3658_, v___y_3637_, v___y_3638_);
                            lean_dec_ref_known(v___x_3653_, 7);
                            v___y_3660_ = v___x_3681_;
                            state = 1;
                            continue;
                        } else {
                            v_label_3682_ = l_Lean_Syntax_getArg(v___x_3677_, v___x_3629_);
                            lean_dec(v___x_3677_);
                            v___x_3683_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
                            v___x_3684_ = l_Lean_Name_mkStr4(
                                v___x_3631_,
                                v___x_3670_,
                                v___x_3671_,
                                v___x_3683_,
                            );
                            lean_inc(v_label_3682_);
                            v___x_3685_ = l_Lean_Syntax_isOfKind(v_label_3682_, v___x_3684_);
                            lean_dec(v___x_3684_);
                            if v___x_3685_ == 0 {
                                lean_dec(v_label_3682_);
                                lean_dec(v_stx_3635_);
                                lean_dec(v_decl_3634_);
                                lean_dec(v___x_3629_);
                                v___x_3686_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
                                v___x_3687_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_3686_, v___x_3653_, v___x_3658_, v___y_3637_, v___y_3638_);
                                lean_dec_ref_known(v___x_3653_, 7);
                                v___y_3660_ = v___x_3687_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3688_ = lean_box(0);
                                v___x_3689_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3689_, 0, v_label_3682_);
                                v___x_3690_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_3634_, v_kind_3636_, v_stx_3635_, v___x_3633_, v___x_3676_, v___x_3629_, v___x_3688_, v___x_3689_, v___x_3653_, v___x_3658_, v___y_3637_, v___y_3638_);
                                lean_dec_ref_known(v___x_3653_, 7);
                                lean_dec_ref_known(v___x_3689_, 1);
                                lean_dec(v___x_3629_);
                                lean_dec(v_stx_3635_);
                                v___y_3660_ = v___x_3690_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3677_);
                        lean_dec_ref(v___x_3631_);
                        v___x_3691_ = lean_box(0);
                        v___x_3692_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_3634_, v_kind_3636_, v_stx_3635_, v___x_3633_, v___x_3676_, v___x_3629_, v___x_3691_, v___x_3652_, v___x_3653_, v___x_3658_, v___y_3637_, v___y_3638_);
                        lean_dec_ref_known(v___x_3653_, 7);
                        lean_dec(v___x_3629_);
                        lean_dec(v_stx_3635_);
                        v___y_3660_ = v___x_3692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_3660_) == 0 {
                    v_a_3661_ = lean_ctor_get(v___y_3660_, 0);
                    v_isSharedCheck_3669_ = (!lean_is_exclusive(v___y_3660_)) as u8;
                    if v_isSharedCheck_3669_ == 0 {
                        v___x_3663_ = v___y_3660_;
                        v_isShared_3664_ = v_isSharedCheck_3669_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3661_);
                        lean_dec(v___y_3660_);
                        v___x_3663_ = lean_box(0);
                        v_isShared_3664_ = v_isSharedCheck_3669_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3658_);
                    return v___y_3660_;
                }
            }
            2 => {
                v___x_3665_ = lean_st_ref_get(v___x_3658_);
                lean_dec(v___x_3658_);
                lean_dec(v___x_3665_);
                if v_isShared_3664_ == 0 {
                    v___x_3667_ = v___x_3663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3661_);
                    v___x_3667_ = v_reuseFailAlloc_3668_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(
    mut v___x_3693_: *mut LeanObject,
    mut v___x_3694_: *mut LeanObject,
    mut v___x_3695_: *mut LeanObject,
    mut v___x_3696_: *mut LeanObject,
    mut v___x_3697_: *mut LeanObject,
    mut v_decl_3698_: *mut LeanObject,
    mut v_stx_3699_: *mut LeanObject,
    mut v_kind_3700_: *mut LeanObject,
    mut v___y_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3704_: u8 = 0;
    let mut v_res_3705_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3704_ = (lean_unbox(v_kind_3700_) as u8);
    v_res_3705_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_3693_, v___x_3694_, v___x_3695_, v___x_3696_, v___x_3697_, v_decl_3698_, v_stx_3699_, v_kind_boxed_3704_, v___y_3701_, v___y_3702_);
    lean_dec(v___y_3702_);
    lean_dec_ref(v___y_3701_);
    lean_dec(v___x_3697_);
    return v_res_3705_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(
    mut v_msgData_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    v___x_3710_ = lean_st_ref_get(v___y_3708_);
    v_env_3711_ = lean_ctor_get(v___x_3710_, 0);
    lean_inc_ref(v_env_3711_);
    lean_dec(v___x_3710_);
    v_options_3712_ = lean_ctor_get(v___y_3707_, 2);
    v___x_3713_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
    v___x_3714_ = lean_unsigned_to_nat(32);
    v___x_3715_ = lean_mk_empty_array_with_capacity(v___x_3714_);
    lean_dec_ref(v___x_3715_);
    v___x_3716_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
    lean_inc_ref(v_options_3712_);
    v___x_3717_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3717_, 0, v_env_3711_);
    lean_ctor_set(v___x_3717_, 1, v___x_3713_);
    lean_ctor_set(v___x_3717_, 2, v___x_3716_);
    lean_ctor_set(v___x_3717_, 3, v_options_3712_);
    v___x_3718_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3718_, 0, v___x_3717_);
    lean_ctor_set(v___x_3718_, 1, v_msgData_3706_);
    v___x_3719_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3719_, 0, v___x_3718_);
    return v___x_3719_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_msgData_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3724_: *mut LeanObject = core::ptr::null_mut();
    v_res_3724_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msgData_3720_, v___y_3721_, v___y_3722_);
    lean_dec(v___y_3722_);
    lean_dec_ref(v___y_3721_);
    return v_res_3724_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(
    mut v_msg_3725_: *mut LeanObject,
    mut v___y_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3734_: u8 = 0;
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3729_ = lean_ctor_get(v___y_3726_, 5);
                v___x_3730_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msg_3725_, v___y_3726_, v___y_3727_);
                v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
                v_isSharedCheck_3739_ = (!lean_is_exclusive(v___x_3730_)) as u8;
                if v_isSharedCheck_3739_ == 0 {
                    v___x_3733_ = v___x_3730_;
                    v_isShared_3734_ = v_isSharedCheck_3739_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3731_);
                    lean_dec(v___x_3730_);
                    v___x_3733_ = lean_box(0);
                    v_isShared_3734_ = v_isSharedCheck_3739_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3729_);
                v___x_3735_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3735_, 0, v_ref_3729_);
                lean_ctor_set(v___x_3735_, 1, v_a_3731_);
                if v_isShared_3734_ == 0 {
                    lean_ctor_set_tag(v___x_3733_, 1);
                    lean_ctor_set(v___x_3733_, 0, v___x_3735_);
                    v___x_3737_ = v___x_3733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3735_);
                    v___x_3737_ = v_reuseFailAlloc_3738_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_msg_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3744_: *mut LeanObject = core::ptr::null_mut();
    v_res_3744_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_3740_, v___y_3741_, v___y_3742_);
    lean_dec(v___y_3742_);
    lean_dec_ref(v___y_3741_);
    return v_res_3744_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    v___x_3746_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3747_ = l_Lean_stringToMessageData(v___x_3746_);
    return v___x_3747_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    v___x_3749_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3750_ = l_Lean_stringToMessageData(v___x_3749_);
    return v___x_3750_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(
    mut v___x_3751_: *mut LeanObject,
    mut v_decl_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    v___x_3756_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
    v___x_3757_ = l_Lean_MessageData_ofName(v___x_3751_);
    v___x_3758_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3758_, 0, v___x_3756_);
    lean_ctor_set(v___x_3758_, 1, v___x_3757_);
    v___x_3759_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
    v___x_3760_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3760_, 0, v___x_3758_);
    lean_ctor_set(v___x_3760_, 1, v___x_3759_);
    v___x_3761_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v___x_3760_, v___y_3753_, v___y_3754_);
    return v___x_3761_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(
    mut v___x_3762_: *mut LeanObject,
    mut v_decl_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3767_: *mut LeanObject = core::ptr::null_mut();
    v_res_3767_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_3762_, v_decl_3763_, v___y_3764_, v___y_3765_);
    lean_dec(v___y_3765_);
    lean_dec_ref(v___y_3764_);
    lean_dec(v_decl_3763_);
    return v_res_3767_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3853_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
    v___x_3854_ = l_Lean_registerBuiltinAttribute(v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(
    mut v_a_3855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3856_: *mut LeanObject = core::ptr::null_mut();
    v_res_3856_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_();
    return v_res_3856_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_3857_: *mut LeanObject,
    mut v_msg_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    v___x_3862_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_3858_, v___y_3859_, v___y_3860_);
    return v___x_3862_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_3863_: *mut LeanObject,
    mut v_msg_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
    mut v___y_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3868_: *mut LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(v_00_u03b1_3863_, v_msg_3864_, v___y_3865_, v___y_3866_);
    lean_dec(v___y_3866_);
    lean_dec_ref(v___y_3865_);
    return v_res_3868_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_NormCast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CoeAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_NormCast_instInhabitedLabel_default =
        _init_l_Lean_Meta_NormCast_instInhabitedLabel_default();
    l_Lean_Meta_NormCast_instInhabitedLabel = _init_l_Lean_Meta_NormCast_instInhabitedLabel();
    res = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_NormCast_pushCastExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_NormCast_pushCastExt);
    lean_dec_ref(res);
    l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default =
        _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default();
    lean_mark_persistent(l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default);
    l_Lean_Meta_NormCast_instInhabitedNormCastExtension =
        _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension();
    lean_mark_persistent(l_Lean_Meta_NormCast_instInhabitedNormCastExtension);
    res = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_NormCast_normCastExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_NormCast_normCastExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_NormCast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_NormCast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CoeAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_NormCast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_NormCast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_NormCast(builtin);
}

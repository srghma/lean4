// Lean compiler output
// Module: Lean.Meta.CongrTheorems
// Imports: Lean.AddDecl Lean.ReservedNameAction Lean.Structure Lean.Meta.Tactic.Subst Lean.Meta.FunInfo
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_isNat, l_String_Slice_toNat_x21};
use crate::r#gen::Init::Meta::Defs::{
    lean_name_append_after, lean_name_append_before, lean_name_append_index_after,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addDecl, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_levelParams;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_containsOnBranch, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_bindingBody_x21,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_bindingName_x21, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_replaceFVars, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_getFVar_x21, l_Lean_LocalContext_setBinderInfo,
    l_Lean_LocalContext_setUserName, l_Lean_LocalDecl_binderInfo, l_Lean_LocalDecl_fvarId,
    l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppM, l_Lean_Meta_mkAppM___boxed, l_Lean_Meta_mkEq, l_Lean_Meta_mkEq___boxed,
    l_Lean_Meta_mkEqNDRec, l_Lean_Meta_mkEqOfHEq, l_Lean_Meta_mkEqRec, l_Lean_Meta_mkEqRefl,
    l_Lean_Meta_mkHEq, l_Lean_Meta_mkHEqRefl,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instInhabitedParamInfo_default,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_realizeConst,
};
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, l_Lean_Meta_FunInfo_getArity, l_Lean_Meta_getFunInfo,
    runtime_initialize_Lean_Meta_FunInfo,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assert;
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::l_Lean_Meta_FVarSubst_find_x3f;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_intro1Core;
use crate::r#gen::Lean::Meta::Tactic::Subst::{
    initialize_Lean_Meta_Tactic_Subst, l_Lean_Meta_substCore,
    runtime_initialize_Lean_Meta_Tactic_Subst,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::{
    initialize_Lean_ReservedNameAction, l_Lean_executeReservedNameAction,
    l_Lean_registerReservedNameAction, runtime_initialize_Lean_ReservedNameAction,
};
use crate::r#gen::Lean::ResolveName::l_Lean_registerReservedNamePredicate;
use crate::r#gen::Lean::Structure::{
    initialize_Lean_Structure, l_Lean_isSubobjectField_x3f, runtime_initialize_Lean_Structure,
};
use crate::r#gen::Lean::Util::Recognizers::l_Lean_Expr_isHEq;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::{
    lean_expr_eqv, lean_expr_instantiate, lean_expr_instantiate1,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_5, lean_apply_6, lean_apply_7, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Lean_Meta_instInhabitedCongrArgKind_default: u8 = 0;
pub static mut l_Lean_Meta_instInhabitedCongrArgKind: u8 = 0;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 65, 114, 103, 75,
            105, 110, 100, 46, 102, 105, 120, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value: LeanStringObject<36> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 65, 114, 103, 75,
            105, 110, 100, 46, 102, 105, 120, 101, 100, 78, 111, 80, 97, 114, 97, 109, 0,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 65, 114, 103, 75,
            105, 110, 100, 46, 101, 113, 0,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value: LeanStringObject<28> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 65, 114, 103, 75,
            105, 110, 100, 46, 99, 97, 115, 116, 0,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 65, 114, 103, 75,
            105, 110, 100, 46, 104, 101, 113, 0,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value: LeanStringObject<40> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 65, 114, 103, 75,
            105, 110, 100, 46, 115, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 73, 110,
            115, 116, 0,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCongrArgKind_repr___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind_repr___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCongrArgKind_repr___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCongrArgKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprCongrArgKind_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprCongrArgKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReprCongrArgKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCongrArgKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instBEqCongrArgKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instBEqCongrArgKind_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instBEqCongrArgKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqCongrArgKind___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instBEqCongrArgKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqCongrArgKind___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [101, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value) as *mut LeanObject,18388690793488095770 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value) as *mut LeanObject,13589827700912665667 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0_value: LeanStringObject<47> =
    LeanStringObject {
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
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101,
            32, 96, 104, 99, 111, 110, 103, 114, 96, 32, 116, 104, 101, 111, 114, 101, 109, 58, 32,
            101, 120, 112, 101, 99, 116, 101, 100, 32, 0,
        ],
    };
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 44, 32, 98, 117, 116, 32, 103, 111,
            116, 32, 0,
        ],
    };
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 102, 111, 114, 0],
    };
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_getCongrSimpKinds___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_getCongrSimpKinds___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getCongrSimpKinds___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [83, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 105, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value) as *mut LeanObject,13409365605382521367 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value) as *mut LeanObject,15293707491349124431 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4_value) as *mut LeanObject;
pub static l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1_value: LeanStringObject<73> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 73, m_capacity: 73, m_length: 72, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 84, 104, 101, 111, 114, 101, 109, 115, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107, 67, 111, 110, 103, 114, 83, 105, 109, 112, 67, 111, 114, 101, 63, 46, 109, 107, 80, 114, 111, 111, 102, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value: LeanStringObject<69> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 103, 114, 84, 104, 101, 111, 114, 101, 109, 115, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107, 67, 111, 110, 103, 114, 83, 105, 109, 112, 67, 111, 114, 101, 63, 46, 109, 107, 63, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [101, 95, 0]};
static mut l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_hcongrThmSuffixBase___closed__0_value: LeanStringObject<7> =
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
        m_data: [104, 99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Meta_hcongrThmSuffixBase___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_hcongrThmSuffixBase___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_hcongrThmSuffixBase: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_hcongrThmSuffixBase___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [104, 99, 111, 110, 103, 114, 95, 0],
    };
static mut l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_hcongrThmSuffixBasePrefix: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_isHCongrReservedNameSuffix___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_congrSimpSuffix___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [99, 111, 110, 103, 114, 95, 115, 105, 109, 112, 0],
};
static mut l_Lean_Meta_congrSimpSuffix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_congrSimpSuffix___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_congrSimpSuffix: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_congrSimpSuffix___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,11699215918282396216 as *mut LeanObject] };
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,8100821273481874895 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 110, 103, 114, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,14478848213975949407 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,2153343399056149650 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,4831514804830874003 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,13631086748237910299 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,3136939006533871466 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,6898615515195644483 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,3058785846607944206 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,12253599094130766938 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,3954811660999597043 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 111, 110, 103, 114, 75, 105, 110, 100, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject,10322700006590711791 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 99, 108, 97, 114, 101, 100, 32, 96, 0]};
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value: LeanStringObject<
    37,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107, 72, 67, 111, 110, 103, 114, 87, 105,
        116, 104, 65, 114, 105, 116, 121, 70, 111, 114, 67, 111, 110, 115, 116, 63, 0,
    ],
};
static mut l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0_value: LeanStringObject<31> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107, 67, 111, 110, 103, 114, 83, 105,
            109, 112, 70, 111, 114, 67, 111, 110, 115, 116, 63, 0,
        ],
    };
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101,
            32, 96, 0,
        ],
    };
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2_value: LeanStringObject<3> =
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
        m_data: [96, 32, 0],
    };
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_CongrArgKind_ctorIdx(mut v_x_5125_: u8) -> *mut LeanObject {
    match v_x_5125_ {
        0 => {
            let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
            v___x_5126_ = lean_unsigned_to_nat(0);
            return v___x_5126_;
        }
        1 => {
            let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
            v___x_5127_ = lean_unsigned_to_nat(1);
            return v___x_5127_;
        }
        2 => {
            let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
            v___x_5128_ = lean_unsigned_to_nat(2);
            return v___x_5128_;
        }
        3 => {
            let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
            v___x_5129_ = lean_unsigned_to_nat(3);
            return v___x_5129_;
        }
        4 => {
            let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
            v___x_5130_ = lean_unsigned_to_nat(4);
            return v___x_5130_;
        }
        _ => {
            let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
            v___x_5131_ = lean_unsigned_to_nat(5);
            return v___x_5131_;
        }
    }
}
pub unsafe fn l_Lean_Meta_CongrArgKind_ctorIdx___boxed(
    mut v_x_5132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_5133_: u8 = 0;
    let mut v_res_5134_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_5133_ = (lean_unbox(v_x_5132_) as u8);
    v_res_5134_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_x_boxed_5133_);
    return v_res_5134_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_toCtorIdx(mut v_x_5135_: u8) -> *mut LeanObject {
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    v___x_5136_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_x_5135_);
    return v___x_5136_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_toCtorIdx___boxed(
    mut v_x_5137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_5138_: u8 = 0;
    let mut v_res_5139_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_5138_ = (lean_unbox(v_x_5137_) as u8);
    v_res_5139_ = l_Lean_Meta_CongrArgKind_toCtorIdx(v_x_4__boxed_5138_);
    return v_res_5139_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_ctorElim___redArg(
    mut v_k_5140_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5140_);
    return v_k_5140_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_ctorElim___redArg___boxed(
    mut v_k_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5142_: *mut LeanObject = core::ptr::null_mut();
    v_res_5142_ = l_Lean_Meta_CongrArgKind_ctorElim___redArg(v_k_5141_);
    lean_dec(v_k_5141_);
    return v_res_5142_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_ctorElim(
    mut v_motive_5143_: *mut LeanObject,
    mut v_ctorIdx_5144_: *mut LeanObject,
    mut v_t_5145_: u8,
    mut v_h_5146_: *mut LeanObject,
    mut v_k_5147_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5147_);
    return v_k_5147_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_ctorElim___boxed(
    mut v_motive_5148_: *mut LeanObject,
    mut v_ctorIdx_5149_: *mut LeanObject,
    mut v_t_5150_: *mut LeanObject,
    mut v_h_5151_: *mut LeanObject,
    mut v_k_5152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5153_: u8 = 0;
    let mut v_res_5154_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5153_ = (lean_unbox(v_t_5150_) as u8);
    v_res_5154_ = l_Lean_Meta_CongrArgKind_ctorElim(
        v_motive_5148_,
        v_ctorIdx_5149_,
        v_t_boxed_5153_,
        v_h_5151_,
        v_k_5152_,
    );
    lean_dec(v_k_5152_);
    lean_dec(v_ctorIdx_5149_);
    return v_res_5154_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixed_elim___redArg(
    mut v_fixed_5155_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fixed_5155_);
    return v_fixed_5155_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixed_elim___redArg___boxed(
    mut v_fixed_5156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5157_: *mut LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Lean_Meta_CongrArgKind_fixed_elim___redArg(v_fixed_5156_);
    lean_dec(v_fixed_5156_);
    return v_res_5157_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixed_elim(
    mut v_motive_5158_: *mut LeanObject,
    mut v_t_5159_: u8,
    mut v_h_5160_: *mut LeanObject,
    mut v_fixed_5161_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fixed_5161_);
    return v_fixed_5161_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixed_elim___boxed(
    mut v_motive_5162_: *mut LeanObject,
    mut v_t_5163_: *mut LeanObject,
    mut v_h_5164_: *mut LeanObject,
    mut v_fixed_5165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5166_: u8 = 0;
    let mut v_res_5167_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5166_ = (lean_unbox(v_t_5163_) as u8);
    v_res_5167_ = l_Lean_Meta_CongrArgKind_fixed_elim(
        v_motive_5162_,
        v_t_boxed_5166_,
        v_h_5164_,
        v_fixed_5165_,
    );
    lean_dec(v_fixed_5165_);
    return v_res_5167_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(
    mut v_fixedNoParam_5168_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fixedNoParam_5168_);
    return v_fixedNoParam_5168_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg___boxed(
    mut v_fixedNoParam_5169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5170_: *mut LeanObject = core::ptr::null_mut();
    v_res_5170_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(v_fixedNoParam_5169_);
    lean_dec(v_fixedNoParam_5169_);
    return v_res_5170_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixedNoParam_elim(
    mut v_motive_5171_: *mut LeanObject,
    mut v_t_5172_: u8,
    mut v_h_5173_: *mut LeanObject,
    mut v_fixedNoParam_5174_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fixedNoParam_5174_);
    return v_fixedNoParam_5174_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_fixedNoParam_elim___boxed(
    mut v_motive_5175_: *mut LeanObject,
    mut v_t_5176_: *mut LeanObject,
    mut v_h_5177_: *mut LeanObject,
    mut v_fixedNoParam_5178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5179_: u8 = 0;
    let mut v_res_5180_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5179_ = (lean_unbox(v_t_5176_) as u8);
    v_res_5180_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim(
        v_motive_5175_,
        v_t_boxed_5179_,
        v_h_5177_,
        v_fixedNoParam_5178_,
    );
    lean_dec(v_fixedNoParam_5178_);
    return v_res_5180_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_eq_elim___redArg(
    mut v_eq_5181_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eq_5181_);
    return v_eq_5181_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_eq_elim___redArg___boxed(
    mut v_eq_5182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5183_: *mut LeanObject = core::ptr::null_mut();
    v_res_5183_ = l_Lean_Meta_CongrArgKind_eq_elim___redArg(v_eq_5182_);
    lean_dec(v_eq_5182_);
    return v_res_5183_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_eq_elim(
    mut v_motive_5184_: *mut LeanObject,
    mut v_t_5185_: u8,
    mut v_h_5186_: *mut LeanObject,
    mut v_eq_5187_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eq_5187_);
    return v_eq_5187_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_eq_elim___boxed(
    mut v_motive_5188_: *mut LeanObject,
    mut v_t_5189_: *mut LeanObject,
    mut v_h_5190_: *mut LeanObject,
    mut v_eq_5191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5192_: u8 = 0;
    let mut v_res_5193_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5192_ = (lean_unbox(v_t_5189_) as u8);
    v_res_5193_ =
        l_Lean_Meta_CongrArgKind_eq_elim(v_motive_5188_, v_t_boxed_5192_, v_h_5190_, v_eq_5191_);
    lean_dec(v_eq_5191_);
    return v_res_5193_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_cast_elim___redArg(
    mut v_cast_5194_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_cast_5194_);
    return v_cast_5194_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_cast_elim___redArg___boxed(
    mut v_cast_5195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5196_: *mut LeanObject = core::ptr::null_mut();
    v_res_5196_ = l_Lean_Meta_CongrArgKind_cast_elim___redArg(v_cast_5195_);
    lean_dec(v_cast_5195_);
    return v_res_5196_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_cast_elim(
    mut v_motive_5197_: *mut LeanObject,
    mut v_t_5198_: u8,
    mut v_h_5199_: *mut LeanObject,
    mut v_cast_5200_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_cast_5200_);
    return v_cast_5200_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_cast_elim___boxed(
    mut v_motive_5201_: *mut LeanObject,
    mut v_t_5202_: *mut LeanObject,
    mut v_h_5203_: *mut LeanObject,
    mut v_cast_5204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5205_: u8 = 0;
    let mut v_res_5206_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5205_ = (lean_unbox(v_t_5202_) as u8);
    v_res_5206_ = l_Lean_Meta_CongrArgKind_cast_elim(
        v_motive_5201_,
        v_t_boxed_5205_,
        v_h_5203_,
        v_cast_5204_,
    );
    lean_dec(v_cast_5204_);
    return v_res_5206_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_heq_elim___redArg(
    mut v_heq_5207_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_heq_5207_);
    return v_heq_5207_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_heq_elim___redArg___boxed(
    mut v_heq_5208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5209_: *mut LeanObject = core::ptr::null_mut();
    v_res_5209_ = l_Lean_Meta_CongrArgKind_heq_elim___redArg(v_heq_5208_);
    lean_dec(v_heq_5208_);
    return v_res_5209_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_heq_elim(
    mut v_motive_5210_: *mut LeanObject,
    mut v_t_5211_: u8,
    mut v_h_5212_: *mut LeanObject,
    mut v_heq_5213_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_heq_5213_);
    return v_heq_5213_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_heq_elim___boxed(
    mut v_motive_5214_: *mut LeanObject,
    mut v_t_5215_: *mut LeanObject,
    mut v_h_5216_: *mut LeanObject,
    mut v_heq_5217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5218_: u8 = 0;
    let mut v_res_5219_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5218_ = (lean_unbox(v_t_5215_) as u8);
    v_res_5219_ =
        l_Lean_Meta_CongrArgKind_heq_elim(v_motive_5214_, v_t_boxed_5218_, v_h_5216_, v_heq_5217_);
    lean_dec(v_heq_5217_);
    return v_res_5219_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(
    mut v_subsingletonInst_5220_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_subsingletonInst_5220_);
    return v_subsingletonInst_5220_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg___boxed(
    mut v_subsingletonInst_5221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5222_: *mut LeanObject = core::ptr::null_mut();
    v_res_5222_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(v_subsingletonInst_5221_);
    lean_dec(v_subsingletonInst_5221_);
    return v_res_5222_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_subsingletonInst_elim(
    mut v_motive_5223_: *mut LeanObject,
    mut v_t_5224_: u8,
    mut v_h_5225_: *mut LeanObject,
    mut v_subsingletonInst_5226_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_subsingletonInst_5226_);
    return v_subsingletonInst_5226_;
}
pub unsafe fn l_Lean_Meta_CongrArgKind_subsingletonInst_elim___boxed(
    mut v_motive_5227_: *mut LeanObject,
    mut v_t_5228_: *mut LeanObject,
    mut v_h_5229_: *mut LeanObject,
    mut v_subsingletonInst_5230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5231_: u8 = 0;
    let mut v_res_5232_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5231_ = (lean_unbox(v_t_5228_) as u8);
    v_res_5232_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim(
        v_motive_5227_,
        v_t_boxed_5231_,
        v_h_5229_,
        v_subsingletonInst_5230_,
    );
    lean_dec(v_subsingletonInst_5230_);
    return v_res_5232_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCongrArgKind_default() -> u8 {
    let mut v___x_5233_: u8 = 0;
    v___x_5233_ = 0;
    return v___x_5233_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCongrArgKind() -> u8 {
    let mut v___x_5234_: u8 = 0;
    v___x_5234_ = 0;
    return v___x_5234_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12() -> *mut LeanObject {
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    v___x_5253_ = lean_unsigned_to_nat(2);
    v___x_5254_ = lean_nat_to_int(v___x_5253_);
    return v___x_5254_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13() -> *mut LeanObject {
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    v___x_5255_ = lean_unsigned_to_nat(1);
    v___x_5256_ = lean_nat_to_int(v___x_5255_);
    return v___x_5256_;
}
pub unsafe fn l_Lean_Meta_instReprCongrArgKind_repr(
    mut v_x_5257_: u8,
    mut v_prec_5258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: u8 = 0;
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: u8 = 0;
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: u8 = 0;
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: u8 = 0;
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: u8 = 0;
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: u8 = 0;
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: u8 = 0;
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: u8 = 0;
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: u8 = 0;
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: u8 = 0;
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_5257_ {
                0 => {
                    v___x_5301_ = lean_unsigned_to_nat(1024);
                    v___x_5302_ = lean_nat_dec_le(v___x_5301_, v_prec_5258_);
                    if v___x_5302_ == 0 {
                        v___x_5303_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12,
                        );
                        v___y_5260_ = v___x_5303_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5304_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13,
                        );
                        v___y_5260_ = v___x_5304_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_5305_ = lean_unsigned_to_nat(1024);
                    v___x_5306_ = lean_nat_dec_le(v___x_5305_, v_prec_5258_);
                    if v___x_5306_ == 0 {
                        v___x_5307_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12,
                        );
                        v___y_5267_ = v___x_5307_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5308_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13,
                        );
                        v___y_5267_ = v___x_5308_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_5309_ = lean_unsigned_to_nat(1024);
                    v___x_5310_ = lean_nat_dec_le(v___x_5309_, v_prec_5258_);
                    if v___x_5310_ == 0 {
                        v___x_5311_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12,
                        );
                        v___y_5274_ = v___x_5311_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5312_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13,
                        );
                        v___y_5274_ = v___x_5312_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_5313_ = lean_unsigned_to_nat(1024);
                    v___x_5314_ = lean_nat_dec_le(v___x_5313_, v_prec_5258_);
                    if v___x_5314_ == 0 {
                        v___x_5315_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12,
                        );
                        v___y_5281_ = v___x_5315_;
                        state = 4;
                        continue;
                    } else {
                        v___x_5316_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13,
                        );
                        v___y_5281_ = v___x_5316_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v___x_5317_ = lean_unsigned_to_nat(1024);
                    v___x_5318_ = lean_nat_dec_le(v___x_5317_, v_prec_5258_);
                    if v___x_5318_ == 0 {
                        v___x_5319_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12,
                        );
                        v___y_5288_ = v___x_5319_;
                        state = 5;
                        continue;
                    } else {
                        v___x_5320_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13,
                        );
                        v___y_5288_ = v___x_5320_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v___x_5321_ = lean_unsigned_to_nat(1024);
                    v___x_5322_ = lean_nat_dec_le(v___x_5321_, v_prec_5258_);
                    if v___x_5322_ == 0 {
                        v___x_5323_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12,
                        );
                        v___y_5295_ = v___x_5323_;
                        state = 6;
                        continue;
                    } else {
                        v___x_5324_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once
                            ),
                            _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13,
                        );
                        v___y_5295_ = v___x_5324_;
                        state = 6;
                        continue;
                    }
                }
            },
            1 => {
                v___x_5261_ = l_Lean_Meta_instReprCongrArgKind_repr___closed__1;
                lean_inc(v___y_5260_);
                v___x_5262_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5262_, 0, v___y_5260_);
                lean_ctor_set(v___x_5262_, 1, v___x_5261_);
                v___x_5263_ = 0;
                v___x_5264_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5264_, 0, v___x_5262_);
                lean_ctor_set_uint8(
                    v___x_5264_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5263_,
                );
                v___x_5265_ = l_Repr_addAppParen(v___x_5264_, v_prec_5258_);
                return v___x_5265_;
            }
            2 => {
                v___x_5268_ = l_Lean_Meta_instReprCongrArgKind_repr___closed__3;
                lean_inc(v___y_5267_);
                v___x_5269_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5269_, 0, v___y_5267_);
                lean_ctor_set(v___x_5269_, 1, v___x_5268_);
                v___x_5270_ = 0;
                v___x_5271_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5271_, 0, v___x_5269_);
                lean_ctor_set_uint8(
                    v___x_5271_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5270_,
                );
                v___x_5272_ = l_Repr_addAppParen(v___x_5271_, v_prec_5258_);
                return v___x_5272_;
            }
            3 => {
                v___x_5275_ = l_Lean_Meta_instReprCongrArgKind_repr___closed__5;
                lean_inc(v___y_5274_);
                v___x_5276_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5276_, 0, v___y_5274_);
                lean_ctor_set(v___x_5276_, 1, v___x_5275_);
                v___x_5277_ = 0;
                v___x_5278_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5278_, 0, v___x_5276_);
                lean_ctor_set_uint8(
                    v___x_5278_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5277_,
                );
                v___x_5279_ = l_Repr_addAppParen(v___x_5278_, v_prec_5258_);
                return v___x_5279_;
            }
            4 => {
                v___x_5282_ = l_Lean_Meta_instReprCongrArgKind_repr___closed__7;
                lean_inc(v___y_5281_);
                v___x_5283_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5283_, 0, v___y_5281_);
                lean_ctor_set(v___x_5283_, 1, v___x_5282_);
                v___x_5284_ = 0;
                v___x_5285_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5285_, 0, v___x_5283_);
                lean_ctor_set_uint8(
                    v___x_5285_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5284_,
                );
                v___x_5286_ = l_Repr_addAppParen(v___x_5285_, v_prec_5258_);
                return v___x_5286_;
            }
            5 => {
                v___x_5289_ = l_Lean_Meta_instReprCongrArgKind_repr___closed__9;
                lean_inc(v___y_5288_);
                v___x_5290_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5290_, 0, v___y_5288_);
                lean_ctor_set(v___x_5290_, 1, v___x_5289_);
                v___x_5291_ = 0;
                v___x_5292_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5292_, 0, v___x_5290_);
                lean_ctor_set_uint8(
                    v___x_5292_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5291_,
                );
                v___x_5293_ = l_Repr_addAppParen(v___x_5292_, v_prec_5258_);
                return v___x_5293_;
            }
            6 => {
                v___x_5296_ = l_Lean_Meta_instReprCongrArgKind_repr___closed__11;
                lean_inc(v___y_5295_);
                v___x_5297_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5297_, 0, v___y_5295_);
                lean_ctor_set(v___x_5297_, 1, v___x_5296_);
                v___x_5298_ = 0;
                v___x_5299_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5299_, 0, v___x_5297_);
                lean_ctor_set_uint8(
                    v___x_5299_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5298_,
                );
                v___x_5300_ = l_Repr_addAppParen(v___x_5299_, v_prec_5258_);
                return v___x_5300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReprCongrArgKind_repr___boxed(
    mut v_x_5325_: *mut LeanObject,
    mut v_prec_5326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_345__boxed_5327_: u8 = 0;
    let mut v_res_5328_: *mut LeanObject = core::ptr::null_mut();
    v_x_345__boxed_5327_ = (lean_unbox(v_x_5325_) as u8);
    v_res_5328_ = l_Lean_Meta_instReprCongrArgKind_repr(v_x_345__boxed_5327_, v_prec_5326_);
    lean_dec(v_prec_5326_);
    return v_res_5328_;
}
pub unsafe fn l_Lean_Meta_instBEqCongrArgKind_beq(mut v_x_5331_: u8, mut v_y_5332_: u8) -> u8 {
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    v___x_5333_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_x_5331_);
    v___x_5334_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_y_5332_);
    v___x_5335_ = lean_nat_dec_eq(v___x_5333_, v___x_5334_);
    lean_dec(v___x_5334_);
    lean_dec(v___x_5333_);
    return v___x_5335_;
}
pub unsafe fn l_Lean_Meta_instBEqCongrArgKind_beq___boxed(
    mut v_x_5336_: *mut LeanObject,
    mut v_y_5337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_5338_: u8 = 0;
    let mut v_y_18__boxed_5339_: u8 = 0;
    let mut v_res_5340_: u8 = 0;
    let mut v_r_5341_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_5338_ = (lean_unbox(v_x_5336_) as u8);
    v_y_18__boxed_5339_ = (lean_unbox(v_y_5337_) as u8);
    v_res_5340_ = l_Lean_Meta_instBEqCongrArgKind_beq(v_x_17__boxed_5338_, v_y_18__boxed_5339_);
    v_r_5341_ = lean_box((v_res_5340_) as usize);
    return v_r_5341_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(
    mut v_as_5345_: *mut LeanObject,
    mut v_sz_5346_: usize,
    mut v_i_5347_: usize,
    mut v_b_5348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5349_: u8 = 0;
    let mut v_a_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: usize = 0;
    let mut v___x_5358_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5349_ = lean_usize_dec_lt(v_i_5347_, v_sz_5346_);
                if v___x_5349_ == 0 {
                    return v_b_5348_;
                } else {
                    v_a_5350_ = lean_array_uget_borrowed(v_as_5345_, v_i_5347_);
                    lean_inc_ref(v_b_5348_);
                    v___x_5351_ = l_Lean_LocalContext_getFVar_x21(v_b_5348_, v_a_5350_);
                    v___x_5352_ = l_Lean_LocalDecl_fvarId(v___x_5351_);
                    v___x_5353_ = l_Lean_LocalDecl_userName(v___x_5351_);
                    lean_dec_ref(v___x_5351_);
                    v___x_5354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0;
                    v___x_5355_ = lean_name_append_after(v___x_5353_, v___x_5354_);
                    v___x_5356_ =
                        l_Lean_LocalContext_setUserName(v_b_5348_, v___x_5352_, v___x_5355_);
                    v___x_5357_ = 1usize;
                    v___x_5358_ = lean_usize_add(v_i_5347_, v___x_5357_);
                    v_i_5347_ = v___x_5358_;
                    v_b_5348_ = v___x_5356_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(
    mut v_as_5360_: *mut LeanObject,
    mut v_sz_5361_: *mut LeanObject,
    mut v_i_5362_: *mut LeanObject,
    mut v_b_5363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5364_: usize = 0;
    let mut v_i_boxed_5365_: usize = 0;
    let mut v_res_5366_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5364_ = lean_unbox_usize(v_sz_5361_);
    lean_dec(v_sz_5361_);
    v_i_boxed_5365_ = lean_unbox_usize(v_i_5362_);
    lean_dec(v_i_5362_);
    v_res_5366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_as_5360_, v_sz_boxed_5364_, v_i_boxed_5365_, v_b_5363_);
    lean_dec_ref(v_as_5360_);
    return v_res_5366_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(
    mut v_ys_5367_: *mut LeanObject,
    mut v_lctx_5368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5369_: usize = 0;
    let mut v___x_5370_: usize = 0;
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    v_sz_5369_ = lean_array_size(v_ys_5367_);
    v___x_5370_ = 0usize;
    v___x_5371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_ys_5367_, v_sz_5369_, v___x_5370_, v_lctx_5368_);
    return v___x_5371_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(
    mut v_ys_5372_: *mut LeanObject,
    mut v_lctx_5373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5374_: *mut LeanObject = core::ptr::null_mut();
    v_res_5374_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(
        v_ys_5372_,
        v_lctx_5373_,
    );
    lean_dec_ref(v_ys_5372_);
    return v_res_5374_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(
    mut v_as_5375_: *mut LeanObject,
    mut v_sz_5376_: usize,
    mut v_i_5377_: usize,
    mut v_b_5378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5379_: u8 = 0;
    let mut v_a_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: u8 = 0;
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: usize = 0;
    let mut v___x_5386_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5379_ = lean_usize_dec_lt(v_i_5377_, v_sz_5376_);
                if v___x_5379_ == 0 {
                    return v_b_5378_;
                } else {
                    v_a_5380_ = lean_array_uget_borrowed(v_as_5375_, v_i_5377_);
                    lean_inc_ref(v_b_5378_);
                    v___x_5381_ = l_Lean_LocalContext_getFVar_x21(v_b_5378_, v_a_5380_);
                    v___x_5382_ = l_Lean_LocalDecl_fvarId(v___x_5381_);
                    lean_dec_ref(v___x_5381_);
                    v___x_5383_ = 0;
                    v___x_5384_ =
                        l_Lean_LocalContext_setBinderInfo(v_b_5378_, v___x_5382_, v___x_5383_);
                    v___x_5385_ = 1usize;
                    v___x_5386_ = lean_usize_add(v_i_5377_, v___x_5385_);
                    v_i_5377_ = v___x_5386_;
                    v_b_5378_ = v___x_5384_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(
    mut v_as_5388_: *mut LeanObject,
    mut v_sz_5389_: *mut LeanObject,
    mut v_i_5390_: *mut LeanObject,
    mut v_b_5391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5392_: usize = 0;
    let mut v_i_boxed_5393_: usize = 0;
    let mut v_res_5394_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5392_ = lean_unbox_usize(v_sz_5389_);
    lean_dec(v_sz_5389_);
    v_i_boxed_5393_ = lean_unbox_usize(v_i_5390_);
    lean_dec(v_i_5390_);
    v_res_5394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_as_5388_, v_sz_boxed_5392_, v_i_boxed_5393_, v_b_5391_);
    lean_dec_ref(v_as_5388_);
    return v_res_5394_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(
    mut v_ys_5395_: *mut LeanObject,
    mut v_lctx_5396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5397_: usize = 0;
    let mut v___x_5398_: usize = 0;
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    v_sz_5397_ = lean_array_size(v_ys_5395_);
    v___x_5398_ = 0usize;
    v___x_5399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_ys_5395_, v_sz_5397_, v___x_5398_, v_lctx_5396_);
    return v___x_5399_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(
    mut v_ys_5400_: *mut LeanObject,
    mut v_lctx_5401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5402_: *mut LeanObject = core::ptr::null_mut();
    v_res_5402_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_5400_, v_lctx_5401_);
    lean_dec_ref(v_ys_5400_);
    return v_res_5402_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(
    mut v_k_5403_: *mut LeanObject,
    mut v_b_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5408_);
    lean_inc_ref(v___y_5407_);
    lean_inc(v___y_5406_);
    lean_inc_ref(v___y_5405_);
    v___x_5410_ = lean_apply_6(
        v_k_5403_,
        v_b_5404_,
        v___y_5405_,
        v___y_5406_,
        v___y_5407_,
        v___y_5408_,
        lean_box(0),
    );
    return v___x_5410_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_5411_: *mut LeanObject,
    mut v_b_5412_: *mut LeanObject,
    mut v___y_5413_: *mut LeanObject,
    mut v___y_5414_: *mut LeanObject,
    mut v___y_5415_: *mut LeanObject,
    mut v___y_5416_: *mut LeanObject,
    mut v___y_5417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5418_: *mut LeanObject = core::ptr::null_mut();
    v_res_5418_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_5411_, v_b_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
    lean_dec(v___y_5416_);
    lean_dec_ref(v___y_5415_);
    lean_dec(v___y_5414_);
    lean_dec_ref(v___y_5413_);
    return v_res_5418_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(
    mut v_name_5419_: *mut LeanObject,
    mut v_bi_5420_: u8,
    mut v_type_5421_: *mut LeanObject,
    mut v_k_5422_: *mut LeanObject,
    mut v_kind_5423_: u8,
    mut v___y_5424_: *mut LeanObject,
    mut v___y_5425_: *mut LeanObject,
    mut v___y_5426_: *mut LeanObject,
    mut v___y_5427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_a_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5442_: u8 = 0;
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5429_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_5429_, 0, v_k_5422_);
                v___x_5430_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_5419_,
                    v_bi_5420_,
                    v_type_5421_,
                    v___f_5429_,
                    v_kind_5423_,
                    v___y_5424_,
                    v___y_5425_,
                    v___y_5426_,
                    v___y_5427_,
                );
                if lean_obj_tag(v___x_5430_) == 0 {
                    v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
                    v_isSharedCheck_5438_ = (!lean_is_exclusive(v___x_5430_)) as u8;
                    if v_isSharedCheck_5438_ == 0 {
                        v___x_5433_ = v___x_5430_;
                        v_isShared_5434_ = v_isSharedCheck_5438_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5431_);
                        lean_dec(v___x_5430_);
                        v___x_5433_ = lean_box(0);
                        v_isShared_5434_ = v_isSharedCheck_5438_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5439_ = lean_ctor_get(v___x_5430_, 0);
                    v_isSharedCheck_5446_ = (!lean_is_exclusive(v___x_5430_)) as u8;
                    if v_isSharedCheck_5446_ == 0 {
                        v___x_5441_ = v___x_5430_;
                        v_isShared_5442_ = v_isSharedCheck_5446_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5439_);
                        lean_dec(v___x_5430_);
                        v___x_5441_ = lean_box(0);
                        v_isShared_5442_ = v_isSharedCheck_5446_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5434_ == 0 {
                    v___x_5436_ = v___x_5433_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5436_;
            }
            3 => {
                if v_isShared_5442_ == 0 {
                    v___x_5444_ = v___x_5441_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
                    v___x_5444_ = v_reuseFailAlloc_5445_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___boxed(
    mut v_name_5447_: *mut LeanObject,
    mut v_bi_5448_: *mut LeanObject,
    mut v_type_5449_: *mut LeanObject,
    mut v_k_5450_: *mut LeanObject,
    mut v_kind_5451_: *mut LeanObject,
    mut v___y_5452_: *mut LeanObject,
    mut v___y_5453_: *mut LeanObject,
    mut v___y_5454_: *mut LeanObject,
    mut v___y_5455_: *mut LeanObject,
    mut v___y_5456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_5457_: u8 = 0;
    let mut v_kind_boxed_5458_: u8 = 0;
    let mut v_res_5459_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_5457_ = (lean_unbox(v_bi_5448_) as u8);
    v_kind_boxed_5458_ = (lean_unbox(v_kind_5451_) as u8);
    v_res_5459_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_5447_, v_bi_boxed_5457_, v_type_5449_, v_k_5450_, v_kind_boxed_5458_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_);
    lean_dec(v___y_5455_);
    lean_dec_ref(v___y_5454_);
    lean_dec(v___y_5453_);
    lean_dec_ref(v___y_5452_);
    return v_res_5459_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(
    mut v_name_5460_: *mut LeanObject,
    mut v_type_5461_: *mut LeanObject,
    mut v_k_5462_: *mut LeanObject,
    mut v___y_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
    mut v___y_5466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5468_: u8 = 0;
    let mut v___x_5469_: u8 = 0;
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    v___x_5468_ = 0;
    v___x_5469_ = 0;
    v___x_5470_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_5460_, v___x_5468_, v_type_5461_, v_k_5462_, v___x_5469_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
    return v___x_5470_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg___boxed(
    mut v_name_5471_: *mut LeanObject,
    mut v_type_5472_: *mut LeanObject,
    mut v_k_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5479_: *mut LeanObject = core::ptr::null_mut();
    v_res_5479_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_5471_, v_type_5472_, v_k_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_);
    lean_dec(v___y_5477_);
    lean_dec_ref(v___y_5476_);
    lean_dec(v___y_5475_);
    lean_dec_ref(v___y_5474_);
    return v_res_5479_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(
    mut v_eqs_5483_: *mut LeanObject,
    mut v_kinds_5484_: *mut LeanObject,
    mut v_xs_5485_: *mut LeanObject,
    mut v_ys_5486_: *mut LeanObject,
    mut v_k_5487_: *mut LeanObject,
    mut v___x_5488_: *mut LeanObject,
    mut v_h_5489_: *mut LeanObject,
    mut v___y_5490_: *mut LeanObject,
    mut v___y_5491_: *mut LeanObject,
    mut v___y_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5495_: *mut LeanObject = core::ptr::null_mut();
    v_res_5495_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(v_eqs_5483_, v_kinds_5484_, v_xs_5485_, v_ys_5486_, v_k_5487_, v___x_5488_, v_h_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
    lean_dec(v___y_5493_);
    lean_dec_ref(v___y_5492_);
    lean_dec(v___y_5491_);
    lean_dec_ref(v___y_5490_);
    lean_dec(v___x_5488_);
    return v_res_5495_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(
    mut v_eqs_5496_: *mut LeanObject,
    mut v_kinds_5497_: *mut LeanObject,
    mut v_xs_5498_: *mut LeanObject,
    mut v_ys_5499_: *mut LeanObject,
    mut v_k_5500_: *mut LeanObject,
    mut v___x_5501_: *mut LeanObject,
    mut v_h_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: u8 = 0;
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    v___x_5508_ = lean_array_push(v_eqs_5496_, v_h_5502_);
    v___x_5509_ = 2;
    v___x_5510_ = lean_box((v___x_5509_) as usize);
    v___x_5511_ = lean_array_push(v_kinds_5497_, v___x_5510_);
    v___x_5512_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(
            v_xs_5498_,
            v_ys_5499_,
            v_k_5500_,
            v___x_5501_,
            v___x_5508_,
            v___x_5511_,
            v___y_5503_,
            v___y_5504_,
            v___y_5505_,
            v___y_5506_,
        );
    return v___x_5512_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(
    mut v_eqs_5513_: *mut LeanObject,
    mut v_kinds_5514_: *mut LeanObject,
    mut v_xs_5515_: *mut LeanObject,
    mut v_ys_5516_: *mut LeanObject,
    mut v_k_5517_: *mut LeanObject,
    mut v___x_5518_: *mut LeanObject,
    mut v_h_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
    mut v___y_5522_: *mut LeanObject,
    mut v___y_5523_: *mut LeanObject,
    mut v___y_5524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5525_: *mut LeanObject = core::ptr::null_mut();
    v_res_5525_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(v_eqs_5513_, v_kinds_5514_, v_xs_5515_, v_ys_5516_, v_k_5517_, v___x_5518_, v_h_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
    lean_dec(v___y_5523_);
    lean_dec_ref(v___y_5522_);
    lean_dec(v___y_5521_);
    lean_dec_ref(v___y_5520_);
    lean_dec(v___x_5518_);
    return v_res_5525_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(
    mut v_xs_5526_: *mut LeanObject,
    mut v_ys_5527_: *mut LeanObject,
    mut v_k_5528_: *mut LeanObject,
    mut v_i_5529_: *mut LeanObject,
    mut v_eqs_5530_: *mut LeanObject,
    mut v_kinds_5531_: *mut LeanObject,
    mut v_a_5532_: *mut LeanObject,
    mut v_a_5533_: *mut LeanObject,
    mut v_a_5534_: *mut LeanObject,
    mut v_a_5535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: u8 = 0;
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5561_: u8 = 0;
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5565_: u8 = 0;
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5577_: u8 = 0;
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v_a_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5585_: u8 = 0;
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_a_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5593_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5537_ = lean_array_get_size(v_xs_5526_);
                v___x_5538_ = lean_nat_dec_lt(v_i_5529_, v___x_5537_);
                if v___x_5538_ == 0 {
                    lean_dec_ref(v_ys_5527_);
                    lean_dec_ref(v_xs_5526_);
                    lean_inc(v_a_5535_);
                    lean_inc_ref(v_a_5534_);
                    lean_inc(v_a_5533_);
                    lean_inc_ref(v_a_5532_);
                    v___x_5539_ = lean_apply_7(
                        v_k_5528_,
                        v_eqs_5530_,
                        v_kinds_5531_,
                        v_a_5532_,
                        v_a_5533_,
                        v_a_5534_,
                        v_a_5535_,
                        lean_box(0),
                    );
                    return v___x_5539_;
                } else {
                    v___x_5540_ = l_Lean_instInhabitedExpr;
                    v_x_5541_ = lean_array_get_borrowed(v___x_5540_, v_xs_5526_, v_i_5529_);
                    lean_inc(v_a_5535_);
                    lean_inc_ref(v_a_5534_);
                    lean_inc(v_a_5533_);
                    lean_inc_ref(v_a_5532_);
                    lean_inc(v_x_5541_);
                    v___x_5542_ =
                        lean_infer_type(v_x_5541_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
                    if lean_obj_tag(v___x_5542_) == 0 {
                        v_a_5543_ = lean_ctor_get(v___x_5542_, 0);
                        lean_inc(v_a_5543_);
                        lean_dec_ref_known(v___x_5542_, 1);
                        v_y_5544_ = lean_array_get_borrowed(v___x_5540_, v_ys_5527_, v_i_5529_);
                        lean_inc(v_a_5535_);
                        lean_inc_ref(v_a_5534_);
                        lean_inc(v_a_5533_);
                        lean_inc_ref(v_a_5532_);
                        lean_inc(v_y_5544_);
                        v___x_5545_ =
                            lean_infer_type(v_y_5544_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
                        if lean_obj_tag(v___x_5545_) == 0 {
                            v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
                            lean_inc(v_a_5546_);
                            lean_dec_ref_known(v___x_5545_, 1);
                            v___x_5547_ = l_Lean_Expr_cleanupAnnotations(v_a_5543_);
                            v___x_5548_ = l_Lean_Expr_cleanupAnnotations(v_a_5546_);
                            v___x_5549_ = lean_expr_eqv(v___x_5547_, v___x_5548_);
                            lean_dec_ref(v___x_5548_);
                            lean_dec_ref(v___x_5547_);
                            if v___x_5549_ == 0 {
                                lean_inc(v_y_5544_);
                                lean_inc(v_x_5541_);
                                v___x_5550_ = l_Lean_Meta_mkHEq(
                                    v_x_5541_, v_y_5544_, v_a_5532_, v_a_5533_, v_a_5534_,
                                    v_a_5535_,
                                );
                                if lean_obj_tag(v___x_5550_) == 0 {
                                    v_a_5551_ = lean_ctor_get(v___x_5550_, 0);
                                    lean_inc(v_a_5551_);
                                    lean_dec_ref_known(v___x_5550_, 1);
                                    v___x_5552_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1;
                                    v___x_5553_ = lean_unsigned_to_nat(1);
                                    v___x_5554_ = lean_nat_add(v_i_5529_, v___x_5553_);
                                    lean_inc(v___x_5554_);
                                    v___f_5555_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 6);
                                    lean_closure_set(v___f_5555_, 0, v_eqs_5530_);
                                    lean_closure_set(v___f_5555_, 1, v_kinds_5531_);
                                    lean_closure_set(v___f_5555_, 2, v_xs_5526_);
                                    lean_closure_set(v___f_5555_, 3, v_ys_5527_);
                                    lean_closure_set(v___f_5555_, 4, v_k_5528_);
                                    lean_closure_set(v___f_5555_, 5, v___x_5554_);
                                    v___x_5556_ =
                                        lean_name_append_index_after(v___x_5552_, v___x_5554_);
                                    v___x_5557_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_5556_, v_a_5551_, v___f_5555_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
                                    return v___x_5557_;
                                } else {
                                    lean_dec_ref(v_kinds_5531_);
                                    lean_dec_ref(v_eqs_5530_);
                                    lean_dec_ref(v_k_5528_);
                                    lean_dec_ref(v_ys_5527_);
                                    lean_dec_ref(v_xs_5526_);
                                    v_a_5558_ = lean_ctor_get(v___x_5550_, 0);
                                    v_isSharedCheck_5565_ = (!lean_is_exclusive(v___x_5550_)) as u8;
                                    if v_isSharedCheck_5565_ == 0 {
                                        v___x_5560_ = v___x_5550_;
                                        v_isShared_5561_ = v_isSharedCheck_5565_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5558_);
                                        lean_dec(v___x_5550_);
                                        v___x_5560_ = lean_box(0);
                                        v_isShared_5561_ = v_isSharedCheck_5565_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v_y_5544_);
                                lean_inc(v_x_5541_);
                                v___x_5566_ = l_Lean_Meta_mkEq(
                                    v_x_5541_, v_y_5544_, v_a_5532_, v_a_5533_, v_a_5534_,
                                    v_a_5535_,
                                );
                                if lean_obj_tag(v___x_5566_) == 0 {
                                    v_a_5567_ = lean_ctor_get(v___x_5566_, 0);
                                    lean_inc(v_a_5567_);
                                    lean_dec_ref_known(v___x_5566_, 1);
                                    v___x_5568_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1;
                                    v___x_5569_ = lean_unsigned_to_nat(1);
                                    v___x_5570_ = lean_nat_add(v_i_5529_, v___x_5569_);
                                    lean_inc(v___x_5570_);
                                    v___f_5571_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed as *mut core::ffi::c_void, 12, 6);
                                    lean_closure_set(v___f_5571_, 0, v_eqs_5530_);
                                    lean_closure_set(v___f_5571_, 1, v_kinds_5531_);
                                    lean_closure_set(v___f_5571_, 2, v_xs_5526_);
                                    lean_closure_set(v___f_5571_, 3, v_ys_5527_);
                                    lean_closure_set(v___f_5571_, 4, v_k_5528_);
                                    lean_closure_set(v___f_5571_, 5, v___x_5570_);
                                    v___x_5572_ =
                                        lean_name_append_index_after(v___x_5568_, v___x_5570_);
                                    v___x_5573_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_5572_, v_a_5567_, v___f_5571_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
                                    return v___x_5573_;
                                } else {
                                    lean_dec_ref(v_kinds_5531_);
                                    lean_dec_ref(v_eqs_5530_);
                                    lean_dec_ref(v_k_5528_);
                                    lean_dec_ref(v_ys_5527_);
                                    lean_dec_ref(v_xs_5526_);
                                    v_a_5574_ = lean_ctor_get(v___x_5566_, 0);
                                    v_isSharedCheck_5581_ = (!lean_is_exclusive(v___x_5566_)) as u8;
                                    if v_isSharedCheck_5581_ == 0 {
                                        v___x_5576_ = v___x_5566_;
                                        v_isShared_5577_ = v_isSharedCheck_5581_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5574_);
                                        lean_dec(v___x_5566_);
                                        v___x_5576_ = lean_box(0);
                                        v_isShared_5577_ = v_isSharedCheck_5581_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5543_);
                            lean_dec_ref(v_kinds_5531_);
                            lean_dec_ref(v_eqs_5530_);
                            lean_dec_ref(v_k_5528_);
                            lean_dec_ref(v_ys_5527_);
                            lean_dec_ref(v_xs_5526_);
                            v_a_5582_ = lean_ctor_get(v___x_5545_, 0);
                            v_isSharedCheck_5589_ = (!lean_is_exclusive(v___x_5545_)) as u8;
                            if v_isSharedCheck_5589_ == 0 {
                                v___x_5584_ = v___x_5545_;
                                v_isShared_5585_ = v_isSharedCheck_5589_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5582_);
                                lean_dec(v___x_5545_);
                                v___x_5584_ = lean_box(0);
                                v_isShared_5585_ = v_isSharedCheck_5589_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_kinds_5531_);
                        lean_dec_ref(v_eqs_5530_);
                        lean_dec_ref(v_k_5528_);
                        lean_dec_ref(v_ys_5527_);
                        lean_dec_ref(v_xs_5526_);
                        v_a_5590_ = lean_ctor_get(v___x_5542_, 0);
                        v_isSharedCheck_5597_ = (!lean_is_exclusive(v___x_5542_)) as u8;
                        if v_isSharedCheck_5597_ == 0 {
                            v___x_5592_ = v___x_5542_;
                            v_isShared_5593_ = v_isSharedCheck_5597_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5590_);
                            lean_dec(v___x_5542_);
                            v___x_5592_ = lean_box(0);
                            v_isShared_5593_ = v_isSharedCheck_5597_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5561_ == 0 {
                    v___x_5563_ = v___x_5560_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5564_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_a_5558_);
                    v___x_5563_ = v_reuseFailAlloc_5564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5563_;
            }
            3 => {
                if v_isShared_5577_ == 0 {
                    v___x_5579_ = v___x_5576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
                    v___x_5579_ = v_reuseFailAlloc_5580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5579_;
            }
            5 => {
                if v_isShared_5585_ == 0 {
                    v___x_5587_ = v___x_5584_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5582_);
                    v___x_5587_ = v_reuseFailAlloc_5588_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5587_;
            }
            7 => {
                if v_isShared_5593_ == 0 {
                    v___x_5595_ = v___x_5592_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
                    v___x_5595_ = v_reuseFailAlloc_5596_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(
    mut v_eqs_5598_: *mut LeanObject,
    mut v_kinds_5599_: *mut LeanObject,
    mut v_xs_5600_: *mut LeanObject,
    mut v_ys_5601_: *mut LeanObject,
    mut v_k_5602_: *mut LeanObject,
    mut v___x_5603_: *mut LeanObject,
    mut v_h_5604_: *mut LeanObject,
    mut v___y_5605_: *mut LeanObject,
    mut v___y_5606_: *mut LeanObject,
    mut v___y_5607_: *mut LeanObject,
    mut v___y_5608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: u8 = 0;
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    v___x_5610_ = lean_array_push(v_eqs_5598_, v_h_5604_);
    v___x_5611_ = 4;
    v___x_5612_ = lean_box((v___x_5611_) as usize);
    v___x_5613_ = lean_array_push(v_kinds_5599_, v___x_5612_);
    v___x_5614_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(
            v_xs_5600_,
            v_ys_5601_,
            v_k_5602_,
            v___x_5603_,
            v___x_5610_,
            v___x_5613_,
            v___y_5605_,
            v___y_5606_,
            v___y_5607_,
            v___y_5608_,
        );
    return v___x_5614_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(
    mut v_xs_5615_: *mut LeanObject,
    mut v_ys_5616_: *mut LeanObject,
    mut v_k_5617_: *mut LeanObject,
    mut v_i_5618_: *mut LeanObject,
    mut v_eqs_5619_: *mut LeanObject,
    mut v_kinds_5620_: *mut LeanObject,
    mut v_a_5621_: *mut LeanObject,
    mut v_a_5622_: *mut LeanObject,
    mut v_a_5623_: *mut LeanObject,
    mut v_a_5624_: *mut LeanObject,
    mut v_a_5625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5626_: *mut LeanObject = core::ptr::null_mut();
    v_res_5626_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(
            v_xs_5615_,
            v_ys_5616_,
            v_k_5617_,
            v_i_5618_,
            v_eqs_5619_,
            v_kinds_5620_,
            v_a_5621_,
            v_a_5622_,
            v_a_5623_,
            v_a_5624_,
        );
    lean_dec(v_a_5624_);
    lean_dec_ref(v_a_5623_);
    lean_dec(v_a_5622_);
    lean_dec_ref(v_a_5621_);
    lean_dec(v_i_5618_);
    return v_res_5626_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(
    mut v_00_u03b1_5627_: *mut LeanObject,
    mut v_xs_5628_: *mut LeanObject,
    mut v_ys_5629_: *mut LeanObject,
    mut v_k_5630_: *mut LeanObject,
    mut v_i_5631_: *mut LeanObject,
    mut v_eqs_5632_: *mut LeanObject,
    mut v_kinds_5633_: *mut LeanObject,
    mut v_a_5634_: *mut LeanObject,
    mut v_a_5635_: *mut LeanObject,
    mut v_a_5636_: *mut LeanObject,
    mut v_a_5637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    v___x_5639_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(
            v_xs_5628_,
            v_ys_5629_,
            v_k_5630_,
            v_i_5631_,
            v_eqs_5632_,
            v_kinds_5633_,
            v_a_5634_,
            v_a_5635_,
            v_a_5636_,
            v_a_5637_,
        );
    return v___x_5639_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(
    mut v_00_u03b1_5640_: *mut LeanObject,
    mut v_xs_5641_: *mut LeanObject,
    mut v_ys_5642_: *mut LeanObject,
    mut v_k_5643_: *mut LeanObject,
    mut v_i_5644_: *mut LeanObject,
    mut v_eqs_5645_: *mut LeanObject,
    mut v_kinds_5646_: *mut LeanObject,
    mut v_a_5647_: *mut LeanObject,
    mut v_a_5648_: *mut LeanObject,
    mut v_a_5649_: *mut LeanObject,
    mut v_a_5650_: *mut LeanObject,
    mut v_a_5651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5652_: *mut LeanObject = core::ptr::null_mut();
    v_res_5652_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(
            v_00_u03b1_5640_,
            v_xs_5641_,
            v_ys_5642_,
            v_k_5643_,
            v_i_5644_,
            v_eqs_5645_,
            v_kinds_5646_,
            v_a_5647_,
            v_a_5648_,
            v_a_5649_,
            v_a_5650_,
        );
    lean_dec(v_a_5650_);
    lean_dec_ref(v_a_5649_);
    lean_dec(v_a_5648_);
    lean_dec_ref(v_a_5647_);
    lean_dec(v_i_5644_);
    return v_res_5652_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(
    mut v_00_u03b1_5653_: *mut LeanObject,
    mut v_name_5654_: *mut LeanObject,
    mut v_bi_5655_: u8,
    mut v_type_5656_: *mut LeanObject,
    mut v_k_5657_: *mut LeanObject,
    mut v_kind_5658_: u8,
    mut v___y_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
    mut v___y_5662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    v___x_5664_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_5654_, v_bi_5655_, v_type_5656_, v_k_5657_, v_kind_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
    return v___x_5664_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___boxed(
    mut v_00_u03b1_5665_: *mut LeanObject,
    mut v_name_5666_: *mut LeanObject,
    mut v_bi_5667_: *mut LeanObject,
    mut v_type_5668_: *mut LeanObject,
    mut v_k_5669_: *mut LeanObject,
    mut v_kind_5670_: *mut LeanObject,
    mut v___y_5671_: *mut LeanObject,
    mut v___y_5672_: *mut LeanObject,
    mut v___y_5673_: *mut LeanObject,
    mut v___y_5674_: *mut LeanObject,
    mut v___y_5675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_5676_: u8 = 0;
    let mut v_kind_boxed_5677_: u8 = 0;
    let mut v_res_5678_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_5676_ = (lean_unbox(v_bi_5667_) as u8);
    v_kind_boxed_5677_ = (lean_unbox(v_kind_5670_) as u8);
    v_res_5678_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_5665_, v_name_5666_, v_bi_boxed_5676_, v_type_5668_, v_k_5669_, v_kind_boxed_5677_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
    lean_dec(v___y_5674_);
    lean_dec_ref(v___y_5673_);
    lean_dec(v___y_5672_);
    lean_dec_ref(v___y_5671_);
    return v_res_5678_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(
    mut v_00_u03b1_5679_: *mut LeanObject,
    mut v_name_5680_: *mut LeanObject,
    mut v_type_5681_: *mut LeanObject,
    mut v_k_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    v___x_5688_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_5680_, v_type_5681_, v_k_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_);
    return v___x_5688_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___boxed(
    mut v_00_u03b1_5689_: *mut LeanObject,
    mut v_name_5690_: *mut LeanObject,
    mut v_type_5691_: *mut LeanObject,
    mut v_k_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5698_: *mut LeanObject = core::ptr::null_mut();
    v_res_5698_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(v_00_u03b1_5689_, v_name_5690_, v_type_5691_, v_k_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
    lean_dec(v___y_5696_);
    lean_dec_ref(v___y_5695_);
    lean_dec(v___y_5694_);
    lean_dec_ref(v___y_5693_);
    return v_res_5698_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(
    mut v_xs_5701_: *mut LeanObject,
    mut v_ys_5702_: *mut LeanObject,
    mut v_k_5703_: *mut LeanObject,
    mut v_a_5704_: *mut LeanObject,
    mut v_a_5705_: *mut LeanObject,
    mut v_a_5706_: *mut LeanObject,
    mut v_a_5707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    v___x_5709_ = lean_unsigned_to_nat(0);
    v___x_5710_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0;
    v___x_5711_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(
            v_xs_5701_,
            v_ys_5702_,
            v_k_5703_,
            v___x_5709_,
            v___x_5710_,
            v___x_5710_,
            v_a_5704_,
            v_a_5705_,
            v_a_5706_,
            v_a_5707_,
        );
    return v___x_5711_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___boxed(
    mut v_xs_5712_: *mut LeanObject,
    mut v_ys_5713_: *mut LeanObject,
    mut v_k_5714_: *mut LeanObject,
    mut v_a_5715_: *mut LeanObject,
    mut v_a_5716_: *mut LeanObject,
    mut v_a_5717_: *mut LeanObject,
    mut v_a_5718_: *mut LeanObject,
    mut v_a_5719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5720_: *mut LeanObject = core::ptr::null_mut();
    v_res_5720_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(
            v_xs_5712_, v_ys_5713_, v_k_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_,
        );
    lean_dec(v_a_5718_);
    lean_dec_ref(v_a_5717_);
    lean_dec(v_a_5716_);
    lean_dec_ref(v_a_5715_);
    return v_res_5720_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(
    mut v_00_u03b1_5721_: *mut LeanObject,
    mut v_xs_5722_: *mut LeanObject,
    mut v_ys_5723_: *mut LeanObject,
    mut v_k_5724_: *mut LeanObject,
    mut v_a_5725_: *mut LeanObject,
    mut v_a_5726_: *mut LeanObject,
    mut v_a_5727_: *mut LeanObject,
    mut v_a_5728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    v___x_5730_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(
            v_xs_5722_, v_ys_5723_, v_k_5724_, v_a_5725_, v_a_5726_, v_a_5727_, v_a_5728_,
        );
    return v___x_5730_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed(
    mut v_00_u03b1_5731_: *mut LeanObject,
    mut v_xs_5732_: *mut LeanObject,
    mut v_ys_5733_: *mut LeanObject,
    mut v_k_5734_: *mut LeanObject,
    mut v_a_5735_: *mut LeanObject,
    mut v_a_5736_: *mut LeanObject,
    mut v_a_5737_: *mut LeanObject,
    mut v_a_5738_: *mut LeanObject,
    mut v_a_5739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5740_: *mut LeanObject = core::ptr::null_mut();
    v_res_5740_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(
        v_00_u03b1_5731_,
        v_xs_5732_,
        v_ys_5733_,
        v_k_5734_,
        v_a_5735_,
        v_a_5736_,
        v_a_5737_,
        v_a_5738_,
    );
    lean_dec(v_a_5738_);
    lean_dec_ref(v_a_5737_);
    lean_dec(v_a_5736_);
    lean_dec_ref(v_a_5735_);
    return v_res_5740_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(
    mut v_k_5741_: *mut LeanObject,
    mut v_b_5742_: *mut LeanObject,
    mut v_c_5743_: *mut LeanObject,
    mut v___y_5744_: *mut LeanObject,
    mut v___y_5745_: *mut LeanObject,
    mut v___y_5746_: *mut LeanObject,
    mut v___y_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5747_);
    lean_inc_ref(v___y_5746_);
    lean_inc(v___y_5745_);
    lean_inc_ref(v___y_5744_);
    v___x_5749_ = lean_apply_7(
        v_k_5741_,
        v_b_5742_,
        v_c_5743_,
        v___y_5744_,
        v___y_5745_,
        v___y_5746_,
        v___y_5747_,
        lean_box(0),
    );
    return v___x_5749_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(
    mut v_k_5750_: *mut LeanObject,
    mut v_b_5751_: *mut LeanObject,
    mut v_c_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5758_: *mut LeanObject = core::ptr::null_mut();
    v_res_5758_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(v_k_5750_, v_b_5751_, v_c_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
    lean_dec(v___y_5756_);
    lean_dec_ref(v___y_5755_);
    lean_dec(v___y_5754_);
    lean_dec_ref(v___y_5753_);
    return v_res_5758_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(
    mut v_type_5759_: *mut LeanObject,
    mut v_maxFVars_x3f_5760_: *mut LeanObject,
    mut v_k_5761_: *mut LeanObject,
    mut v_cleanupAnnotations_5762_: u8,
    mut v_whnfType_5763_: u8,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5774_: u8 = 0;
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5778_: u8 = 0;
    let mut v_a_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5782_: u8 = 0;
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5769_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_5769_, 0, v_k_5761_);
                v___x_5770_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_5759_,
                    v_maxFVars_x3f_5760_,
                    v___f_5769_,
                    v_cleanupAnnotations_5762_,
                    v_whnfType_5763_,
                    v___y_5764_,
                    v___y_5765_,
                    v___y_5766_,
                    v___y_5767_,
                );
                if lean_obj_tag(v___x_5770_) == 0 {
                    v_a_5771_ = lean_ctor_get(v___x_5770_, 0);
                    v_isSharedCheck_5778_ = (!lean_is_exclusive(v___x_5770_)) as u8;
                    if v_isSharedCheck_5778_ == 0 {
                        v___x_5773_ = v___x_5770_;
                        v_isShared_5774_ = v_isSharedCheck_5778_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5771_);
                        lean_dec(v___x_5770_);
                        v___x_5773_ = lean_box(0);
                        v_isShared_5774_ = v_isSharedCheck_5778_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5779_ = lean_ctor_get(v___x_5770_, 0);
                    v_isSharedCheck_5786_ = (!lean_is_exclusive(v___x_5770_)) as u8;
                    if v_isSharedCheck_5786_ == 0 {
                        v___x_5781_ = v___x_5770_;
                        v_isShared_5782_ = v_isSharedCheck_5786_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5779_);
                        lean_dec(v___x_5770_);
                        v___x_5781_ = lean_box(0);
                        v_isShared_5782_ = v_isSharedCheck_5786_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5774_ == 0 {
                    v___x_5776_ = v___x_5773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_a_5771_);
                    v___x_5776_ = v_reuseFailAlloc_5777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5776_;
            }
            3 => {
                if v_isShared_5782_ == 0 {
                    v___x_5784_ = v___x_5781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5779_);
                    v___x_5784_ = v_reuseFailAlloc_5785_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___boxed(
    mut v_type_5787_: *mut LeanObject,
    mut v_maxFVars_x3f_5788_: *mut LeanObject,
    mut v_k_5789_: *mut LeanObject,
    mut v_cleanupAnnotations_5790_: *mut LeanObject,
    mut v_whnfType_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5797_: u8 = 0;
    let mut v_whnfType_boxed_5798_: u8 = 0;
    let mut v_res_5799_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5797_ = (lean_unbox(v_cleanupAnnotations_5790_) as u8);
    v_whnfType_boxed_5798_ = (lean_unbox(v_whnfType_5791_) as u8);
    v_res_5799_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_5787_, v_maxFVars_x3f_5788_, v_k_5789_, v_cleanupAnnotations_boxed_5797_, v_whnfType_boxed_5798_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_);
    lean_dec(v___y_5795_);
    lean_dec_ref(v___y_5794_);
    lean_dec(v___y_5793_);
    lean_dec_ref(v___y_5792_);
    return v_res_5799_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(
    mut v_00_u03b1_5800_: *mut LeanObject,
    mut v_type_5801_: *mut LeanObject,
    mut v_maxFVars_x3f_5802_: *mut LeanObject,
    mut v_k_5803_: *mut LeanObject,
    mut v_cleanupAnnotations_5804_: u8,
    mut v_whnfType_5805_: u8,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
    mut v___y_5808_: *mut LeanObject,
    mut v___y_5809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    v___x_5811_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_5801_, v_maxFVars_x3f_5802_, v_k_5803_, v_cleanupAnnotations_5804_, v_whnfType_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_);
    return v___x_5811_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___boxed(
    mut v_00_u03b1_5812_: *mut LeanObject,
    mut v_type_5813_: *mut LeanObject,
    mut v_maxFVars_x3f_5814_: *mut LeanObject,
    mut v_k_5815_: *mut LeanObject,
    mut v_cleanupAnnotations_5816_: *mut LeanObject,
    mut v_whnfType_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5823_: u8 = 0;
    let mut v_whnfType_boxed_5824_: u8 = 0;
    let mut v_res_5825_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5823_ = (lean_unbox(v_cleanupAnnotations_5816_) as u8);
    v_whnfType_boxed_5824_ = (lean_unbox(v_whnfType_5817_) as u8);
    v_res_5825_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(v_00_u03b1_5812_, v_type_5813_, v_maxFVars_x3f_5814_, v_k_5815_, v_cleanupAnnotations_boxed_5823_, v_whnfType_boxed_5824_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
    lean_dec(v___y_5821_);
    lean_dec_ref(v___y_5820_);
    lean_dec(v___y_5819_);
    lean_dec_ref(v___y_5818_);
    return v_res_5825_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(
    mut v___x_5834_: *mut LeanObject,
    mut v___x_5835_: *mut LeanObject,
    mut v___x_5836_: *mut LeanObject,
    mut v___x_5837_: *mut LeanObject,
    mut v___x_5838_: *mut LeanObject,
    mut v_a_5839_: *mut LeanObject,
    mut v_type_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1902__boxed_5846_: u8 = 0;
    let mut v_res_5847_: *mut LeanObject = core::ptr::null_mut();
    v___x_1902__boxed_5846_ = (lean_unbox(v___x_5836_) as u8);
    v_res_5847_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(
            v___x_5834_,
            v___x_5835_,
            v___x_1902__boxed_5846_,
            v___x_5837_,
            v___x_5838_,
            v_a_5839_,
            v_type_5840_,
            v___y_5841_,
            v___y_5842_,
            v___y_5843_,
            v___y_5844_,
        );
    lean_dec(v___y_5844_);
    lean_dec_ref(v___y_5843_);
    lean_dec(v___y_5842_);
    lean_dec_ref(v___y_5841_);
    lean_dec_ref(v_a_5839_);
    return v_res_5847_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(
    mut v_type_5848_: *mut LeanObject,
    mut v_a_5849_: *mut LeanObject,
    mut v_a_5850_: *mut LeanObject,
    mut v_a_5851_: *mut LeanObject,
    mut v_a_5852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: u8 = 0;
    v___x_5854_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1;
    v___x_5855_ = lean_unsigned_to_nat(3);
    v___x_5856_ = l_Lean_Expr_isAppOfArity(v_type_5848_, v___x_5854_, v___x_5855_);
    if v___x_5856_ == 0 {
        let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5859_: u8 = 0;
        v___x_5857_ =
            l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3;
        v___x_5858_ = lean_unsigned_to_nat(4);
        v___x_5859_ = l_Lean_Expr_isAppOfArity(v_type_5848_, v___x_5857_, v___x_5858_);
        if v___x_5859_ == 0 {
            let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5865_: u8 = 0;
            let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
            v___x_5860_ = l_Lean_instInhabitedExpr;
            v___x_5861_ = lean_unsigned_to_nat(1);
            v___x_5862_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4;
            v___x_5863_ = lean_box((v___x_5859_) as usize);
            v___f_5864_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed as *mut core::ffi::c_void, 12, 5);
            lean_closure_set(v___f_5864_, 0, v___x_5860_);
            lean_closure_set(v___f_5864_, 1, v___x_5861_);
            lean_closure_set(v___f_5864_, 2, v___x_5863_);
            lean_closure_set(v___f_5864_, 3, v___x_5855_);
            lean_closure_set(v___f_5864_, 4, v___x_5862_);
            v___x_5865_ = 1;
            v___x_5866_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_5848_, v___x_5862_, v___f_5864_, v___x_5865_, v___x_5859_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_);
            return v___x_5866_;
        } else {
            let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
            v___x_5867_ = l_Lean_Expr_appFn_x21(v_type_5848_);
            lean_dec_ref(v_type_5848_);
            v___x_5868_ = l_Lean_Expr_appFn_x21(v___x_5867_);
            lean_dec_ref(v___x_5867_);
            v___x_5869_ = l_Lean_Expr_appArg_x21(v___x_5868_);
            lean_dec_ref(v___x_5868_);
            v___x_5870_ =
                l_Lean_Meta_mkHEqRefl(v___x_5869_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_);
            return v___x_5870_;
        }
    } else {
        let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
        v___x_5871_ = l_Lean_Expr_appFn_x21(v_type_5848_);
        lean_dec_ref(v_type_5848_);
        v___x_5872_ = l_Lean_Expr_appArg_x21(v___x_5871_);
        lean_dec_ref(v___x_5871_);
        v___x_5873_ = l_Lean_Meta_mkEqRefl(v___x_5872_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_);
        return v___x_5873_;
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(
    mut v_type_5874_: *mut LeanObject,
    mut v_motive_5875_: *mut LeanObject,
    mut v___x_5876_: *mut LeanObject,
    mut v_b_5877_: *mut LeanObject,
    mut v___x_5878_: u8,
    mut v___x_5879_: *mut LeanObject,
    mut v_a_5880_: *mut LeanObject,
    mut v_eqPr_5881_: *mut LeanObject,
    mut v___y_5882_: *mut LeanObject,
    mut v___y_5883_: *mut LeanObject,
    mut v___y_5884_: *mut LeanObject,
    mut v___y_5885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_major_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: u8 = 0;
    let mut v___x_5904_: u8 = 0;
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: u8 = 0;
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_5887_ = l_Lean_Expr_bindingBody_x21(v_type_5874_);
                v___x_5888_ =
                    l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(
                        v_type_5887_,
                        v___y_5882_,
                        v___y_5883_,
                        v___y_5884_,
                        v___y_5885_,
                    );
                if lean_obj_tag(v___x_5888_) == 0 {
                    v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
                    lean_inc(v_a_5889_);
                    lean_dec_ref_known(v___x_5888_, 1);
                    lean_inc(v___y_5885_);
                    lean_inc_ref(v___y_5884_);
                    lean_inc(v___y_5883_);
                    lean_inc_ref(v___y_5882_);
                    lean_inc_ref(v_eqPr_5881_);
                    v___x_5890_ = lean_infer_type(
                        v_eqPr_5881_,
                        v___y_5882_,
                        v___y_5883_,
                        v___y_5884_,
                        v___y_5885_,
                    );
                    if lean_obj_tag(v___x_5890_) == 0 {
                        v_a_5891_ = lean_ctor_get(v___x_5890_, 0);
                        lean_inc(v_a_5891_);
                        lean_dec_ref_known(v___x_5890_, 1);
                        lean_inc(v___y_5885_);
                        lean_inc_ref(v___y_5884_);
                        lean_inc(v___y_5883_);
                        lean_inc_ref(v___y_5882_);
                        v___x_5892_ = lean_whnf(
                            v_a_5891_,
                            v___y_5882_,
                            v___y_5883_,
                            v___y_5884_,
                            v___y_5885_,
                        );
                        if lean_obj_tag(v___x_5892_) == 0 {
                            v_a_5893_ = lean_ctor_get(v___x_5892_, 0);
                            lean_inc(v_a_5893_);
                            lean_dec_ref_known(v___x_5892_, 1);
                            v_motive_5894_ = l_Lean_Expr_bindingBody_x21(v_motive_5875_);
                            v___x_5914_ = l_Lean_Expr_isHEq(v_a_5893_);
                            lean_dec(v_a_5893_);
                            if v___x_5914_ == 0 {
                                lean_inc_ref(v_eqPr_5881_);
                                v_major_5896_ = v_eqPr_5881_;
                                v___y_5897_ = v___y_5882_;
                                v___y_5898_ = v___y_5883_;
                                v___y_5899_ = v___y_5884_;
                                v___y_5900_ = v___y_5885_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc_ref(v_eqPr_5881_);
                                v___x_5915_ = l_Lean_Meta_mkEqOfHEq(
                                    v_eqPr_5881_,
                                    v___x_5914_,
                                    v___y_5882_,
                                    v___y_5883_,
                                    v___y_5884_,
                                    v___y_5885_,
                                );
                                if lean_obj_tag(v___x_5915_) == 0 {
                                    v_a_5916_ = lean_ctor_get(v___x_5915_, 0);
                                    lean_inc(v_a_5916_);
                                    lean_dec_ref_known(v___x_5915_, 1);
                                    v_major_5896_ = v_a_5916_;
                                    v___y_5897_ = v___y_5882_;
                                    v___y_5898_ = v___y_5883_;
                                    v___y_5899_ = v___y_5884_;
                                    v___y_5900_ = v___y_5885_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_motive_5894_);
                                    lean_dec(v_a_5889_);
                                    lean_dec_ref(v_eqPr_5881_);
                                    lean_dec_ref(v_a_5880_);
                                    lean_dec_ref(v_b_5877_);
                                    return v___x_5915_;
                                }
                            }
                        } else {
                            lean_dec(v_a_5889_);
                            lean_dec_ref(v_eqPr_5881_);
                            lean_dec_ref(v_a_5880_);
                            lean_dec_ref(v_b_5877_);
                            return v___x_5892_;
                        }
                    } else {
                        lean_dec(v_a_5889_);
                        lean_dec_ref(v_eqPr_5881_);
                        lean_dec_ref(v_a_5880_);
                        lean_dec_ref(v_b_5877_);
                        return v___x_5890_;
                    }
                } else {
                    lean_dec_ref(v_eqPr_5881_);
                    lean_dec_ref(v_a_5880_);
                    lean_dec_ref(v_b_5877_);
                    return v___x_5888_;
                }
            }
            1 => {
                v___x_5901_ = lean_mk_empty_array_with_capacity(v___x_5876_);
                lean_inc_ref(v_b_5877_);
                v___x_5902_ = lean_array_push(v___x_5901_, v_b_5877_);
                v___x_5903_ = 1;
                v___x_5904_ = 1;
                v___x_5905_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_5902_,
                    v_motive_5894_,
                    v___x_5878_,
                    v___x_5903_,
                    v___x_5878_,
                    v___x_5903_,
                    v___x_5904_,
                    v___y_5897_,
                    v___y_5898_,
                    v___y_5899_,
                    v___y_5900_,
                );
                lean_dec_ref(v___x_5902_);
                if lean_obj_tag(v___x_5905_) == 0 {
                    v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
                    lean_inc(v_a_5906_);
                    lean_dec_ref_known(v___x_5905_, 1);
                    v___x_5907_ = l_Lean_Meta_mkEqNDRec(
                        v_a_5906_,
                        v_a_5889_,
                        v_major_5896_,
                        v___y_5897_,
                        v___y_5898_,
                        v___y_5899_,
                        v___y_5900_,
                    );
                    if lean_obj_tag(v___x_5907_) == 0 {
                        v_a_5908_ = lean_ctor_get(v___x_5907_, 0);
                        lean_inc(v_a_5908_);
                        lean_dec_ref_known(v___x_5907_, 1);
                        v___x_5909_ = lean_mk_empty_array_with_capacity(v___x_5879_);
                        v___x_5910_ = lean_array_push(v___x_5909_, v_a_5880_);
                        v___x_5911_ = lean_array_push(v___x_5910_, v_b_5877_);
                        v___x_5912_ = lean_array_push(v___x_5911_, v_eqPr_5881_);
                        v___x_5913_ = l_Lean_Meta_mkLambdaFVars(
                            v___x_5912_,
                            v_a_5908_,
                            v___x_5878_,
                            v___x_5903_,
                            v___x_5878_,
                            v___x_5903_,
                            v___x_5904_,
                            v___y_5897_,
                            v___y_5898_,
                            v___y_5899_,
                            v___y_5900_,
                        );
                        lean_dec_ref(v___x_5912_);
                        return v___x_5913_;
                    } else {
                        lean_dec_ref(v_eqPr_5881_);
                        lean_dec_ref(v_a_5880_);
                        lean_dec_ref(v_b_5877_);
                        return v___x_5907_;
                    }
                } else {
                    lean_dec_ref(v_major_5896_);
                    lean_dec(v_a_5889_);
                    lean_dec_ref(v_eqPr_5881_);
                    lean_dec_ref(v_a_5880_);
                    lean_dec_ref(v_b_5877_);
                    return v___x_5905_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(
    mut v_type_5917_: *mut LeanObject,
    mut v_motive_5918_: *mut LeanObject,
    mut v___x_5919_: *mut LeanObject,
    mut v_b_5920_: *mut LeanObject,
    mut v___x_5921_: *mut LeanObject,
    mut v___x_5922_: *mut LeanObject,
    mut v_a_5923_: *mut LeanObject,
    mut v_eqPr_5924_: *mut LeanObject,
    mut v___y_5925_: *mut LeanObject,
    mut v___y_5926_: *mut LeanObject,
    mut v___y_5927_: *mut LeanObject,
    mut v___y_5928_: *mut LeanObject,
    mut v___y_5929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958__boxed_5930_: u8 = 0;
    let mut v_res_5931_: *mut LeanObject = core::ptr::null_mut();
    v___x_1958__boxed_5930_ = (lean_unbox(v___x_5921_) as u8);
    v_res_5931_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(
            v_type_5917_,
            v_motive_5918_,
            v___x_5919_,
            v_b_5920_,
            v___x_1958__boxed_5930_,
            v___x_5922_,
            v_a_5923_,
            v_eqPr_5924_,
            v___y_5925_,
            v___y_5926_,
            v___y_5927_,
            v___y_5928_,
        );
    lean_dec(v___y_5928_);
    lean_dec_ref(v___y_5927_);
    lean_dec(v___y_5926_);
    lean_dec_ref(v___y_5925_);
    lean_dec(v___x_5922_);
    lean_dec(v___x_5919_);
    lean_dec_ref(v_motive_5918_);
    lean_dec_ref(v_type_5917_);
    return v_res_5931_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(
    mut v___x_5932_: *mut LeanObject,
    mut v___x_5933_: *mut LeanObject,
    mut v_type_5934_: *mut LeanObject,
    mut v_a_5935_: *mut LeanObject,
    mut v___x_5936_: *mut LeanObject,
    mut v___x_5937_: u8,
    mut v___x_5938_: *mut LeanObject,
    mut v_b_5939_: *mut LeanObject,
    mut v_motive_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
    mut v___y_5942_: *mut LeanObject,
    mut v___y_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    v_b_5946_ = lean_array_get_borrowed(v___x_5932_, v_b_5939_, v___x_5933_);
    v___x_5947_ = l_Lean_Expr_bindingBody_x21(v_type_5934_);
    v_type_5948_ = lean_expr_instantiate1(v___x_5947_, v_a_5935_);
    lean_dec_ref(v___x_5947_);
    v___x_5949_ = lean_box((v___x_5937_) as usize);
    lean_inc(v_b_5946_);
    lean_inc_ref(v_motive_5940_);
    v___f_5950_ = lean_alloc_closure(
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        7,
    );
    lean_closure_set(v___f_5950_, 0, v_type_5948_);
    lean_closure_set(v___f_5950_, 1, v_motive_5940_);
    lean_closure_set(v___f_5950_, 2, v___x_5936_);
    lean_closure_set(v___f_5950_, 3, v_b_5946_);
    lean_closure_set(v___f_5950_, 4, v___x_5949_);
    lean_closure_set(v___f_5950_, 5, v___x_5938_);
    lean_closure_set(v___f_5950_, 6, v_a_5935_);
    v___x_5951_ = l_Lean_Expr_bindingName_x21(v_motive_5940_);
    v___x_5952_ = l_Lean_Expr_bindingDomain_x21(v_motive_5940_);
    lean_dec_ref(v_motive_5940_);
    v___x_5953_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_5951_, v___x_5952_, v___f_5950_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
    return v___x_5953_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(
    mut v___x_5954_: *mut LeanObject,
    mut v___x_5955_: *mut LeanObject,
    mut v_type_5956_: *mut LeanObject,
    mut v_a_5957_: *mut LeanObject,
    mut v___x_5958_: *mut LeanObject,
    mut v___x_5959_: *mut LeanObject,
    mut v___x_5960_: *mut LeanObject,
    mut v_b_5961_: *mut LeanObject,
    mut v_motive_5962_: *mut LeanObject,
    mut v___y_5963_: *mut LeanObject,
    mut v___y_5964_: *mut LeanObject,
    mut v___y_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
    mut v___y_5967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1917__boxed_5968_: u8 = 0;
    let mut v_res_5969_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917__boxed_5968_ = (lean_unbox(v___x_5959_) as u8);
    v_res_5969_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(
            v___x_5954_,
            v___x_5955_,
            v_type_5956_,
            v_a_5957_,
            v___x_5958_,
            v___x_1917__boxed_5968_,
            v___x_5960_,
            v_b_5961_,
            v_motive_5962_,
            v___y_5963_,
            v___y_5964_,
            v___y_5965_,
            v___y_5966_,
        );
    lean_dec(v___y_5966_);
    lean_dec_ref(v___y_5965_);
    lean_dec(v___y_5964_);
    lean_dec_ref(v___y_5963_);
    lean_dec_ref(v_b_5961_);
    lean_dec_ref(v_type_5956_);
    lean_dec(v___x_5955_);
    lean_dec_ref(v___x_5954_);
    return v_res_5969_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(
    mut v___x_5970_: *mut LeanObject,
    mut v___x_5971_: *mut LeanObject,
    mut v___x_5972_: u8,
    mut v___x_5973_: *mut LeanObject,
    mut v___x_5974_: *mut LeanObject,
    mut v_a_5975_: *mut LeanObject,
    mut v_type_5976_: *mut LeanObject,
    mut v___y_5977_: *mut LeanObject,
    mut v___y_5978_: *mut LeanObject,
    mut v___y_5979_: *mut LeanObject,
    mut v___y_5980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: u8 = 0;
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    v___x_5982_ = lean_unsigned_to_nat(0);
    v_a_5983_ = lean_array_get(v___x_5970_, v_a_5975_, v___x_5982_);
    v___x_5984_ = lean_box((v___x_5972_) as usize);
    lean_inc_ref(v_type_5976_);
    v___f_5985_ = lean_alloc_closure(
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed
            as *mut core::ffi::c_void,
        14,
        7,
    );
    lean_closure_set(v___f_5985_, 0, v___x_5970_);
    lean_closure_set(v___f_5985_, 1, v___x_5982_);
    lean_closure_set(v___f_5985_, 2, v_type_5976_);
    lean_closure_set(v___f_5985_, 3, v_a_5983_);
    lean_closure_set(v___f_5985_, 4, v___x_5971_);
    lean_closure_set(v___f_5985_, 5, v___x_5984_);
    lean_closure_set(v___f_5985_, 6, v___x_5973_);
    v___x_5986_ = 1;
    v___x_5987_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_5976_, v___x_5974_, v___f_5985_, v___x_5986_, v___x_5972_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_);
    return v___x_5987_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___boxed(
    mut v_type_5988_: *mut LeanObject,
    mut v_a_5989_: *mut LeanObject,
    mut v_a_5990_: *mut LeanObject,
    mut v_a_5991_: *mut LeanObject,
    mut v_a_5992_: *mut LeanObject,
    mut v_a_5993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5994_: *mut LeanObject = core::ptr::null_mut();
    v_res_5994_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(
        v_type_5988_,
        v_a_5989_,
        v_a_5990_,
        v_a_5991_,
        v_a_5992_,
    );
    lean_dec(v_a_5992_);
    lean_dec_ref(v_a_5991_);
    lean_dec(v_a_5990_);
    lean_dec_ref(v_a_5989_);
    return v_res_5994_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(
    mut v_lctx_5995_: *mut LeanObject,
    mut v_localInsts_5996_: *mut LeanObject,
    mut v_x_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6007_: u8 = 0;
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6011_: u8 = 0;
    let mut v_a_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6015_: u8 = 0;
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6003_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    lean_box(0),
                    v_lctx_5995_,
                    v_localInsts_5996_,
                    v_x_5997_,
                    v___y_5998_,
                    v___y_5999_,
                    v___y_6000_,
                    v___y_6001_,
                );
                if lean_obj_tag(v___x_6003_) == 0 {
                    v_a_6004_ = lean_ctor_get(v___x_6003_, 0);
                    v_isSharedCheck_6011_ = (!lean_is_exclusive(v___x_6003_)) as u8;
                    if v_isSharedCheck_6011_ == 0 {
                        v___x_6006_ = v___x_6003_;
                        v_isShared_6007_ = v_isSharedCheck_6011_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6004_);
                        lean_dec(v___x_6003_);
                        v___x_6006_ = lean_box(0);
                        v_isShared_6007_ = v_isSharedCheck_6011_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6012_ = lean_ctor_get(v___x_6003_, 0);
                    v_isSharedCheck_6019_ = (!lean_is_exclusive(v___x_6003_)) as u8;
                    if v_isSharedCheck_6019_ == 0 {
                        v___x_6014_ = v___x_6003_;
                        v_isShared_6015_ = v_isSharedCheck_6019_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6012_);
                        lean_dec(v___x_6003_);
                        v___x_6014_ = lean_box(0);
                        v_isShared_6015_ = v_isSharedCheck_6019_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6007_ == 0 {
                    v___x_6009_ = v___x_6006_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6010_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
                    v___x_6009_ = v_reuseFailAlloc_6010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6009_;
            }
            3 => {
                if v_isShared_6015_ == 0 {
                    v___x_6017_ = v___x_6014_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
                    v___x_6017_ = v_reuseFailAlloc_6018_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(
    mut v_lctx_6020_: *mut LeanObject,
    mut v_localInsts_6021_: *mut LeanObject,
    mut v_x_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
    mut v___y_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6028_: *mut LeanObject = core::ptr::null_mut();
    v_res_6028_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(
        v_lctx_6020_,
        v_localInsts_6021_,
        v_x_6022_,
        v___y_6023_,
        v___y_6024_,
        v___y_6025_,
        v___y_6026_,
    );
    lean_dec(v___y_6026_);
    lean_dec_ref(v___y_6025_);
    lean_dec(v___y_6024_);
    lean_dec_ref(v___y_6023_);
    return v_res_6028_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(
    mut v_00_u03b1_6029_: *mut LeanObject,
    mut v_lctx_6030_: *mut LeanObject,
    mut v_localInsts_6031_: *mut LeanObject,
    mut v_x_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
    mut v___y_6035_: *mut LeanObject,
    mut v___y_6036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    v___x_6038_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(
        v_lctx_6030_,
        v_localInsts_6031_,
        v_x_6032_,
        v___y_6033_,
        v___y_6034_,
        v___y_6035_,
        v___y_6036_,
    );
    return v___x_6038_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(
    mut v_00_u03b1_6039_: *mut LeanObject,
    mut v_lctx_6040_: *mut LeanObject,
    mut v_localInsts_6041_: *mut LeanObject,
    mut v_x_6042_: *mut LeanObject,
    mut v___y_6043_: *mut LeanObject,
    mut v___y_6044_: *mut LeanObject,
    mut v___y_6045_: *mut LeanObject,
    mut v___y_6046_: *mut LeanObject,
    mut v___y_6047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6048_: *mut LeanObject = core::ptr::null_mut();
    v_res_6048_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(
        v_00_u03b1_6039_,
        v_lctx_6040_,
        v_localInsts_6041_,
        v_x_6042_,
        v___y_6043_,
        v___y_6044_,
        v___y_6045_,
        v___y_6046_,
    );
    lean_dec(v___y_6046_);
    lean_dec_ref(v___y_6045_);
    lean_dec(v___y_6044_);
    lean_dec_ref(v___y_6043_);
    return v_res_6048_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(
    mut v_as_6049_: *mut LeanObject,
    mut v_sz_6050_: usize,
    mut v_i_6051_: usize,
    mut v_b_6052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6054_: u8 = 0;
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v_fst_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6065_: u8 = 0;
    let mut v_array_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: u8 = 0;
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6079_: u8 = 0;
    let mut v_array_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6098_: u8 = 0;
    let mut v_a_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: usize = 0;
    let mut v___x_6112_: usize = 0;
    let mut v_reuseFailAlloc_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_unused_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6122_: u8 = 0;
    let mut v_unused_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut v_unused_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6128_: u8 = 0;
    let mut v_unused_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6054_ = lean_usize_dec_lt(v_i_6051_, v_sz_6050_);
                if v___x_6054_ == 0 {
                    v___x_6055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6055_, 0, v_b_6052_);
                    return v___x_6055_;
                } else {
                    v_snd_6056_ = lean_ctor_get(v_b_6052_, 1);
                    lean_inc(v_snd_6056_);
                    v_snd_6057_ = lean_ctor_get(v_snd_6056_, 1);
                    lean_inc(v_snd_6057_);
                    v_fst_6058_ = lean_ctor_get(v_b_6052_, 0);
                    v_isSharedCheck_6128_ = (!lean_is_exclusive(v_b_6052_)) as u8;
                    if v_isSharedCheck_6128_ == 0 {
                        v_unused_6129_ = lean_ctor_get(v_b_6052_, 1);
                        lean_dec(v_unused_6129_);
                        v___x_6060_ = v_b_6052_;
                        v_isShared_6061_ = v_isSharedCheck_6128_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_6058_);
                        lean_dec(v_b_6052_);
                        v___x_6060_ = lean_box(0);
                        v_isShared_6061_ = v_isSharedCheck_6128_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6062_ = lean_ctor_get(v_snd_6056_, 0);
                v_isSharedCheck_6126_ = (!lean_is_exclusive(v_snd_6056_)) as u8;
                if v_isSharedCheck_6126_ == 0 {
                    v_unused_6127_ = lean_ctor_get(v_snd_6056_, 1);
                    lean_dec(v_unused_6127_);
                    v___x_6064_ = v_snd_6056_;
                    v_isShared_6065_ = v_isSharedCheck_6126_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_6062_);
                    lean_dec(v_snd_6056_);
                    v___x_6064_ = lean_box(0);
                    v_isShared_6065_ = v_isSharedCheck_6126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_array_6066_ = lean_ctor_get(v_snd_6057_, 0);
                v_start_6067_ = lean_ctor_get(v_snd_6057_, 1);
                v_stop_6068_ = lean_ctor_get(v_snd_6057_, 2);
                v___x_6069_ = lean_nat_dec_lt(v_start_6067_, v_stop_6068_);
                if v___x_6069_ == 0 {
                    if v_isShared_6065_ == 0 {
                        v___x_6071_ = v___x_6064_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6076_, 0, v_fst_6062_);
                        lean_ctor_set(v_reuseFailAlloc_6076_, 1, v_snd_6057_);
                        v___x_6071_ = v_reuseFailAlloc_6076_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_6068_);
                    lean_inc(v_start_6067_);
                    lean_inc_ref(v_array_6066_);
                    v_isSharedCheck_6122_ = (!lean_is_exclusive(v_snd_6057_)) as u8;
                    if v_isSharedCheck_6122_ == 0 {
                        v_unused_6123_ = lean_ctor_get(v_snd_6057_, 2);
                        lean_dec(v_unused_6123_);
                        v_unused_6124_ = lean_ctor_get(v_snd_6057_, 1);
                        lean_dec(v_unused_6124_);
                        v_unused_6125_ = lean_ctor_get(v_snd_6057_, 0);
                        lean_dec(v_unused_6125_);
                        v___x_6078_ = v_snd_6057_;
                        v_isShared_6079_ = v_isSharedCheck_6122_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_snd_6057_);
                        v___x_6078_ = lean_box(0);
                        v_isShared_6079_ = v_isSharedCheck_6122_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6061_ == 0 {
                    lean_ctor_set(v___x_6060_, 1, v___x_6071_);
                    v___x_6073_ = v___x_6060_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6075_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_fst_6058_);
                    lean_ctor_set(v_reuseFailAlloc_6075_, 1, v___x_6071_);
                    v___x_6073_ = v_reuseFailAlloc_6075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6074_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6074_, 0, v___x_6073_);
                return v___x_6074_;
            }
            5 => {
                v_array_6080_ = lean_ctor_get(v_fst_6062_, 0);
                v_start_6081_ = lean_ctor_get(v_fst_6062_, 1);
                v_stop_6082_ = lean_ctor_get(v_fst_6062_, 2);
                v___x_6083_ = lean_array_fget(v_array_6066_, v_start_6067_);
                v___x_6084_ = lean_unsigned_to_nat(1);
                v___x_6085_ = lean_nat_add(v_start_6067_, v___x_6084_);
                lean_dec(v_start_6067_);
                if v_isShared_6079_ == 0 {
                    lean_ctor_set(v___x_6078_, 1, v___x_6085_);
                    v___x_6087_ = v___x_6078_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6121_, 0, v_array_6066_);
                    lean_ctor_set(v_reuseFailAlloc_6121_, 1, v___x_6085_);
                    lean_ctor_set(v_reuseFailAlloc_6121_, 2, v_stop_6068_);
                    v___x_6087_ = v_reuseFailAlloc_6121_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6088_ = lean_nat_dec_lt(v_start_6081_, v_stop_6082_);
                if v___x_6088_ == 0 {
                    lean_dec(v___x_6083_);
                    if v_isShared_6065_ == 0 {
                        lean_ctor_set(v___x_6064_, 1, v___x_6087_);
                        v___x_6090_ = v___x_6064_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6095_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6095_, 0, v_fst_6062_);
                        lean_ctor_set(v_reuseFailAlloc_6095_, 1, v___x_6087_);
                        v___x_6090_ = v_reuseFailAlloc_6095_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_6082_);
                    lean_inc(v_start_6081_);
                    lean_inc_ref(v_array_6080_);
                    v_isSharedCheck_6117_ = (!lean_is_exclusive(v_fst_6062_)) as u8;
                    if v_isSharedCheck_6117_ == 0 {
                        v_unused_6118_ = lean_ctor_get(v_fst_6062_, 2);
                        lean_dec(v_unused_6118_);
                        v_unused_6119_ = lean_ctor_get(v_fst_6062_, 1);
                        lean_dec(v_unused_6119_);
                        v_unused_6120_ = lean_ctor_get(v_fst_6062_, 0);
                        lean_dec(v_unused_6120_);
                        v___x_6097_ = v_fst_6062_;
                        v_isShared_6098_ = v_isSharedCheck_6117_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v_fst_6062_);
                        v___x_6097_ = lean_box(0);
                        v_isShared_6098_ = v_isSharedCheck_6117_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_6061_ == 0 {
                    lean_ctor_set(v___x_6060_, 1, v___x_6090_);
                    v___x_6092_ = v___x_6060_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6094_, 0, v_fst_6058_);
                    lean_ctor_set(v_reuseFailAlloc_6094_, 1, v___x_6090_);
                    v___x_6092_ = v_reuseFailAlloc_6094_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6093_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6093_, 0, v___x_6092_);
                return v___x_6093_;
            }
            9 => {
                v_a_6099_ = lean_array_uget_borrowed(v_as_6049_, v_i_6051_);
                v___x_6100_ = lean_array_fget(v_array_6080_, v_start_6081_);
                v___x_6101_ = lean_nat_add(v_start_6081_, v___x_6084_);
                lean_dec(v_start_6081_);
                if v_isShared_6098_ == 0 {
                    lean_ctor_set(v___x_6097_, 1, v___x_6101_);
                    v___x_6103_ = v___x_6097_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_array_6080_);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 1, v___x_6101_);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 2, v_stop_6082_);
                    v___x_6103_ = v_reuseFailAlloc_6116_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_inc(v_a_6099_);
                v___x_6104_ = lean_array_push(v_fst_6058_, v_a_6099_);
                v___x_6105_ = lean_array_push(v___x_6104_, v___x_6100_);
                v___x_6106_ = lean_array_push(v___x_6105_, v___x_6083_);
                if v_isShared_6065_ == 0 {
                    lean_ctor_set(v___x_6064_, 1, v___x_6087_);
                    lean_ctor_set(v___x_6064_, 0, v___x_6103_);
                    v___x_6108_ = v___x_6064_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6115_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6115_, 0, v___x_6103_);
                    lean_ctor_set(v_reuseFailAlloc_6115_, 1, v___x_6087_);
                    v___x_6108_ = v_reuseFailAlloc_6115_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_6061_ == 0 {
                    lean_ctor_set(v___x_6060_, 1, v___x_6108_);
                    lean_ctor_set(v___x_6060_, 0, v___x_6106_);
                    v___x_6110_ = v___x_6060_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6114_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6114_, 0, v___x_6106_);
                    lean_ctor_set(v_reuseFailAlloc_6114_, 1, v___x_6108_);
                    v___x_6110_ = v_reuseFailAlloc_6114_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6111_ = 1usize;
                v___x_6112_ = lean_usize_add(v_i_6051_, v___x_6111_);
                v_i_6051_ = v___x_6112_;
                v_b_6052_ = v___x_6110_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(
    mut v_as_6130_: *mut LeanObject,
    mut v_sz_6131_: *mut LeanObject,
    mut v_i_6132_: *mut LeanObject,
    mut v_b_6133_: *mut LeanObject,
    mut v___y_6134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6135_: usize = 0;
    let mut v_i_boxed_6136_: usize = 0;
    let mut v_res_6137_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6135_ = lean_unbox_usize(v_sz_6131_);
    lean_dec(v_sz_6131_);
    v_i_boxed_6136_ = lean_unbox_usize(v_i_6132_);
    lean_dec(v_i_6132_);
    v_res_6137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_6130_, v_sz_boxed_6135_, v_i_boxed_6136_, v_b_6133_);
    lean_dec_ref(v_as_6130_);
    return v_res_6137_;
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity___lam__0(
    mut v_ys_6138_: *mut LeanObject,
    mut v_xs_6139_: *mut LeanObject,
    mut v_f_6140_: *mut LeanObject,
    mut v___x_6141_: u8,
    mut v___x_6142_: u8,
    mut v_eqs_6143_: *mut LeanObject,
    mut v_argKinds_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6158_: usize = 0;
    let mut v___x_6159_: usize = 0;
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: u8 = 0;
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6174_: u8 = 0;
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6179_: u8 = 0;
    let mut v_a_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6183_: u8 = 0;
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6187_: u8 = 0;
    let mut v_a_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6191_: u8 = 0;
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6195_: u8 = 0;
    let mut v_a_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6199_: u8 = 0;
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6203_: u8 = 0;
    let mut v_a_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6207_: u8 = 0;
    let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6150_ = lean_unsigned_to_nat(0);
                v___x_6151_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0;
                v___x_6152_ = lean_array_get_size(v_ys_6138_);
                lean_inc_ref(v_ys_6138_);
                v___x_6153_ = l_Array_toSubarray___redArg(v_ys_6138_, v___x_6150_, v___x_6152_);
                v___x_6154_ = lean_array_get_size(v_eqs_6143_);
                v___x_6155_ = l_Array_toSubarray___redArg(v_eqs_6143_, v___x_6150_, v___x_6154_);
                v___x_6156_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6156_, 0, v___x_6153_);
                lean_ctor_set(v___x_6156_, 1, v___x_6155_);
                v___x_6157_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6157_, 0, v___x_6151_);
                lean_ctor_set(v___x_6157_, 1, v___x_6156_);
                v_sz_6158_ = lean_array_size(v_xs_6139_);
                v___x_6159_ = 0usize;
                v___x_6160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_xs_6139_, v_sz_6158_, v___x_6159_, v___x_6157_);
                if lean_obj_tag(v___x_6160_) == 0 {
                    v_a_6161_ = lean_ctor_get(v___x_6160_, 0);
                    lean_inc(v_a_6161_);
                    lean_dec_ref_known(v___x_6160_, 1);
                    lean_inc_ref(v_f_6140_);
                    v___x_6162_ = l_Lean_mkAppN(v_f_6140_, v_xs_6139_);
                    v___x_6163_ = l_Lean_mkAppN(v_f_6140_, v_ys_6138_);
                    lean_dec_ref(v_ys_6138_);
                    v___x_6164_ = l_Lean_Meta_mkHEq(
                        v___x_6162_,
                        v___x_6163_,
                        v___y_6145_,
                        v___y_6146_,
                        v___y_6147_,
                        v___y_6148_,
                    );
                    if lean_obj_tag(v___x_6164_) == 0 {
                        v_a_6165_ = lean_ctor_get(v___x_6164_, 0);
                        lean_inc(v_a_6165_);
                        lean_dec_ref_known(v___x_6164_, 1);
                        v_fst_6166_ = lean_ctor_get(v_a_6161_, 0);
                        lean_inc(v_fst_6166_);
                        lean_dec(v_a_6161_);
                        v___x_6167_ = 1;
                        v___x_6168_ = l_Lean_Meta_mkForallFVars(
                            v_fst_6166_,
                            v_a_6165_,
                            v___x_6141_,
                            v___x_6142_,
                            v___x_6142_,
                            v___x_6167_,
                            v___y_6145_,
                            v___y_6146_,
                            v___y_6147_,
                            v___y_6148_,
                        );
                        lean_dec(v_fst_6166_);
                        if lean_obj_tag(v___x_6168_) == 0 {
                            v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
                            lean_inc_n(v_a_6169_, 2);
                            lean_dec_ref_known(v___x_6168_, 1);
                            v___x_6170_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_a_6169_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
                            if lean_obj_tag(v___x_6170_) == 0 {
                                v_a_6171_ = lean_ctor_get(v___x_6170_, 0);
                                v_isSharedCheck_6179_ = (!lean_is_exclusive(v___x_6170_)) as u8;
                                if v_isSharedCheck_6179_ == 0 {
                                    v___x_6173_ = v___x_6170_;
                                    v_isShared_6174_ = v_isSharedCheck_6179_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_6171_);
                                    lean_dec(v___x_6170_);
                                    v___x_6173_ = lean_box(0);
                                    v_isShared_6174_ = v_isSharedCheck_6179_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_6169_);
                                lean_dec_ref(v_argKinds_6144_);
                                v_a_6180_ = lean_ctor_get(v___x_6170_, 0);
                                v_isSharedCheck_6187_ = (!lean_is_exclusive(v___x_6170_)) as u8;
                                if v_isSharedCheck_6187_ == 0 {
                                    v___x_6182_ = v___x_6170_;
                                    v_isShared_6183_ = v_isSharedCheck_6187_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6180_);
                                    lean_dec(v___x_6170_);
                                    v___x_6182_ = lean_box(0);
                                    v_isShared_6183_ = v_isSharedCheck_6187_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_argKinds_6144_);
                            v_a_6188_ = lean_ctor_get(v___x_6168_, 0);
                            v_isSharedCheck_6195_ = (!lean_is_exclusive(v___x_6168_)) as u8;
                            if v_isSharedCheck_6195_ == 0 {
                                v___x_6190_ = v___x_6168_;
                                v_isShared_6191_ = v_isSharedCheck_6195_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6188_);
                                lean_dec(v___x_6168_);
                                v___x_6190_ = lean_box(0);
                                v_isShared_6191_ = v_isSharedCheck_6195_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6161_);
                        lean_dec_ref(v_argKinds_6144_);
                        v_a_6196_ = lean_ctor_get(v___x_6164_, 0);
                        v_isSharedCheck_6203_ = (!lean_is_exclusive(v___x_6164_)) as u8;
                        if v_isSharedCheck_6203_ == 0 {
                            v___x_6198_ = v___x_6164_;
                            v_isShared_6199_ = v_isSharedCheck_6203_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6196_);
                            lean_dec(v___x_6164_);
                            v___x_6198_ = lean_box(0);
                            v_isShared_6199_ = v_isSharedCheck_6203_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_argKinds_6144_);
                    lean_dec_ref(v_f_6140_);
                    lean_dec_ref(v_ys_6138_);
                    v_a_6204_ = lean_ctor_get(v___x_6160_, 0);
                    v_isSharedCheck_6211_ = (!lean_is_exclusive(v___x_6160_)) as u8;
                    if v_isSharedCheck_6211_ == 0 {
                        v___x_6206_ = v___x_6160_;
                        v_isShared_6207_ = v_isSharedCheck_6211_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6204_);
                        lean_dec(v___x_6160_);
                        v___x_6206_ = lean_box(0);
                        v_isShared_6207_ = v_isSharedCheck_6211_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6175_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6175_, 0, v_a_6169_);
                lean_ctor_set(v___x_6175_, 1, v_a_6171_);
                lean_ctor_set(v___x_6175_, 2, v_argKinds_6144_);
                if v_isShared_6174_ == 0 {
                    lean_ctor_set(v___x_6173_, 0, v___x_6175_);
                    v___x_6177_ = v___x_6173_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6178_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6178_, 0, v___x_6175_);
                    v___x_6177_ = v_reuseFailAlloc_6178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6177_;
            }
            3 => {
                if v_isShared_6183_ == 0 {
                    v___x_6185_ = v___x_6182_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_a_6180_);
                    v___x_6185_ = v_reuseFailAlloc_6186_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6185_;
            }
            5 => {
                if v_isShared_6191_ == 0 {
                    v___x_6193_ = v___x_6190_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6194_, 0, v_a_6188_);
                    v___x_6193_ = v_reuseFailAlloc_6194_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6193_;
            }
            7 => {
                if v_isShared_6199_ == 0 {
                    v___x_6201_ = v___x_6198_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6202_, 0, v_a_6196_);
                    v___x_6201_ = v_reuseFailAlloc_6202_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6201_;
            }
            9 => {
                if v_isShared_6207_ == 0 {
                    v___x_6209_ = v___x_6206_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6210_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6210_, 0, v_a_6204_);
                    v___x_6209_ = v_reuseFailAlloc_6210_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(
    mut v_ys_6212_: *mut LeanObject,
    mut v_xs_6213_: *mut LeanObject,
    mut v_f_6214_: *mut LeanObject,
    mut v___x_6215_: *mut LeanObject,
    mut v___x_6216_: *mut LeanObject,
    mut v_eqs_6217_: *mut LeanObject,
    mut v_argKinds_6218_: *mut LeanObject,
    mut v___y_6219_: *mut LeanObject,
    mut v___y_6220_: *mut LeanObject,
    mut v___y_6221_: *mut LeanObject,
    mut v___y_6222_: *mut LeanObject,
    mut v___y_6223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4841__boxed_6224_: u8 = 0;
    let mut v___x_4842__boxed_6225_: u8 = 0;
    let mut v_res_6226_: *mut LeanObject = core::ptr::null_mut();
    v___x_4841__boxed_6224_ = (lean_unbox(v___x_6215_) as u8);
    v___x_4842__boxed_6225_ = (lean_unbox(v___x_6216_) as u8);
    v_res_6226_ = l_Lean_Meta_mkHCongrWithArity___lam__0(
        v_ys_6212_,
        v_xs_6213_,
        v_f_6214_,
        v___x_4841__boxed_6224_,
        v___x_4842__boxed_6225_,
        v_eqs_6217_,
        v_argKinds_6218_,
        v___y_6219_,
        v___y_6220_,
        v___y_6221_,
        v___y_6222_,
    );
    lean_dec(v___y_6222_);
    lean_dec_ref(v___y_6221_);
    lean_dec(v___y_6220_);
    lean_dec_ref(v___y_6219_);
    lean_dec_ref(v_xs_6213_);
    return v_res_6226_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(
    mut v_msgData_6227_: *mut LeanObject,
    mut v___y_6228_: *mut LeanObject,
    mut v___y_6229_: *mut LeanObject,
    mut v___y_6230_: *mut LeanObject,
    mut v___y_6231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    v___x_6233_ = lean_st_ref_get(v___y_6231_);
    v_env_6234_ = lean_ctor_get(v___x_6233_, 0);
    lean_inc_ref(v_env_6234_);
    lean_dec(v___x_6233_);
    v___x_6235_ = lean_st_ref_get(v___y_6229_);
    v_mctx_6236_ = lean_ctor_get(v___x_6235_, 0);
    lean_inc_ref(v_mctx_6236_);
    lean_dec(v___x_6235_);
    v_lctx_6237_ = lean_ctor_get(v___y_6228_, 2);
    v_options_6238_ = lean_ctor_get(v___y_6230_, 2);
    lean_inc_ref(v_options_6238_);
    lean_inc_ref(v_lctx_6237_);
    v___x_6239_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_6239_, 0, v_env_6234_);
    lean_ctor_set(v___x_6239_, 1, v_mctx_6236_);
    lean_ctor_set(v___x_6239_, 2, v_lctx_6237_);
    lean_ctor_set(v___x_6239_, 3, v_options_6238_);
    v___x_6240_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_6240_, 0, v___x_6239_);
    lean_ctor_set(v___x_6240_, 1, v_msgData_6227_);
    v___x_6241_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6241_, 0, v___x_6240_);
    return v___x_6241_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0___boxed(
    mut v_msgData_6242_: *mut LeanObject,
    mut v___y_6243_: *mut LeanObject,
    mut v___y_6244_: *mut LeanObject,
    mut v___y_6245_: *mut LeanObject,
    mut v___y_6246_: *mut LeanObject,
    mut v___y_6247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6248_: *mut LeanObject = core::ptr::null_mut();
    v_res_6248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msgData_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
    lean_dec(v___y_6246_);
    lean_dec_ref(v___y_6245_);
    lean_dec(v___y_6244_);
    lean_dec_ref(v___y_6243_);
    return v_res_6248_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(
    mut v_msg_6249_: *mut LeanObject,
    mut v___y_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6260_: u8 = 0;
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6255_ = lean_ctor_get(v___y_6252_, 5);
                v___x_6256_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
                v_a_6257_ = lean_ctor_get(v___x_6256_, 0);
                v_isSharedCheck_6265_ = (!lean_is_exclusive(v___x_6256_)) as u8;
                if v_isSharedCheck_6265_ == 0 {
                    v___x_6259_ = v___x_6256_;
                    v_isShared_6260_ = v_isSharedCheck_6265_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6257_);
                    lean_dec(v___x_6256_);
                    v___x_6259_ = lean_box(0);
                    v_isShared_6260_ = v_isSharedCheck_6265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_6255_);
                v___x_6261_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6261_, 0, v_ref_6255_);
                lean_ctor_set(v___x_6261_, 1, v_a_6257_);
                if v_isShared_6260_ == 0 {
                    lean_ctor_set_tag(v___x_6259_, 1);
                    lean_ctor_set(v___x_6259_, 0, v___x_6261_);
                    v___x_6263_ = v___x_6259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6264_, 0, v___x_6261_);
                    v___x_6263_ = v_reuseFailAlloc_6264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(
    mut v_msg_6266_: *mut LeanObject,
    mut v___y_6267_: *mut LeanObject,
    mut v___y_6268_: *mut LeanObject,
    mut v___y_6269_: *mut LeanObject,
    mut v___y_6270_: *mut LeanObject,
    mut v___y_6271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6272_: *mut LeanObject = core::ptr::null_mut();
    v_res_6272_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(
        v_msg_6266_,
        v___y_6267_,
        v___y_6268_,
        v___y_6269_,
        v___y_6270_,
    );
    lean_dec(v___y_6270_);
    lean_dec_ref(v___y_6269_);
    lean_dec(v___y_6268_);
    lean_dec_ref(v___y_6267_);
    return v_res_6272_;
}
pub unsafe fn _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    v___x_6274_ = l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0;
    v___x_6275_ = l_Lean_stringToMessageData(v___x_6274_);
    return v___x_6275_;
}
pub unsafe fn _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    v___x_6277_ = l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2;
    v___x_6278_ = l_Lean_stringToMessageData(v___x_6277_);
    return v___x_6278_;
}
pub unsafe fn _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5() -> *mut LeanObject {
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    v___x_6280_ = l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4;
    v___x_6281_ = l_Lean_stringToMessageData(v___x_6280_);
    return v___x_6281_;
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity___lam__1(
    mut v_xs_6282_: *mut LeanObject,
    mut v_numArgs_6283_: *mut LeanObject,
    mut v_f_6284_: *mut LeanObject,
    mut v_ys_6285_: *mut LeanObject,
    mut v_x_6286_: *mut LeanObject,
    mut v___y_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
    mut v___y_6289_: *mut LeanObject,
    mut v___y_6290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: u8 = 0;
    v___x_6292_ = lean_array_get_size(v_xs_6282_);
    v___x_6293_ = lean_nat_dec_eq(v___x_6292_, v_numArgs_6283_);
    if v___x_6293_ == 0 {
        let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ys_6285_);
        lean_dec_ref(v_xs_6282_);
        v___x_6294_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once),
            _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1,
        );
        v___x_6295_ = l_Nat_reprFast(v_numArgs_6283_);
        v___x_6296_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_6296_, 0, v___x_6295_);
        v___x_6297_ = l_Lean_MessageData_ofFormat(v___x_6296_);
        v___x_6298_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_6298_, 0, v___x_6294_);
        lean_ctor_set(v___x_6298_, 1, v___x_6297_);
        v___x_6299_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once),
            _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3,
        );
        v___x_6300_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_6300_, 0, v___x_6298_);
        lean_ctor_set(v___x_6300_, 1, v___x_6299_);
        v___x_6301_ = l_Nat_reprFast(v___x_6292_);
        v___x_6302_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_6302_, 0, v___x_6301_);
        v___x_6303_ = l_Lean_MessageData_ofFormat(v___x_6302_);
        v___x_6304_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_6304_, 0, v___x_6300_);
        lean_ctor_set(v___x_6304_, 1, v___x_6303_);
        v___x_6305_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5),
            core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once),
            _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5,
        );
        v___x_6306_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_6306_, 0, v___x_6304_);
        lean_ctor_set(v___x_6306_, 1, v___x_6305_);
        v___x_6307_ = l_Lean_indentExpr(v_f_6284_);
        v___x_6308_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_6308_, 0, v___x_6306_);
        lean_ctor_set(v___x_6308_, 1, v___x_6307_);
        v___x_6309_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(
            v___x_6308_,
            v___y_6287_,
            v___y_6288_,
            v___y_6289_,
            v___y_6290_,
        );
        return v___x_6309_;
    } else {
        let mut v_lctx_6310_: *mut LeanObject = core::ptr::null_mut();
        let mut v_localInstances_6311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6312_: u8 = 0;
        let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_numArgs_6283_);
        v_lctx_6310_ = lean_ctor_get(v___y_6287_, 2);
        v_localInstances_6311_ = lean_ctor_get(v___y_6287_, 3);
        v___x_6312_ = 0;
        v___x_6313_ = lean_box((v___x_6312_) as usize);
        v___x_6314_ = lean_box((v___x_6293_) as usize);
        lean_inc_ref(v_xs_6282_);
        lean_inc_ref(v_ys_6285_);
        v___f_6315_ = lean_alloc_closure(
            l_Lean_Meta_mkHCongrWithArity___lam__0___boxed as *mut core::ffi::c_void,
            12,
            5,
        );
        lean_closure_set(v___f_6315_, 0, v_ys_6285_);
        lean_closure_set(v___f_6315_, 1, v_xs_6282_);
        lean_closure_set(v___f_6315_, 2, v_f_6284_);
        lean_closure_set(v___f_6315_, 3, v___x_6313_);
        lean_closure_set(v___f_6315_, 4, v___x_6314_);
        lean_inc_ref(v_lctx_6310_);
        v___x_6316_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(
            v_ys_6285_,
            v_lctx_6310_,
        );
        v___x_6317_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(
            v_ys_6285_,
            v___x_6316_,
        );
        v___x_6318_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(
            v_xs_6282_,
            v___x_6317_,
        );
        v___x_6319_ = lean_alloc_closure(
            l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed
                as *mut core::ffi::c_void,
            9,
            4,
        );
        lean_closure_set(v___x_6319_, 0, lean_box(0));
        lean_closure_set(v___x_6319_, 1, v_xs_6282_);
        lean_closure_set(v___x_6319_, 2, v_ys_6285_);
        lean_closure_set(v___x_6319_, 3, v___f_6315_);
        lean_inc_ref(v_localInstances_6311_);
        v___x_6320_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(
            v___x_6318_,
            v_localInstances_6311_,
            v___x_6319_,
            v___y_6287_,
            v___y_6288_,
            v___y_6289_,
            v___y_6290_,
        );
        return v___x_6320_;
    }
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(
    mut v_xs_6321_: *mut LeanObject,
    mut v_numArgs_6322_: *mut LeanObject,
    mut v_f_6323_: *mut LeanObject,
    mut v_ys_6324_: *mut LeanObject,
    mut v_x_6325_: *mut LeanObject,
    mut v___y_6326_: *mut LeanObject,
    mut v___y_6327_: *mut LeanObject,
    mut v___y_6328_: *mut LeanObject,
    mut v___y_6329_: *mut LeanObject,
    mut v___y_6330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6331_: *mut LeanObject = core::ptr::null_mut();
    v_res_6331_ = l_Lean_Meta_mkHCongrWithArity___lam__1(
        v_xs_6321_,
        v_numArgs_6322_,
        v_f_6323_,
        v_ys_6324_,
        v_x_6325_,
        v___y_6326_,
        v___y_6327_,
        v___y_6328_,
        v___y_6329_,
    );
    lean_dec(v___y_6329_);
    lean_dec_ref(v___y_6328_);
    lean_dec(v___y_6327_);
    lean_dec_ref(v___y_6326_);
    lean_dec_ref(v_x_6325_);
    return v_res_6331_;
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity___lam__2(
    mut v_numArgs_6332_: *mut LeanObject,
    mut v_f_6333_: *mut LeanObject,
    mut v_a_6334_: *mut LeanObject,
    mut v___x_6335_: *mut LeanObject,
    mut v_xs_6336_: *mut LeanObject,
    mut v_x_6337_: *mut LeanObject,
    mut v___y_6338_: *mut LeanObject,
    mut v___y_6339_: *mut LeanObject,
    mut v___y_6340_: *mut LeanObject,
    mut v___y_6341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: u8 = 0;
    let mut v___x_6345_: u8 = 0;
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    v___f_6343_ = lean_alloc_closure(
        l_Lean_Meta_mkHCongrWithArity___lam__1___boxed as *mut core::ffi::c_void,
        10,
        3,
    );
    lean_closure_set(v___f_6343_, 0, v_xs_6336_);
    lean_closure_set(v___f_6343_, 1, v_numArgs_6332_);
    lean_closure_set(v___f_6343_, 2, v_f_6333_);
    v___x_6344_ = 1;
    v___x_6345_ = 0;
    v___x_6346_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_6334_, v___x_6335_, v___f_6343_, v___x_6344_, v___x_6345_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_);
    return v___x_6346_;
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(
    mut v_numArgs_6347_: *mut LeanObject,
    mut v_f_6348_: *mut LeanObject,
    mut v_a_6349_: *mut LeanObject,
    mut v___x_6350_: *mut LeanObject,
    mut v_xs_6351_: *mut LeanObject,
    mut v_x_6352_: *mut LeanObject,
    mut v___y_6353_: *mut LeanObject,
    mut v___y_6354_: *mut LeanObject,
    mut v___y_6355_: *mut LeanObject,
    mut v___y_6356_: *mut LeanObject,
    mut v___y_6357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6358_: *mut LeanObject = core::ptr::null_mut();
    v_res_6358_ = l_Lean_Meta_mkHCongrWithArity___lam__2(
        v_numArgs_6347_,
        v_f_6348_,
        v_a_6349_,
        v___x_6350_,
        v_xs_6351_,
        v_x_6352_,
        v___y_6353_,
        v___y_6354_,
        v___y_6355_,
        v___y_6356_,
    );
    lean_dec(v___y_6356_);
    lean_dec_ref(v___y_6355_);
    lean_dec(v___y_6354_);
    lean_dec_ref(v___y_6353_);
    lean_dec_ref(v_x_6352_);
    return v_res_6358_;
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity(
    mut v_f_6359_: *mut LeanObject,
    mut v_numArgs_6360_: *mut LeanObject,
    mut v_a_6361_: *mut LeanObject,
    mut v_a_6362_: *mut LeanObject,
    mut v_a_6363_: *mut LeanObject,
    mut v_a_6364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: u8 = 0;
    let mut v___x_6371_: u8 = 0;
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_6364_);
                lean_inc_ref(v_a_6363_);
                lean_inc(v_a_6362_);
                lean_inc_ref(v_a_6361_);
                lean_inc_ref(v_f_6359_);
                v___x_6366_ =
                    lean_infer_type(v_f_6359_, v_a_6361_, v_a_6362_, v_a_6363_, v_a_6364_);
                if lean_obj_tag(v___x_6366_) == 0 {
                    v_a_6367_ = lean_ctor_get(v___x_6366_, 0);
                    lean_inc_n(v_a_6367_, 2);
                    lean_dec_ref_known(v___x_6366_, 1);
                    lean_inc(v_numArgs_6360_);
                    v___x_6368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6368_, 0, v_numArgs_6360_);
                    lean_inc_ref(v___x_6368_);
                    v___f_6369_ = lean_alloc_closure(
                        l_Lean_Meta_mkHCongrWithArity___lam__2___boxed as *mut core::ffi::c_void,
                        11,
                        4,
                    );
                    lean_closure_set(v___f_6369_, 0, v_numArgs_6360_);
                    lean_closure_set(v___f_6369_, 1, v_f_6359_);
                    lean_closure_set(v___f_6369_, 2, v_a_6367_);
                    lean_closure_set(v___f_6369_, 3, v___x_6368_);
                    v___x_6370_ = 1;
                    v___x_6371_ = 0;
                    v___x_6372_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_6367_, v___x_6368_, v___f_6369_, v___x_6370_, v___x_6371_, v_a_6361_, v_a_6362_, v_a_6363_, v_a_6364_);
                    return v___x_6372_;
                } else {
                    lean_dec(v_numArgs_6360_);
                    lean_dec_ref(v_f_6359_);
                    v_a_6373_ = lean_ctor_get(v___x_6366_, 0);
                    v_isSharedCheck_6380_ = (!lean_is_exclusive(v___x_6366_)) as u8;
                    if v_isSharedCheck_6380_ == 0 {
                        v___x_6375_ = v___x_6366_;
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6373_);
                        lean_dec(v___x_6366_);
                        v___x_6375_ = lean_box(0);
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6376_ == 0 {
                    v___x_6378_ = v___x_6375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6379_, 0, v_a_6373_);
                    v___x_6378_ = v_reuseFailAlloc_6379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArity___boxed(
    mut v_f_6381_: *mut LeanObject,
    mut v_numArgs_6382_: *mut LeanObject,
    mut v_a_6383_: *mut LeanObject,
    mut v_a_6384_: *mut LeanObject,
    mut v_a_6385_: *mut LeanObject,
    mut v_a_6386_: *mut LeanObject,
    mut v_a_6387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6388_: *mut LeanObject = core::ptr::null_mut();
    v_res_6388_ = l_Lean_Meta_mkHCongrWithArity(
        v_f_6381_,
        v_numArgs_6382_,
        v_a_6383_,
        v_a_6384_,
        v_a_6385_,
        v_a_6386_,
    );
    lean_dec(v_a_6386_);
    lean_dec_ref(v_a_6385_);
    lean_dec(v_a_6384_);
    lean_dec_ref(v_a_6383_);
    return v_res_6388_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(
    mut v_00_u03b1_6389_: *mut LeanObject,
    mut v_msg_6390_: *mut LeanObject,
    mut v___y_6391_: *mut LeanObject,
    mut v___y_6392_: *mut LeanObject,
    mut v___y_6393_: *mut LeanObject,
    mut v___y_6394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    v___x_6396_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(
        v_msg_6390_,
        v___y_6391_,
        v___y_6392_,
        v___y_6393_,
        v___y_6394_,
    );
    return v___x_6396_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(
    mut v_00_u03b1_6397_: *mut LeanObject,
    mut v_msg_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
    mut v___y_6402_: *mut LeanObject,
    mut v___y_6403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6404_: *mut LeanObject = core::ptr::null_mut();
    v_res_6404_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(
        v_00_u03b1_6397_,
        v_msg_6398_,
        v___y_6399_,
        v___y_6400_,
        v___y_6401_,
        v___y_6402_,
    );
    lean_dec(v___y_6402_);
    lean_dec_ref(v___y_6401_);
    lean_dec(v___y_6400_);
    lean_dec_ref(v___y_6399_);
    return v_res_6404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(
    mut v_as_6405_: *mut LeanObject,
    mut v_sz_6406_: usize,
    mut v_i_6407_: usize,
    mut v_b_6408_: *mut LeanObject,
    mut v___y_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    v___x_6414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_6405_, v_sz_6406_, v_i_6407_, v_b_6408_);
    return v___x_6414_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(
    mut v_as_6415_: *mut LeanObject,
    mut v_sz_6416_: *mut LeanObject,
    mut v_i_6417_: *mut LeanObject,
    mut v_b_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6424_: usize = 0;
    let mut v_i_boxed_6425_: usize = 0;
    let mut v_res_6426_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6424_ = lean_unbox_usize(v_sz_6416_);
    lean_dec(v_sz_6416_);
    v_i_boxed_6425_ = lean_unbox_usize(v_i_6417_);
    lean_dec(v_i_6417_);
    v_res_6426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_as_6415_, v_sz_boxed_6424_, v_i_boxed_6425_, v_b_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_);
    lean_dec(v___y_6422_);
    lean_dec_ref(v___y_6421_);
    lean_dec(v___y_6420_);
    lean_dec_ref(v___y_6419_);
    lean_dec_ref(v_as_6415_);
    return v_res_6426_;
}
pub unsafe fn l_Lean_Meta_mkHCongr(
    mut v_f_6427_: *mut LeanObject,
    mut v_a_6428_: *mut LeanObject,
    mut v_a_6429_: *mut LeanObject,
    mut v_a_6430_: *mut LeanObject,
    mut v_a_6431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6441_: u8 = 0;
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6433_ = lean_box(0);
                lean_inc_ref(v_f_6427_);
                v___x_6434_ = l_Lean_Meta_getFunInfo(
                    v_f_6427_,
                    v___x_6433_,
                    v_a_6428_,
                    v_a_6429_,
                    v_a_6430_,
                    v_a_6431_,
                );
                if lean_obj_tag(v___x_6434_) == 0 {
                    v_a_6435_ = lean_ctor_get(v___x_6434_, 0);
                    lean_inc(v_a_6435_);
                    lean_dec_ref_known(v___x_6434_, 1);
                    v___x_6436_ = l_Lean_Meta_FunInfo_getArity(v_a_6435_);
                    lean_dec(v_a_6435_);
                    v___x_6437_ = l_Lean_Meta_mkHCongrWithArity(
                        v_f_6427_,
                        v___x_6436_,
                        v_a_6428_,
                        v_a_6429_,
                        v_a_6430_,
                        v_a_6431_,
                    );
                    return v___x_6437_;
                } else {
                    lean_dec_ref(v_f_6427_);
                    v_a_6438_ = lean_ctor_get(v___x_6434_, 0);
                    v_isSharedCheck_6445_ = (!lean_is_exclusive(v___x_6434_)) as u8;
                    if v_isSharedCheck_6445_ == 0 {
                        v___x_6440_ = v___x_6434_;
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6438_);
                        lean_dec(v___x_6434_);
                        v___x_6440_ = lean_box(0);
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6441_ == 0 {
                    v___x_6443_ = v___x_6440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_a_6438_);
                    v___x_6443_ = v_reuseFailAlloc_6444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkHCongr___boxed(
    mut v_f_6446_: *mut LeanObject,
    mut v_a_6447_: *mut LeanObject,
    mut v_a_6448_: *mut LeanObject,
    mut v_a_6449_: *mut LeanObject,
    mut v_a_6450_: *mut LeanObject,
    mut v_a_6451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6452_: *mut LeanObject = core::ptr::null_mut();
    v_res_6452_ = l_Lean_Meta_mkHCongr(v_f_6446_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
    lean_dec(v_a_6450_);
    lean_dec_ref(v_a_6449_);
    lean_dec(v_a_6448_);
    lean_dec_ref(v_a_6447_);
    return v_res_6452_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(
    mut v_a_6453_: *mut LeanObject,
    mut v_as_6454_: *mut LeanObject,
    mut v_i_6455_: usize,
    mut v_stop_6456_: usize,
) -> u8 {
    let mut v___x_6457_: u8 = 0;
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: u8 = 0;
    let mut v___x_6460_: usize = 0;
    let mut v___x_6461_: usize = 0;
    let mut v___x_6463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6457_ = lean_usize_dec_eq(v_i_6455_, v_stop_6456_);
                if v___x_6457_ == 0 {
                    v___x_6458_ = lean_array_uget_borrowed(v_as_6454_, v_i_6455_);
                    v___x_6459_ = lean_nat_dec_eq(v_a_6453_, v___x_6458_);
                    if v___x_6459_ == 0 {
                        v___x_6460_ = 1usize;
                        v___x_6461_ = lean_usize_add(v_i_6455_, v___x_6460_);
                        v_i_6455_ = v___x_6461_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6459_;
                    }
                } else {
                    v___x_6463_ = 0;
                    return v___x_6463_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(
    mut v_a_6464_: *mut LeanObject,
    mut v_as_6465_: *mut LeanObject,
    mut v_i_6466_: *mut LeanObject,
    mut v_stop_6467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6468_: usize = 0;
    let mut v_stop_boxed_6469_: usize = 0;
    let mut v_res_6470_: u8 = 0;
    let mut v_r_6471_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6468_ = lean_unbox_usize(v_i_6466_);
    lean_dec(v_i_6466_);
    v_stop_boxed_6469_ = lean_unbox_usize(v_stop_6467_);
    lean_dec(v_stop_6467_);
    v_res_6470_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_6464_, v_as_6465_, v_i_boxed_6468_, v_stop_boxed_6469_);
    lean_dec_ref(v_as_6465_);
    lean_dec(v_a_6464_);
    v_r_6471_ = lean_box((v_res_6470_) as usize);
    return v_r_6471_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(
    mut v_as_6472_: *mut LeanObject,
    mut v_a_6473_: *mut LeanObject,
) -> u8 {
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: u8 = 0;
    v___x_6474_ = lean_unsigned_to_nat(0);
    v___x_6475_ = lean_array_get_size(v_as_6472_);
    v___x_6476_ = lean_nat_dec_lt(v___x_6474_, v___x_6475_);
    if v___x_6476_ == 0 {
        return v___x_6476_;
    } else {
        if v___x_6476_ == 0 {
            return v___x_6476_;
        } else {
            let mut v___x_6477_: usize = 0;
            let mut v___x_6478_: usize = 0;
            let mut v___x_6479_: u8 = 0;
            v___x_6477_ = 0usize;
            v___x_6478_ = lean_usize_of_nat(v___x_6475_);
            v___x_6479_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_6473_, v_as_6472_, v___x_6477_, v___x_6478_);
            return v___x_6479_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(
    mut v_as_6480_: *mut LeanObject,
    mut v_a_6481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6482_: u8 = 0;
    let mut v_r_6483_: *mut LeanObject = core::ptr::null_mut();
    v_res_6482_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_6480_, v_a_6481_);
    lean_dec(v_a_6481_);
    lean_dec_ref(v_as_6480_);
    v_r_6483_ = lean_box((v_res_6482_) as usize);
    return v_r_6483_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(
    mut v_next_6484_: *mut LeanObject,
    mut v_upperBound_6485_: *mut LeanObject,
    mut v___x_6486_: *mut LeanObject,
    mut v_a_6487_: *mut LeanObject,
    mut v_b_6488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: u8 = 0;
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: u8 = 0;
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backDeps_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: u8 = 0;
    let mut v___x_6502_: u8 = 0;
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6498_ = lean_nat_dec_lt(v_a_6487_, v_upperBound_6485_);
                if v___x_6498_ == 0 {
                    lean_dec(v_a_6487_);
                    return v_b_6488_;
                } else {
                    v___x_6499_ = lean_array_fget_borrowed(v___x_6486_, v_a_6487_);
                    v_backDeps_6500_ = lean_ctor_get(v___x_6499_, 0);
                    v___x_6501_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_backDeps_6500_, v_next_6484_);
                    if v___x_6501_ == 0 {
                        v_a_6490_ = v_b_6488_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6502_ = 0;
                        v___x_6503_ = lean_box((v___x_6502_) as usize);
                        v___x_6504_ = lean_array_get(v___x_6503_, v_b_6488_, v_a_6487_);
                        lean_dec(v___x_6503_);
                        v___x_6505_ = (lean_unbox(v___x_6504_) as u8);
                        lean_dec(v___x_6504_);
                        match v___x_6505_ {
                            2 => {
                                lean_dec(v_a_6487_);
                                state = 2;
                                continue;
                            }
                            0 => {
                                lean_dec(v_a_6487_);
                                state = 2;
                                continue;
                            }
                            _ => {
                                v_a_6490_ = v_b_6488_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6491_ = lean_unsigned_to_nat(1);
                v___x_6492_ = lean_nat_add(v_a_6487_, v___x_6491_);
                lean_dec(v_a_6487_);
                v_a_6487_ = v___x_6492_;
                v_b_6488_ = v_a_6490_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6495_ = 0;
                v___x_6496_ = lean_box((v___x_6495_) as usize);
                v___x_6497_ = lean_array_set(v_b_6488_, v_next_6484_, v___x_6496_);
                return v___x_6497_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(
    mut v_next_6506_: *mut LeanObject,
    mut v_upperBound_6507_: *mut LeanObject,
    mut v___x_6508_: *mut LeanObject,
    mut v_a_6509_: *mut LeanObject,
    mut v_b_6510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6511_: *mut LeanObject = core::ptr::null_mut();
    v_res_6511_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_6506_, v_upperBound_6507_, v___x_6508_, v_a_6509_, v_b_6510_);
    lean_dec_ref(v___x_6508_);
    lean_dec(v_upperBound_6507_);
    lean_dec(v_next_6506_);
    return v_res_6511_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(
    mut v_upperBound_6512_: *mut LeanObject,
    mut v___x_6513_: *mut LeanObject,
    mut v___x_6514_: *mut LeanObject,
    mut v_a_6515_: *mut LeanObject,
    mut v_b_6516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6517_: u8 = 0;
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6517_ = lean_nat_dec_lt(v_a_6515_, v_upperBound_6512_);
                if v___x_6517_ == 0 {
                    lean_dec(v_a_6515_);
                    return v_b_6516_;
                } else {
                    v___x_6518_ = lean_unsigned_to_nat(1);
                    v___x_6519_ = lean_nat_add(v_a_6515_, v___x_6518_);
                    lean_inc(v___x_6519_);
                    v___x_6520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_a_6515_, v___x_6513_, v___x_6514_, v___x_6519_, v_b_6516_);
                    lean_dec(v_a_6515_);
                    v_a_6515_ = v___x_6519_;
                    v_b_6516_ = v___x_6520_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(
    mut v_upperBound_6522_: *mut LeanObject,
    mut v___x_6523_: *mut LeanObject,
    mut v___x_6524_: *mut LeanObject,
    mut v_a_6525_: *mut LeanObject,
    mut v_b_6526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6527_: *mut LeanObject = core::ptr::null_mut();
    v_res_6527_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_6522_, v___x_6523_, v___x_6524_, v_a_6525_, v_b_6526_);
    lean_dec_ref(v___x_6524_);
    lean_dec(v___x_6523_);
    lean_dec(v_upperBound_6522_);
    return v_res_6527_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(
    mut v_info_6528_: *mut LeanObject,
    mut v_kinds_6529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_paramInfo_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    v_paramInfo_6530_ = lean_ctor_get(v_info_6528_, 0);
    v___x_6531_ = lean_array_get_size(v_paramInfo_6530_);
    v___x_6532_ = lean_unsigned_to_nat(0);
    v___x_6533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v___x_6531_, v___x_6531_, v_paramInfo_6530_, v___x_6532_, v_kinds_6529_);
    return v___x_6533_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(
    mut v_info_6534_: *mut LeanObject,
    mut v_kinds_6535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6536_: *mut LeanObject = core::ptr::null_mut();
    v_res_6536_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(
        v_info_6534_,
        v_kinds_6535_,
    );
    lean_dec_ref(v_info_6534_);
    return v_res_6536_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(
    mut v_next_6537_: *mut LeanObject,
    mut v_upperBound_6538_: *mut LeanObject,
    mut v___x_6539_: *mut LeanObject,
    mut v_inst_6540_: *mut LeanObject,
    mut v_R_6541_: *mut LeanObject,
    mut v_a_6542_: *mut LeanObject,
    mut v_b_6543_: *mut LeanObject,
    mut v_c_6544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    v___x_6545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_6537_, v_upperBound_6538_, v___x_6539_, v_a_6542_, v_b_6543_);
    return v___x_6545_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(
    mut v_next_6546_: *mut LeanObject,
    mut v_upperBound_6547_: *mut LeanObject,
    mut v___x_6548_: *mut LeanObject,
    mut v_inst_6549_: *mut LeanObject,
    mut v_R_6550_: *mut LeanObject,
    mut v_a_6551_: *mut LeanObject,
    mut v_b_6552_: *mut LeanObject,
    mut v_c_6553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6554_: *mut LeanObject = core::ptr::null_mut();
    v_res_6554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(v_next_6546_, v_upperBound_6547_, v___x_6548_, v_inst_6549_, v_R_6550_, v_a_6551_, v_b_6552_, v_c_6553_);
    lean_dec_ref(v___x_6548_);
    lean_dec(v_upperBound_6547_);
    lean_dec(v_next_6546_);
    return v_res_6554_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(
    mut v_upperBound_6555_: *mut LeanObject,
    mut v___x_6556_: *mut LeanObject,
    mut v___x_6557_: *mut LeanObject,
    mut v_inst_6558_: *mut LeanObject,
    mut v_R_6559_: *mut LeanObject,
    mut v_a_6560_: *mut LeanObject,
    mut v_b_6561_: *mut LeanObject,
    mut v_c_6562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    v___x_6563_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_6555_, v___x_6556_, v___x_6557_, v_a_6560_, v_b_6561_);
    return v___x_6563_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(
    mut v_upperBound_6564_: *mut LeanObject,
    mut v___x_6565_: *mut LeanObject,
    mut v___x_6566_: *mut LeanObject,
    mut v_inst_6567_: *mut LeanObject,
    mut v_R_6568_: *mut LeanObject,
    mut v_a_6569_: *mut LeanObject,
    mut v_b_6570_: *mut LeanObject,
    mut v_c_6571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6572_: *mut LeanObject = core::ptr::null_mut();
    v_res_6572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(v_upperBound_6564_, v___x_6565_, v___x_6566_, v_inst_6567_, v_R_6568_, v_a_6569_, v_b_6570_, v_c_6571_);
    lean_dec_ref(v___x_6566_);
    lean_dec(v___x_6565_);
    lean_dec(v_upperBound_6564_);
    return v_res_6572_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(
    mut v_as_6573_: *mut LeanObject,
    mut v_i_6574_: usize,
    mut v_stop_6575_: usize,
) -> u8 {
    let mut v___x_6576_: u8 = 0;
    let mut v___x_6577_: u8 = 0;
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: u8 = 0;
    let mut v___x_6580_: usize = 0;
    let mut v___x_6581_: usize = 0;
    let mut v___x_6583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6576_ = lean_usize_dec_eq(v_i_6574_, v_stop_6575_);
                if v___x_6576_ == 0 {
                    v___x_6577_ = 1;
                    v___x_6578_ = lean_array_uget_borrowed(v_as_6573_, v_i_6574_);
                    v___x_6579_ = (lean_unbox(v___x_6578_) as u8);
                    match v___x_6579_ {
                        3 => {
                            return v___x_6577_;
                        }
                        5 => {
                            return v___x_6577_;
                        }
                        _ => {
                            if v___x_6576_ == 0 {
                                v___x_6580_ = 1usize;
                                v___x_6581_ = lean_usize_add(v_i_6574_, v___x_6580_);
                                v_i_6574_ = v___x_6581_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_6577_;
                            }
                        }
                    }
                } else {
                    v___x_6583_ = 0;
                    return v___x_6583_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(
    mut v_as_6584_: *mut LeanObject,
    mut v_i_6585_: *mut LeanObject,
    mut v_stop_6586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6587_: usize = 0;
    let mut v_stop_boxed_6588_: usize = 0;
    let mut v_res_6589_: u8 = 0;
    let mut v_r_6590_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6587_ = lean_unbox_usize(v_i_6585_);
    lean_dec(v_i_6585_);
    v_stop_boxed_6588_ = lean_unbox_usize(v_stop_6586_);
    lean_dec(v_stop_6586_);
    v_res_6589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_6584_, v_i_boxed_6587_, v_stop_boxed_6588_);
    lean_dec_ref(v_as_6584_);
    v_r_6590_ = lean_box((v_res_6589_) as usize);
    return v_r_6590_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(
    mut v_kinds_6591_: *mut LeanObject,
) -> u8 {
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: u8 = 0;
    v___x_6592_ = lean_unsigned_to_nat(0);
    v___x_6593_ = lean_array_get_size(v_kinds_6591_);
    v___x_6594_ = lean_nat_dec_lt(v___x_6592_, v___x_6593_);
    if v___x_6594_ == 0 {
        return v___x_6594_;
    } else {
        if v___x_6594_ == 0 {
            return v___x_6594_;
        } else {
            let mut v___x_6595_: usize = 0;
            let mut v___x_6596_: usize = 0;
            let mut v___x_6597_: u8 = 0;
            v___x_6595_ = 0usize;
            v___x_6596_ = lean_usize_of_nat(v___x_6593_);
            v___x_6597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_kinds_6591_, v___x_6595_, v___x_6596_);
            return v___x_6597_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(
    mut v_kinds_6598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6599_: u8 = 0;
    let mut v_r_6600_: *mut LeanObject = core::ptr::null_mut();
    v_res_6599_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_6598_);
    lean_dec_ref(v_kinds_6598_);
    v_r_6600_ = lean_box((v_res_6599_) as usize);
    return v_r_6600_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(
    mut v___x_6601_: *mut LeanObject,
    mut v_k_6602_: *mut LeanObject,
    mut v_xs_6603_: *mut LeanObject,
    mut v_type_6604_: *mut LeanObject,
    mut v___y_6605_: *mut LeanObject,
    mut v___y_6606_: *mut LeanObject,
    mut v___y_6607_: *mut LeanObject,
    mut v___y_6608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    v___x_6610_ = lean_unsigned_to_nat(0);
    v___x_6611_ = lean_array_get_borrowed(v___x_6601_, v_xs_6603_, v___x_6610_);
    lean_inc(v___y_6608_);
    lean_inc_ref(v___y_6607_);
    lean_inc(v___y_6606_);
    lean_inc_ref(v___y_6605_);
    lean_inc(v___x_6611_);
    v___x_6612_ = lean_apply_7(
        v_k_6602_,
        v___x_6611_,
        v_type_6604_,
        v___y_6605_,
        v___y_6606_,
        v___y_6607_,
        v___y_6608_,
        lean_box(0),
    );
    return v___x_6612_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(
    mut v___x_6613_: *mut LeanObject,
    mut v_k_6614_: *mut LeanObject,
    mut v_xs_6615_: *mut LeanObject,
    mut v_type_6616_: *mut LeanObject,
    mut v___y_6617_: *mut LeanObject,
    mut v___y_6618_: *mut LeanObject,
    mut v___y_6619_: *mut LeanObject,
    mut v___y_6620_: *mut LeanObject,
    mut v___y_6621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6622_: *mut LeanObject = core::ptr::null_mut();
    v_res_6622_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(
        v___x_6613_,
        v_k_6614_,
        v_xs_6615_,
        v_type_6616_,
        v___y_6617_,
        v___y_6618_,
        v___y_6619_,
        v___y_6620_,
    );
    lean_dec(v___y_6620_);
    lean_dec_ref(v___y_6619_);
    lean_dec(v___y_6618_);
    lean_dec_ref(v___y_6617_);
    lean_dec_ref(v_xs_6615_);
    lean_dec_ref(v___x_6613_);
    return v_res_6622_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(
    mut v_type_6623_: *mut LeanObject,
    mut v_k_6624_: *mut LeanObject,
    mut v_a_6625_: *mut LeanObject,
    mut v_a_6626_: *mut LeanObject,
    mut v_a_6627_: *mut LeanObject,
    mut v_a_6628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: u8 = 0;
    let mut v___x_6634_: u8 = 0;
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    v___x_6630_ = l_Lean_instInhabitedExpr;
    v___f_6631_ = lean_alloc_closure(
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        9,
        2,
    );
    lean_closure_set(v___f_6631_, 0, v___x_6630_);
    lean_closure_set(v___f_6631_, 1, v_k_6624_);
    v___x_6632_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4;
    v___x_6633_ = 1;
    v___x_6634_ = 0;
    v___x_6635_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_6623_, v___x_6632_, v___f_6631_, v___x_6633_, v___x_6634_, v_a_6625_, v_a_6626_, v_a_6627_, v_a_6628_);
    return v___x_6635_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(
    mut v_type_6636_: *mut LeanObject,
    mut v_k_6637_: *mut LeanObject,
    mut v_a_6638_: *mut LeanObject,
    mut v_a_6639_: *mut LeanObject,
    mut v_a_6640_: *mut LeanObject,
    mut v_a_6641_: *mut LeanObject,
    mut v_a_6642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6643_: *mut LeanObject = core::ptr::null_mut();
    v_res_6643_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(
        v_type_6636_,
        v_k_6637_,
        v_a_6638_,
        v_a_6639_,
        v_a_6640_,
        v_a_6641_,
    );
    lean_dec(v_a_6641_);
    lean_dec_ref(v_a_6640_);
    lean_dec(v_a_6639_);
    lean_dec_ref(v_a_6638_);
    return v_res_6643_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(
    mut v_00_u03b1_6644_: *mut LeanObject,
    mut v_type_6645_: *mut LeanObject,
    mut v_k_6646_: *mut LeanObject,
    mut v_a_6647_: *mut LeanObject,
    mut v_a_6648_: *mut LeanObject,
    mut v_a_6649_: *mut LeanObject,
    mut v_a_6650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    v___x_6652_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(
        v_type_6645_,
        v_k_6646_,
        v_a_6647_,
        v_a_6648_,
        v_a_6649_,
        v_a_6650_,
    );
    return v___x_6652_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(
    mut v_00_u03b1_6653_: *mut LeanObject,
    mut v_type_6654_: *mut LeanObject,
    mut v_k_6655_: *mut LeanObject,
    mut v_a_6656_: *mut LeanObject,
    mut v_a_6657_: *mut LeanObject,
    mut v_a_6658_: *mut LeanObject,
    mut v_a_6659_: *mut LeanObject,
    mut v_a_6660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6661_: *mut LeanObject = core::ptr::null_mut();
    v_res_6661_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(
        v_00_u03b1_6653_,
        v_type_6654_,
        v_k_6655_,
        v_a_6656_,
        v_a_6657_,
        v_a_6658_,
        v_a_6659_,
    );
    lean_dec(v_a_6659_);
    lean_dec_ref(v_a_6658_);
    lean_dec(v_a_6657_);
    lean_dec_ref(v_a_6656_);
    return v_res_6661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(
    mut v_kinds_6665_: *mut LeanObject,
    mut v___x_6666_: u8,
    mut v_as_6667_: *mut LeanObject,
    mut v_sz_6668_: usize,
    mut v_i_6669_: usize,
    mut v_b_6670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6671_: u8 = 0;
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: u8 = 0;
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: u8 = 0;
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: usize = 0;
    let mut v___x_6683_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6671_ = lean_usize_dec_lt(v_i_6669_, v_sz_6668_);
                if v___x_6671_ == 0 {
                    lean_inc_ref(v_b_6670_);
                    return v_b_6670_;
                } else {
                    v___x_6672_ = lean_box(0);
                    v_a_6673_ = lean_array_uget_borrowed(v_as_6667_, v_i_6669_);
                    v___x_6674_ = 0;
                    v___x_6675_ = lean_box((v___x_6674_) as usize);
                    v___x_6676_ = lean_array_get(v___x_6675_, v_kinds_6665_, v_a_6673_);
                    lean_dec(v___x_6675_);
                    v___x_6677_ = (lean_unbox(v___x_6676_) as u8);
                    lean_dec(v___x_6676_);
                    if v___x_6677_ == 2 {
                        v___x_6678_ = lean_box((v___x_6666_) as usize);
                        v___x_6679_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6679_, 0, v___x_6678_);
                        v___x_6680_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_6680_, 0, v___x_6679_);
                        lean_ctor_set(v___x_6680_, 1, v___x_6672_);
                        return v___x_6680_;
                    } else {
                        v___x_6681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0;
                        v___x_6682_ = 1usize;
                        v___x_6683_ = lean_usize_add(v_i_6669_, v___x_6682_);
                        v_i_6669_ = v___x_6683_;
                        v_b_6670_ = v___x_6681_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(
    mut v_kinds_6685_: *mut LeanObject,
    mut v___x_6686_: *mut LeanObject,
    mut v_as_6687_: *mut LeanObject,
    mut v_sz_6688_: *mut LeanObject,
    mut v_i_6689_: *mut LeanObject,
    mut v_b_6690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_663__boxed_6691_: u8 = 0;
    let mut v_sz_boxed_6692_: usize = 0;
    let mut v_i_boxed_6693_: usize = 0;
    let mut v_res_6694_: *mut LeanObject = core::ptr::null_mut();
    v___x_663__boxed_6691_ = (lean_unbox(v___x_6686_) as u8);
    v_sz_boxed_6692_ = lean_unbox_usize(v_sz_6688_);
    lean_dec(v_sz_6688_);
    v_i_boxed_6693_ = lean_unbox_usize(v_i_6689_);
    lean_dec(v_i_6689_);
    v_res_6694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_6685_, v___x_663__boxed_6691_, v_as_6687_, v_sz_boxed_6692_, v_i_boxed_6693_, v_b_6690_);
    lean_dec_ref(v_b_6690_);
    lean_dec_ref(v_as_6687_);
    lean_dec_ref(v_kinds_6685_);
    return v_res_6694_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(
    mut v_info_6695_: *mut LeanObject,
    mut v_kinds_6696_: *mut LeanObject,
    mut v_i_6697_: *mut LeanObject,
) -> u8 {
    let mut v_paramInfo_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDecInst_6701_: u8 = 0;
    v_paramInfo_6698_ = lean_ctor_get(v_info_6695_, 0);
    v___x_6699_ = l_Lean_Meta_instInhabitedParamInfo_default;
    v___x_6700_ = lean_array_get_borrowed(v___x_6699_, v_paramInfo_6698_, v_i_6697_);
    v_isDecInst_6701_ = lean_ctor_get_uint8(
        v___x_6700_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
    );
    if v_isDecInst_6701_ == 0 {
        return v_isDecInst_6701_;
    } else {
        let mut v_backDeps_6702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_6704_: usize = 0;
        let mut v___x_6705_: usize = 0;
        let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_6707_: *mut LeanObject = core::ptr::null_mut();
        v_backDeps_6702_ = lean_ctor_get(v___x_6700_, 0);
        v___x_6703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0;
        v_sz_6704_ = lean_array_size(v_backDeps_6702_);
        v___x_6705_ = 0usize;
        v___x_6706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_6696_, v_isDecInst_6701_, v_backDeps_6702_, v_sz_6704_, v___x_6705_, v___x_6703_);
        v_fst_6707_ = lean_ctor_get(v___x_6706_, 0);
        lean_inc(v_fst_6707_);
        lean_dec_ref(v___x_6706_);
        if lean_obj_tag(v_fst_6707_) == 0 {
            let mut v___x_6708_: u8 = 0;
            v___x_6708_ = 0;
            return v___x_6708_;
        } else {
            let mut v_val_6709_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6710_: u8 = 0;
            v_val_6709_ = lean_ctor_get(v_fst_6707_, 0);
            lean_inc(v_val_6709_);
            lean_dec_ref_known(v_fst_6707_, 1);
            v___x_6710_ = (lean_unbox(v_val_6709_) as u8);
            lean_dec(v_val_6709_);
            return v___x_6710_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(
    mut v_info_6711_: *mut LeanObject,
    mut v_kinds_6712_: *mut LeanObject,
    mut v_i_6713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6714_: u8 = 0;
    let mut v_r_6715_: *mut LeanObject = core::ptr::null_mut();
    v_res_6714_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(
        v_info_6711_,
        v_kinds_6712_,
        v_i_6713_,
    );
    lean_dec(v_i_6713_);
    lean_dec_ref(v_kinds_6712_);
    lean_dec_ref(v_info_6711_);
    v_r_6715_ = lean_box((v_res_6714_) as usize);
    return v_r_6715_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(
    mut v_type_6716_: *mut LeanObject,
    mut v_k_6717_: *mut LeanObject,
    mut v_cleanupAnnotations_6718_: u8,
    mut v_whnfType_6719_: u8,
    mut v___y_6720_: *mut LeanObject,
    mut v___y_6721_: *mut LeanObject,
    mut v___y_6722_: *mut LeanObject,
    mut v___y_6723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6730_: u8 = 0;
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6734_: u8 = 0;
    let mut v_a_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6738_: u8 = 0;
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6725_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_6725_, 0, v_k_6717_);
                v___x_6726_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_6716_,
                    v___f_6725_,
                    v_cleanupAnnotations_6718_,
                    v_whnfType_6719_,
                    v___y_6720_,
                    v___y_6721_,
                    v___y_6722_,
                    v___y_6723_,
                );
                if lean_obj_tag(v___x_6726_) == 0 {
                    v_a_6727_ = lean_ctor_get(v___x_6726_, 0);
                    v_isSharedCheck_6734_ = (!lean_is_exclusive(v___x_6726_)) as u8;
                    if v_isSharedCheck_6734_ == 0 {
                        v___x_6729_ = v___x_6726_;
                        v_isShared_6730_ = v_isSharedCheck_6734_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6727_);
                        lean_dec(v___x_6726_);
                        v___x_6729_ = lean_box(0);
                        v_isShared_6730_ = v_isSharedCheck_6734_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6735_ = lean_ctor_get(v___x_6726_, 0);
                    v_isSharedCheck_6742_ = (!lean_is_exclusive(v___x_6726_)) as u8;
                    if v_isSharedCheck_6742_ == 0 {
                        v___x_6737_ = v___x_6726_;
                        v_isShared_6738_ = v_isSharedCheck_6742_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6735_);
                        lean_dec(v___x_6726_);
                        v___x_6737_ = lean_box(0);
                        v_isShared_6738_ = v_isSharedCheck_6742_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6730_ == 0 {
                    v___x_6732_ = v___x_6729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6733_, 0, v_a_6727_);
                    v___x_6732_ = v_reuseFailAlloc_6733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6732_;
            }
            3 => {
                if v_isShared_6738_ == 0 {
                    v___x_6740_ = v___x_6737_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6741_, 0, v_a_6735_);
                    v___x_6740_ = v_reuseFailAlloc_6741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(
    mut v_type_6743_: *mut LeanObject,
    mut v_k_6744_: *mut LeanObject,
    mut v_cleanupAnnotations_6745_: *mut LeanObject,
    mut v_whnfType_6746_: *mut LeanObject,
    mut v___y_6747_: *mut LeanObject,
    mut v___y_6748_: *mut LeanObject,
    mut v___y_6749_: *mut LeanObject,
    mut v___y_6750_: *mut LeanObject,
    mut v___y_6751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_6752_: u8 = 0;
    let mut v_whnfType_boxed_6753_: u8 = 0;
    let mut v_res_6754_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6752_ = (lean_unbox(v_cleanupAnnotations_6745_) as u8);
    v_whnfType_boxed_6753_ = (lean_unbox(v_whnfType_6746_) as u8);
    v_res_6754_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_6743_, v_k_6744_, v_cleanupAnnotations_boxed_6752_, v_whnfType_boxed_6753_, v___y_6747_, v___y_6748_, v___y_6749_, v___y_6750_);
    lean_dec(v___y_6750_);
    lean_dec_ref(v___y_6749_);
    lean_dec(v___y_6748_);
    lean_dec_ref(v___y_6747_);
    return v_res_6754_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(
    mut v_00_u03b1_6755_: *mut LeanObject,
    mut v_type_6756_: *mut LeanObject,
    mut v_k_6757_: *mut LeanObject,
    mut v_cleanupAnnotations_6758_: u8,
    mut v_whnfType_6759_: u8,
    mut v___y_6760_: *mut LeanObject,
    mut v___y_6761_: *mut LeanObject,
    mut v___y_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    v___x_6765_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_6756_, v_k_6757_, v_cleanupAnnotations_6758_, v_whnfType_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_);
    return v___x_6765_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(
    mut v_00_u03b1_6766_: *mut LeanObject,
    mut v_type_6767_: *mut LeanObject,
    mut v_k_6768_: *mut LeanObject,
    mut v_cleanupAnnotations_6769_: *mut LeanObject,
    mut v_whnfType_6770_: *mut LeanObject,
    mut v___y_6771_: *mut LeanObject,
    mut v___y_6772_: *mut LeanObject,
    mut v___y_6773_: *mut LeanObject,
    mut v___y_6774_: *mut LeanObject,
    mut v___y_6775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_6776_: u8 = 0;
    let mut v_whnfType_boxed_6777_: u8 = 0;
    let mut v_res_6778_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6776_ = (lean_unbox(v_cleanupAnnotations_6769_) as u8);
    v_whnfType_boxed_6777_ = (lean_unbox(v_whnfType_6770_) as u8);
    v_res_6778_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(v_00_u03b1_6766_, v_type_6767_, v_k_6768_, v_cleanupAnnotations_boxed_6776_, v_whnfType_boxed_6777_, v___y_6771_, v___y_6772_, v___y_6773_, v___y_6774_);
    lean_dec(v___y_6774_);
    lean_dec_ref(v___y_6773_);
    lean_dec(v___y_6772_);
    lean_dec_ref(v___y_6771_);
    return v_res_6778_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(
    mut v_upperBound_6779_: *mut LeanObject,
    mut v_val_6780_: *mut LeanObject,
    mut v_xs_6781_: *mut LeanObject,
    mut v___x_6782_: *mut LeanObject,
    mut v___x_6783_: *mut LeanObject,
    mut v___x_6784_: u8,
    mut v_a_6785_: *mut LeanObject,
    mut v_b_6786_: *mut LeanObject,
    mut v___y_6787_: *mut LeanObject,
    mut v___y_6788_: *mut LeanObject,
    mut v___y_6789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: u8 = 0;
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: u8 = 0;
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6805_: u8 = 0;
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6813_: u8 = 0;
    let mut v___x_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6817_: u8 = 0;
    let mut v___x_6818_: u8 = 0;
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6796_ = lean_nat_dec_lt(v_a_6785_, v_upperBound_6779_);
                if v___x_6796_ == 0 {
                    lean_dec(v_a_6785_);
                    lean_dec(v___x_6783_);
                    lean_dec_ref(v___x_6782_);
                    v___x_6797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6797_, 0, v_b_6786_);
                    return v___x_6797_;
                } else {
                    v_numParams_6798_ = lean_ctor_get(v_val_6780_, 3);
                    v___x_6799_ = lean_nat_dec_lt(v_a_6785_, v_numParams_6798_);
                    if v___x_6799_ == 0 {
                        v___x_6800_ = lean_array_fget_borrowed(v_xs_6781_, v_a_6785_);
                        v___x_6801_ = l_Lean_Expr_fvarId_x21(v___x_6800_);
                        v___x_6802_ = l_Lean_FVarId_getDecl___redArg(
                            v___x_6801_,
                            v___y_6787_,
                            v___y_6788_,
                            v___y_6789_,
                        );
                        if lean_obj_tag(v___x_6802_) == 0 {
                            v_a_6803_ = lean_ctor_get(v___x_6802_, 0);
                            lean_inc(v_a_6803_);
                            lean_dec_ref_known(v___x_6802_, 1);
                            v___x_6808_ = l_Lean_LocalDecl_userName(v_a_6803_);
                            lean_dec(v_a_6803_);
                            lean_inc(v___x_6783_);
                            lean_inc_ref(v___x_6782_);
                            v___x_6809_ =
                                l_Lean_isSubobjectField_x3f(v___x_6782_, v___x_6783_, v___x_6808_);
                            if lean_obj_tag(v___x_6809_) == 0 {
                                v___y_6805_ = v___x_6799_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_6809_, 1);
                                v___y_6805_ = v___x_6784_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_6786_);
                            lean_dec(v_a_6785_);
                            lean_dec(v___x_6783_);
                            lean_dec_ref(v___x_6782_);
                            v_a_6810_ = lean_ctor_get(v___x_6802_, 0);
                            v_isSharedCheck_6817_ = (!lean_is_exclusive(v___x_6802_)) as u8;
                            if v_isSharedCheck_6817_ == 0 {
                                v___x_6812_ = v___x_6802_;
                                v_isShared_6813_ = v_isSharedCheck_6817_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6810_);
                                lean_dec(v___x_6802_);
                                v___x_6812_ = lean_box(0);
                                v_isShared_6813_ = v_isSharedCheck_6817_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_6818_ = 0;
                        v___x_6819_ = lean_box((v___x_6818_) as usize);
                        v___x_6820_ = lean_array_push(v_b_6786_, v___x_6819_);
                        v_a_6792_ = v___x_6820_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6793_ = lean_unsigned_to_nat(1);
                v___x_6794_ = lean_nat_add(v_a_6785_, v___x_6793_);
                lean_dec(v_a_6785_);
                v_a_6785_ = v___x_6794_;
                v_b_6786_ = v_a_6792_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6806_ = lean_box((v___y_6805_) as usize);
                v___x_6807_ = lean_array_push(v_b_6786_, v___x_6806_);
                v_a_6792_ = v___x_6807_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_6813_ == 0 {
                    v___x_6815_ = v___x_6812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6816_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6816_, 0, v_a_6810_);
                    v___x_6815_ = v_reuseFailAlloc_6816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(
    mut v_upperBound_6821_: *mut LeanObject,
    mut v_val_6822_: *mut LeanObject,
    mut v_xs_6823_: *mut LeanObject,
    mut v___x_6824_: *mut LeanObject,
    mut v___x_6825_: *mut LeanObject,
    mut v___x_6826_: *mut LeanObject,
    mut v_a_6827_: *mut LeanObject,
    mut v_b_6828_: *mut LeanObject,
    mut v___y_6829_: *mut LeanObject,
    mut v___y_6830_: *mut LeanObject,
    mut v___y_6831_: *mut LeanObject,
    mut v___y_6832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5663__boxed_6833_: u8 = 0;
    let mut v_res_6834_: *mut LeanObject = core::ptr::null_mut();
    v___x_5663__boxed_6833_ = (lean_unbox(v___x_6826_) as u8);
    v_res_6834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_6821_, v_val_6822_, v_xs_6823_, v___x_6824_, v___x_6825_, v___x_5663__boxed_6833_, v_a_6827_, v_b_6828_, v___y_6829_, v___y_6830_, v___y_6831_);
    lean_dec(v___y_6831_);
    lean_dec_ref(v___y_6830_);
    lean_dec_ref(v___y_6829_);
    lean_dec_ref(v_xs_6823_);
    lean_dec_ref(v_val_6822_);
    lean_dec(v_upperBound_6821_);
    return v_res_6834_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(
    mut v_val_6837_: *mut LeanObject,
    mut v_induct_6838_: *mut LeanObject,
    mut v___x_6839_: u8,
    mut v_xs_6840_: *mut LeanObject,
    mut v_x_6841_: *mut LeanObject,
    mut v___y_6842_: *mut LeanObject,
    mut v___y_6843_: *mut LeanObject,
    mut v___y_6844_: *mut LeanObject,
    mut v___y_6845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6856_: u8 = 0;
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6861_: u8 = 0;
    let mut v_a_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6865_: u8 = 0;
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6847_ = lean_st_ref_get(v___y_6845_);
                v_env_6848_ = lean_ctor_get(v___x_6847_, 0);
                lean_inc_ref(v_env_6848_);
                lean_dec(v___x_6847_);
                v___x_6849_ = lean_array_get_size(v_xs_6840_);
                v___x_6850_ = lean_unsigned_to_nat(0);
                v___x_6851_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0;
                v___x_6852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v___x_6849_, v_val_6837_, v_xs_6840_, v_env_6848_, v_induct_6838_, v___x_6839_, v___x_6850_, v___x_6851_, v___y_6842_, v___y_6844_, v___y_6845_);
                if lean_obj_tag(v___x_6852_) == 0 {
                    v_a_6853_ = lean_ctor_get(v___x_6852_, 0);
                    v_isSharedCheck_6861_ = (!lean_is_exclusive(v___x_6852_)) as u8;
                    if v_isSharedCheck_6861_ == 0 {
                        v___x_6855_ = v___x_6852_;
                        v_isShared_6856_ = v_isSharedCheck_6861_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6853_);
                        lean_dec(v___x_6852_);
                        v___x_6855_ = lean_box(0);
                        v_isShared_6856_ = v_isSharedCheck_6861_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6862_ = lean_ctor_get(v___x_6852_, 0);
                    v_isSharedCheck_6869_ = (!lean_is_exclusive(v___x_6852_)) as u8;
                    if v_isSharedCheck_6869_ == 0 {
                        v___x_6864_ = v___x_6852_;
                        v_isShared_6865_ = v_isSharedCheck_6869_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6862_);
                        lean_dec(v___x_6852_);
                        v___x_6864_ = lean_box(0);
                        v_isShared_6865_ = v_isSharedCheck_6869_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6857_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6857_, 0, v_a_6853_);
                if v_isShared_6856_ == 0 {
                    lean_ctor_set(v___x_6855_, 0, v___x_6857_);
                    v___x_6859_ = v___x_6855_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6860_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6860_, 0, v___x_6857_);
                    v___x_6859_ = v_reuseFailAlloc_6860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6859_;
            }
            3 => {
                if v_isShared_6865_ == 0 {
                    v___x_6867_ = v___x_6864_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6868_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6868_, 0, v_a_6862_);
                    v___x_6867_ = v_reuseFailAlloc_6868_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(
    mut v_val_6870_: *mut LeanObject,
    mut v_induct_6871_: *mut LeanObject,
    mut v___x_6872_: *mut LeanObject,
    mut v_xs_6873_: *mut LeanObject,
    mut v_x_6874_: *mut LeanObject,
    mut v___y_6875_: *mut LeanObject,
    mut v___y_6876_: *mut LeanObject,
    mut v___y_6877_: *mut LeanObject,
    mut v___y_6878_: *mut LeanObject,
    mut v___y_6879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5750__boxed_6880_: u8 = 0;
    let mut v_res_6881_: *mut LeanObject = core::ptr::null_mut();
    v___x_5750__boxed_6880_ = (lean_unbox(v___x_6872_) as u8);
    v_res_6881_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(
            v_val_6870_,
            v_induct_6871_,
            v___x_5750__boxed_6880_,
            v_xs_6873_,
            v_x_6874_,
            v___y_6875_,
            v___y_6876_,
            v___y_6877_,
            v___y_6878_,
        );
    lean_dec(v___y_6878_);
    lean_dec_ref(v___y_6877_);
    lean_dec(v___y_6876_);
    lean_dec_ref(v___y_6875_);
    lean_dec_ref(v_x_6874_);
    lean_dec_ref(v_xs_6873_);
    lean_dec_ref(v_val_6870_);
    return v_res_6881_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    v___x_6882_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6882_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    v___x_6883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
    v___x_6884_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6884_, 0, v___x_6883_);
    return v___x_6884_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
    v___x_6885_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_6886_ = lean_unsigned_to_nat(0);
    v___x_6887_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_6887_, 0, v___x_6886_);
    lean_ctor_set(v___x_6887_, 1, v___x_6886_);
    lean_ctor_set(v___x_6887_, 2, v___x_6886_);
    lean_ctor_set(v___x_6887_, 3, v___x_6886_);
    lean_ctor_set(v___x_6887_, 4, v___x_6885_);
    lean_ctor_set(v___x_6887_, 5, v___x_6885_);
    lean_ctor_set(v___x_6887_, 6, v___x_6885_);
    lean_ctor_set(v___x_6887_, 7, v___x_6885_);
    lean_ctor_set(v___x_6887_, 8, v___x_6885_);
    lean_ctor_set(v___x_6887_, 9, v___x_6885_);
    return v___x_6887_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
    v___x_6888_ = lean_unsigned_to_nat(32);
    v___x_6889_ = lean_mk_empty_array_with_capacity(v___x_6888_);
    v___x_6890_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6890_, 0, v___x_6889_);
    return v___x_6890_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_6891_: usize = 0;
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    v___x_6891_ = 5usize;
    v___x_6892_ = lean_unsigned_to_nat(0);
    v___x_6893_ = lean_unsigned_to_nat(32);
    v___x_6894_ = lean_mk_empty_array_with_capacity(v___x_6893_);
    v___x_6895_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
    v___x_6896_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6896_, 0, v___x_6895_);
    lean_ctor_set(v___x_6896_, 1, v___x_6894_);
    lean_ctor_set(v___x_6896_, 2, v___x_6892_);
    lean_ctor_set(v___x_6896_, 3, v___x_6892_);
    lean_ctor_set_usize(v___x_6896_, 4, v___x_6891_);
    return v___x_6896_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut LeanObject = core::ptr::null_mut();
    v___x_6897_ = lean_box(1);
    v___x_6898_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_6899_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_6900_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6900_, 0, v___x_6899_);
    lean_ctor_set(v___x_6900_, 1, v___x_6898_);
    lean_ctor_set(v___x_6900_, 2, v___x_6897_);
    return v___x_6900_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    v___x_6902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_6903_ = l_Lean_stringToMessageData(v___x_6902_);
    return v___x_6903_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    v___x_6905_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_6906_ = l_Lean_stringToMessageData(v___x_6905_);
    return v___x_6906_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    v___x_6908_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_6909_ = l_Lean_stringToMessageData(v___x_6908_);
    return v___x_6909_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    v___x_6911_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_6912_ = l_Lean_stringToMessageData(v___x_6911_);
    return v___x_6912_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    v___x_6914_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14;
    v___x_6915_ = l_Lean_stringToMessageData(v___x_6914_);
    return v___x_6915_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut LeanObject = core::ptr::null_mut();
    v___x_6917_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16;
    v___x_6918_ = l_Lean_stringToMessageData(v___x_6917_);
    return v___x_6918_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    v___x_6920_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18;
    v___x_6921_ = l_Lean_stringToMessageData(v___x_6920_);
    return v___x_6921_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_msg_6922_: *mut LeanObject,
    mut v_declHint_6923_: *mut LeanObject,
    mut v___y_6924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: u8 = 0;
    let mut v_isExporting_6929_: u8 = 0;
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: u8 = 0;
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6951_: u8 = 0;
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: u8 = 0;
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6983_: u8 = 0;
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6926_ = lean_st_ref_get(v___y_6924_);
                v_env_6927_ = lean_ctor_get(v___x_6926_, 0);
                lean_inc_ref(v_env_6927_);
                lean_dec(v___x_6926_);
                v___x_6928_ = l_Lean_Name_isAnonymous(v_declHint_6923_);
                if v___x_6928_ == 0 {
                    v_isExporting_6929_ = lean_ctor_get_uint8(
                        v_env_6927_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_6929_ == 0 {
                        lean_dec_ref(v_env_6927_);
                        lean_dec(v_declHint_6923_);
                        v___x_6930_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6930_, 0, v_msg_6922_);
                        return v___x_6930_;
                    } else {
                        lean_inc_ref(v_env_6927_);
                        v___x_6931_ = l_Lean_Environment_setExporting(v_env_6927_, v___x_6928_);
                        lean_inc(v_declHint_6923_);
                        lean_inc_ref(v___x_6931_);
                        v___x_6932_ = l_Lean_Environment_contains(
                            v___x_6931_,
                            v_declHint_6923_,
                            v_isExporting_6929_,
                        );
                        if v___x_6932_ == 0 {
                            lean_dec_ref(v___x_6931_);
                            lean_dec_ref(v_env_6927_);
                            lean_dec(v_declHint_6923_);
                            v___x_6933_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_6933_, 0, v_msg_6922_);
                            return v___x_6933_;
                        } else {
                            v___x_6934_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
                            v___x_6935_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
                            v___x_6936_ = l_Lean_Options_empty;
                            v___x_6937_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_6937_, 0, v___x_6931_);
                            lean_ctor_set(v___x_6937_, 1, v___x_6934_);
                            lean_ctor_set(v___x_6937_, 2, v___x_6935_);
                            lean_ctor_set(v___x_6937_, 3, v___x_6936_);
                            lean_inc(v_declHint_6923_);
                            v___x_6938_ =
                                l_Lean_MessageData_ofConstName(v_declHint_6923_, v___x_6928_);
                            v_c_6939_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_6939_, 0, v___x_6937_);
                            lean_ctor_set(v_c_6939_, 1, v___x_6938_);
                            v___x_6940_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_6927_,
                                v_declHint_6923_,
                            );
                            if lean_obj_tag(v___x_6940_) == 0 {
                                lean_dec_ref(v_env_6927_);
                                lean_dec(v_declHint_6923_);
                                v___x_6941_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
                                v___x_6942_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6942_, 0, v___x_6941_);
                                lean_ctor_set(v___x_6942_, 1, v_c_6939_);
                                v___x_6943_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
                                v___x_6944_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6944_, 0, v___x_6942_);
                                lean_ctor_set(v___x_6944_, 1, v___x_6943_);
                                v___x_6945_ = l_Lean_MessageData_note(v___x_6944_);
                                v___x_6946_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6946_, 0, v_msg_6922_);
                                lean_ctor_set(v___x_6946_, 1, v___x_6945_);
                                v___x_6947_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6947_, 0, v___x_6946_);
                                return v___x_6947_;
                            } else {
                                v_val_6948_ = lean_ctor_get(v___x_6940_, 0);
                                v_isSharedCheck_6983_ = (!lean_is_exclusive(v___x_6940_)) as u8;
                                if v_isSharedCheck_6983_ == 0 {
                                    v___x_6950_ = v___x_6940_;
                                    v_isShared_6951_ = v_isSharedCheck_6983_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_6948_);
                                    lean_dec(v___x_6940_);
                                    v___x_6950_ = lean_box(0);
                                    v_isShared_6951_ = v_isSharedCheck_6983_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_6927_);
                    lean_dec(v_declHint_6923_);
                    v___x_6984_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6984_, 0, v_msg_6922_);
                    return v___x_6984_;
                }
            }
            1 => {
                v___x_6952_ = lean_box(0);
                v___x_6953_ = l_Lean_Environment_header(v_env_6927_);
                lean_dec_ref(v_env_6927_);
                v___x_6954_ = l_Lean_EnvironmentHeader_moduleNames(v___x_6953_);
                v_mod_6955_ = lean_array_get(v___x_6952_, v___x_6954_, v_val_6948_);
                lean_dec(v_val_6948_);
                lean_dec_ref(v___x_6954_);
                v___x_6956_ = l_Lean_isPrivateName(v_declHint_6923_);
                lean_dec(v_declHint_6923_);
                if v___x_6956_ == 0 {
                    v___x_6957_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_6958_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6958_, 0, v___x_6957_);
                    lean_ctor_set(v___x_6958_, 1, v_c_6939_);
                    v___x_6959_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_6960_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6960_, 0, v___x_6958_);
                    lean_ctor_set(v___x_6960_, 1, v___x_6959_);
                    v___x_6961_ = l_Lean_MessageData_ofName(v_mod_6955_);
                    v___x_6962_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6962_, 0, v___x_6960_);
                    lean_ctor_set(v___x_6962_, 1, v___x_6961_);
                    v___x_6963_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
                    v___x_6964_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6964_, 0, v___x_6962_);
                    lean_ctor_set(v___x_6964_, 1, v___x_6963_);
                    v___x_6965_ = l_Lean_MessageData_note(v___x_6964_);
                    v___x_6966_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6966_, 0, v_msg_6922_);
                    lean_ctor_set(v___x_6966_, 1, v___x_6965_);
                    if v_isShared_6951_ == 0 {
                        lean_ctor_set_tag(v___x_6950_, 0);
                        lean_ctor_set(v___x_6950_, 0, v___x_6966_);
                        v___x_6968_ = v___x_6950_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6969_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6969_, 0, v___x_6966_);
                        v___x_6968_ = v_reuseFailAlloc_6969_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6970_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_6971_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6971_, 0, v___x_6970_);
                    lean_ctor_set(v___x_6971_, 1, v_c_6939_);
                    v___x_6972_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
                    v___x_6973_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6973_, 0, v___x_6971_);
                    lean_ctor_set(v___x_6973_, 1, v___x_6972_);
                    v___x_6974_ = l_Lean_MessageData_ofName(v_mod_6955_);
                    v___x_6975_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6975_, 0, v___x_6973_);
                    lean_ctor_set(v___x_6975_, 1, v___x_6974_);
                    v___x_6976_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
                    v___x_6977_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6977_, 0, v___x_6975_);
                    lean_ctor_set(v___x_6977_, 1, v___x_6976_);
                    v___x_6978_ = l_Lean_MessageData_note(v___x_6977_);
                    v___x_6979_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6979_, 0, v_msg_6922_);
                    lean_ctor_set(v___x_6979_, 1, v___x_6978_);
                    if v_isShared_6951_ == 0 {
                        lean_ctor_set_tag(v___x_6950_, 0);
                        lean_ctor_set(v___x_6950_, 0, v___x_6979_);
                        v___x_6981_ = v___x_6950_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6982_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6982_, 0, v___x_6979_);
                        v___x_6981_ = v_reuseFailAlloc_6982_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6968_;
            }
            3 => {
                return v___x_6981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_6985_: *mut LeanObject,
    mut v_declHint_6986_: *mut LeanObject,
    mut v___y_6987_: *mut LeanObject,
    mut v___y_6988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6989_: *mut LeanObject = core::ptr::null_mut();
    v_res_6989_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_6985_, v_declHint_6986_, v___y_6987_);
    lean_dec(v___y_6987_);
    return v_res_6989_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(
    mut v_msg_6990_: *mut LeanObject,
    mut v_declHint_6991_: *mut LeanObject,
    mut v___y_6992_: *mut LeanObject,
    mut v___y_6993_: *mut LeanObject,
    mut v___y_6994_: *mut LeanObject,
    mut v___y_6995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7001_: u8 = 0;
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6997_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_6990_, v_declHint_6991_, v___y_6995_);
                v_a_6998_ = lean_ctor_get(v___x_6997_, 0);
                v_isSharedCheck_7007_ = (!lean_is_exclusive(v___x_6997_)) as u8;
                if v_isSharedCheck_7007_ == 0 {
                    v___x_7000_ = v___x_6997_;
                    v_isShared_7001_ = v_isSharedCheck_7007_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6998_);
                    lean_dec(v___x_6997_);
                    v___x_7000_ = lean_box(0);
                    v_isShared_7001_ = v_isSharedCheck_7007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7002_ = l_Lean_unknownIdentifierMessageTag;
                v___x_7003_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_7003_, 0, v___x_7002_);
                lean_ctor_set(v___x_7003_, 1, v_a_6998_);
                if v_isShared_7001_ == 0 {
                    lean_ctor_set(v___x_7000_, 0, v___x_7003_);
                    v___x_7005_ = v___x_7000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7006_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7006_, 0, v___x_7003_);
                    v___x_7005_ = v_reuseFailAlloc_7006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(
    mut v_msg_7008_: *mut LeanObject,
    mut v_declHint_7009_: *mut LeanObject,
    mut v___y_7010_: *mut LeanObject,
    mut v___y_7011_: *mut LeanObject,
    mut v___y_7012_: *mut LeanObject,
    mut v___y_7013_: *mut LeanObject,
    mut v___y_7014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7015_: *mut LeanObject = core::ptr::null_mut();
    v_res_7015_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_7008_, v_declHint_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_);
    lean_dec(v___y_7013_);
    lean_dec_ref(v___y_7012_);
    lean_dec(v___y_7011_);
    lean_dec_ref(v___y_7010_);
    return v_res_7015_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(
    mut v_ref_7016_: *mut LeanObject,
    mut v_msg_7017_: *mut LeanObject,
    mut v___y_7018_: *mut LeanObject,
    mut v___y_7019_: *mut LeanObject,
    mut v___y_7020_: *mut LeanObject,
    mut v___y_7021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7035_: u8 = 0;
    let mut v_cancelTk_x3f_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7037_: u8 = 0;
    let mut v_inheritedTraceOptions_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_7023_ = lean_ctor_get(v___y_7020_, 0);
    v_fileMap_7024_ = lean_ctor_get(v___y_7020_, 1);
    v_options_7025_ = lean_ctor_get(v___y_7020_, 2);
    v_currRecDepth_7026_ = lean_ctor_get(v___y_7020_, 3);
    v_maxRecDepth_7027_ = lean_ctor_get(v___y_7020_, 4);
    v_ref_7028_ = lean_ctor_get(v___y_7020_, 5);
    v_currNamespace_7029_ = lean_ctor_get(v___y_7020_, 6);
    v_openDecls_7030_ = lean_ctor_get(v___y_7020_, 7);
    v_initHeartbeats_7031_ = lean_ctor_get(v___y_7020_, 8);
    v_maxHeartbeats_7032_ = lean_ctor_get(v___y_7020_, 9);
    v_quotContext_7033_ = lean_ctor_get(v___y_7020_, 10);
    v_currMacroScope_7034_ = lean_ctor_get(v___y_7020_, 11);
    v_diag_7035_ = lean_ctor_get_uint8(
        v___y_7020_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_7036_ = lean_ctor_get(v___y_7020_, 12);
    v_suppressElabErrors_7037_ = lean_ctor_get_uint8(
        v___y_7020_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_7038_ = lean_ctor_get(v___y_7020_, 13);
    v_ref_7039_ = l_Lean_replaceRef(v_ref_7016_, v_ref_7028_);
    lean_inc_ref(v_inheritedTraceOptions_7038_);
    lean_inc(v_cancelTk_x3f_7036_);
    lean_inc(v_currMacroScope_7034_);
    lean_inc(v_quotContext_7033_);
    lean_inc(v_maxHeartbeats_7032_);
    lean_inc(v_initHeartbeats_7031_);
    lean_inc(v_openDecls_7030_);
    lean_inc(v_currNamespace_7029_);
    lean_inc(v_maxRecDepth_7027_);
    lean_inc(v_currRecDepth_7026_);
    lean_inc_ref(v_options_7025_);
    lean_inc_ref(v_fileMap_7024_);
    lean_inc_ref(v_fileName_7023_);
    v___x_7040_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_7040_, 0, v_fileName_7023_);
    lean_ctor_set(v___x_7040_, 1, v_fileMap_7024_);
    lean_ctor_set(v___x_7040_, 2, v_options_7025_);
    lean_ctor_set(v___x_7040_, 3, v_currRecDepth_7026_);
    lean_ctor_set(v___x_7040_, 4, v_maxRecDepth_7027_);
    lean_ctor_set(v___x_7040_, 5, v_ref_7039_);
    lean_ctor_set(v___x_7040_, 6, v_currNamespace_7029_);
    lean_ctor_set(v___x_7040_, 7, v_openDecls_7030_);
    lean_ctor_set(v___x_7040_, 8, v_initHeartbeats_7031_);
    lean_ctor_set(v___x_7040_, 9, v_maxHeartbeats_7032_);
    lean_ctor_set(v___x_7040_, 10, v_quotContext_7033_);
    lean_ctor_set(v___x_7040_, 11, v_currMacroScope_7034_);
    lean_ctor_set(v___x_7040_, 12, v_cancelTk_x3f_7036_);
    lean_ctor_set(v___x_7040_, 13, v_inheritedTraceOptions_7038_);
    lean_ctor_set_uint8(
        v___x_7040_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_7035_,
    );
    lean_ctor_set_uint8(
        v___x_7040_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_7037_,
    );
    v___x_7041_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(
        v_msg_7017_,
        v___y_7018_,
        v___y_7019_,
        v___x_7040_,
        v___y_7021_,
    );
    lean_dec_ref_known(v___x_7040_, 14);
    return v___x_7041_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_ref_7042_: *mut LeanObject,
    mut v_msg_7043_: *mut LeanObject,
    mut v___y_7044_: *mut LeanObject,
    mut v___y_7045_: *mut LeanObject,
    mut v___y_7046_: *mut LeanObject,
    mut v___y_7047_: *mut LeanObject,
    mut v___y_7048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7049_: *mut LeanObject = core::ptr::null_mut();
    v_res_7049_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_7042_, v_msg_7043_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
    lean_dec(v___y_7047_);
    lean_dec_ref(v___y_7046_);
    lean_dec(v___y_7045_);
    lean_dec_ref(v___y_7044_);
    lean_dec(v_ref_7042_);
    return v_res_7049_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_ref_7050_: *mut LeanObject,
    mut v_msg_7051_: *mut LeanObject,
    mut v_declHint_7052_: *mut LeanObject,
    mut v___y_7053_: *mut LeanObject,
    mut v___y_7054_: *mut LeanObject,
    mut v___y_7055_: *mut LeanObject,
    mut v___y_7056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    v___x_7058_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_7051_, v_declHint_7052_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
    v_a_7059_ = lean_ctor_get(v___x_7058_, 0);
    lean_inc(v_a_7059_);
    lean_dec_ref(v___x_7058_);
    v___x_7060_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_7050_, v_a_7059_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
    return v___x_7060_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_ref_7061_: *mut LeanObject,
    mut v_msg_7062_: *mut LeanObject,
    mut v_declHint_7063_: *mut LeanObject,
    mut v___y_7064_: *mut LeanObject,
    mut v___y_7065_: *mut LeanObject,
    mut v___y_7066_: *mut LeanObject,
    mut v___y_7067_: *mut LeanObject,
    mut v___y_7068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7069_: *mut LeanObject = core::ptr::null_mut();
    v_res_7069_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_7061_, v_msg_7062_, v_declHint_7063_, v___y_7064_, v___y_7065_, v___y_7066_, v___y_7067_);
    lean_dec(v___y_7067_);
    lean_dec_ref(v___y_7066_);
    lean_dec(v___y_7065_);
    lean_dec_ref(v___y_7064_);
    lean_dec(v_ref_7061_);
    return v_res_7069_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    v___x_7071_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_7072_ = l_Lean_stringToMessageData(v___x_7071_);
    return v___x_7072_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    v___x_7074_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_7075_ = l_Lean_stringToMessageData(v___x_7074_);
    return v___x_7075_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_ref_7076_: *mut LeanObject,
    mut v_constName_7077_: *mut LeanObject,
    mut v___y_7078_: *mut LeanObject,
    mut v___y_7079_: *mut LeanObject,
    mut v___y_7080_: *mut LeanObject,
    mut v___y_7081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: u8 = 0;
    let mut v___x_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    v___x_7083_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_7084_ = 0;
    lean_inc(v_constName_7077_);
    v___x_7085_ = l_Lean_MessageData_ofConstName(v_constName_7077_, v___x_7084_);
    v___x_7086_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7086_, 0, v___x_7083_);
    lean_ctor_set(v___x_7086_, 1, v___x_7085_);
    v___x_7087_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_7088_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7088_, 0, v___x_7086_);
    lean_ctor_set(v___x_7088_, 1, v___x_7087_);
    v___x_7089_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_7076_, v___x_7088_, v_constName_7077_, v___y_7078_, v___y_7079_, v___y_7080_, v___y_7081_);
    return v___x_7089_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_7090_: *mut LeanObject,
    mut v_constName_7091_: *mut LeanObject,
    mut v___y_7092_: *mut LeanObject,
    mut v___y_7093_: *mut LeanObject,
    mut v___y_7094_: *mut LeanObject,
    mut v___y_7095_: *mut LeanObject,
    mut v___y_7096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7097_: *mut LeanObject = core::ptr::null_mut();
    v_res_7097_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_7090_, v_constName_7091_, v___y_7092_, v___y_7093_, v___y_7094_, v___y_7095_);
    lean_dec(v___y_7095_);
    lean_dec_ref(v___y_7094_);
    lean_dec(v___y_7093_);
    lean_dec_ref(v___y_7092_);
    lean_dec(v_ref_7090_);
    return v_res_7097_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(
    mut v_constName_7098_: *mut LeanObject,
    mut v___y_7099_: *mut LeanObject,
    mut v___y_7100_: *mut LeanObject,
    mut v___y_7101_: *mut LeanObject,
    mut v___y_7102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    v_ref_7104_ = lean_ctor_get(v___y_7101_, 5);
    v___x_7105_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_7104_, v_constName_7098_, v___y_7099_, v___y_7100_, v___y_7101_, v___y_7102_);
    return v___x_7105_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_7106_: *mut LeanObject,
    mut v___y_7107_: *mut LeanObject,
    mut v___y_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
    mut v___y_7110_: *mut LeanObject,
    mut v___y_7111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7112_: *mut LeanObject = core::ptr::null_mut();
    v_res_7112_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_7106_, v___y_7107_, v___y_7108_, v___y_7109_, v___y_7110_);
    lean_dec(v___y_7110_);
    lean_dec_ref(v___y_7109_);
    lean_dec(v___y_7108_);
    lean_dec_ref(v___y_7107_);
    return v_res_7112_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(
    mut v_constName_7113_: *mut LeanObject,
    mut v___y_7114_: *mut LeanObject,
    mut v___y_7115_: *mut LeanObject,
    mut v___y_7116_: *mut LeanObject,
    mut v___y_7117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: u8 = 0;
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7127_: u8 = 0;
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7131_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7119_ = lean_st_ref_get(v___y_7117_);
                v_env_7120_ = lean_ctor_get(v___x_7119_, 0);
                lean_inc_ref(v_env_7120_);
                lean_dec(v___x_7119_);
                v___x_7121_ = 0;
                lean_inc(v_constName_7113_);
                v___x_7122_ =
                    l_Lean_Environment_find_x3f(v_env_7120_, v_constName_7113_, v___x_7121_);
                if lean_obj_tag(v___x_7122_) == 0 {
                    v___x_7123_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_);
                    return v___x_7123_;
                } else {
                    lean_dec(v_constName_7113_);
                    v_val_7124_ = lean_ctor_get(v___x_7122_, 0);
                    v_isSharedCheck_7131_ = (!lean_is_exclusive(v___x_7122_)) as u8;
                    if v_isSharedCheck_7131_ == 0 {
                        v___x_7126_ = v___x_7122_;
                        v_isShared_7127_ = v_isSharedCheck_7131_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7124_);
                        lean_dec(v___x_7122_);
                        v___x_7126_ = lean_box(0);
                        v_isShared_7127_ = v_isSharedCheck_7131_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7127_ == 0 {
                    lean_ctor_set_tag(v___x_7126_, 0);
                    v___x_7129_ = v___x_7126_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7130_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7130_, 0, v_val_7124_);
                    v___x_7129_ = v_reuseFailAlloc_7130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(
    mut v_constName_7132_: *mut LeanObject,
    mut v___y_7133_: *mut LeanObject,
    mut v___y_7134_: *mut LeanObject,
    mut v___y_7135_: *mut LeanObject,
    mut v___y_7136_: *mut LeanObject,
    mut v___y_7137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7138_: *mut LeanObject = core::ptr::null_mut();
    v_res_7138_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_7132_, v___y_7133_, v___y_7134_, v___y_7135_, v___y_7136_);
    lean_dec(v___y_7136_);
    lean_dec_ref(v___y_7135_);
    lean_dec(v___y_7134_);
    lean_dec_ref(v___y_7133_);
    return v_res_7138_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(
    mut v_f_7139_: *mut LeanObject,
    mut v_a_7140_: *mut LeanObject,
    mut v_a_7141_: *mut LeanObject,
    mut v_a_7142_: *mut LeanObject,
    mut v_a_7143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7150_: u8 = 0;
    let mut v_val_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_induct_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: u8 = 0;
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: u8 = 0;
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7170_: u8 = 0;
    let mut v_a_7171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7174_: u8 = 0;
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7178_: u8 = 0;
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_f_7139_) == 4 {
                    v_declName_7145_ = lean_ctor_get(v_f_7139_, 0);
                    lean_inc(v_declName_7145_);
                    lean_dec_ref_known(v_f_7139_, 2);
                    v___x_7146_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_7145_, v_a_7140_, v_a_7141_, v_a_7142_, v_a_7143_);
                    if lean_obj_tag(v___x_7146_) == 0 {
                        v_a_7147_ = lean_ctor_get(v___x_7146_, 0);
                        v_isSharedCheck_7170_ = (!lean_is_exclusive(v___x_7146_)) as u8;
                        if v_isSharedCheck_7170_ == 0 {
                            v___x_7149_ = v___x_7146_;
                            v_isShared_7150_ = v_isSharedCheck_7170_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7147_);
                            lean_dec(v___x_7146_);
                            v___x_7149_ = lean_box(0);
                            v_isShared_7150_ = v_isSharedCheck_7170_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7171_ = lean_ctor_get(v___x_7146_, 0);
                        v_isSharedCheck_7178_ = (!lean_is_exclusive(v___x_7146_)) as u8;
                        if v_isSharedCheck_7178_ == 0 {
                            v___x_7173_ = v___x_7146_;
                            v_isShared_7174_ = v_isSharedCheck_7178_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_7171_);
                            lean_dec(v___x_7146_);
                            v___x_7173_ = lean_box(0);
                            v_isShared_7174_ = v_isSharedCheck_7178_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_7139_);
                    v___x_7179_ = lean_box(0);
                    v___x_7180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7180_, 0, v___x_7179_);
                    return v___x_7180_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_7147_) == 6 {
                    v_val_7151_ = lean_ctor_get(v_a_7147_, 0);
                    lean_inc_ref(v_val_7151_);
                    lean_dec_ref_known(v_a_7147_, 1);
                    v___x_7152_ = lean_st_ref_get(v_a_7143_);
                    v_env_7153_ = lean_ctor_get(v___x_7152_, 0);
                    lean_inc_ref(v_env_7153_);
                    lean_dec(v___x_7152_);
                    v_toConstantVal_7154_ = lean_ctor_get(v_val_7151_, 0);
                    v_induct_7155_ = lean_ctor_get(v_val_7151_, 1);
                    lean_inc_n(v_induct_7155_, 2);
                    v___x_7156_ = lean_is_class(v_env_7153_, v_induct_7155_);
                    if v___x_7156_ == 0 {
                        lean_dec(v_induct_7155_);
                        lean_dec_ref(v_val_7151_);
                        v___x_7157_ = lean_box(0);
                        if v_isShared_7150_ == 0 {
                            lean_ctor_set(v___x_7149_, 0, v___x_7157_);
                            v___x_7159_ = v___x_7149_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_7160_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7160_, 0, v___x_7157_);
                            v___x_7159_ = v_reuseFailAlloc_7160_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_7149_);
                        v_type_7161_ = lean_ctor_get(v_toConstantVal_7154_, 2);
                        lean_inc_ref(v_type_7161_);
                        v___x_7162_ = lean_box((v___x_7156_) as usize);
                        v___f_7163_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                        lean_closure_set(v___f_7163_, 0, v_val_7151_);
                        lean_closure_set(v___f_7163_, 1, v_induct_7155_);
                        lean_closure_set(v___f_7163_, 2, v___x_7162_);
                        v___x_7164_ = 0;
                        v___x_7165_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_7161_, v___f_7163_, v___x_7156_, v___x_7164_, v_a_7140_, v_a_7141_, v_a_7142_, v_a_7143_);
                        return v___x_7165_;
                    }
                } else {
                    lean_dec(v_a_7147_);
                    v___x_7166_ = lean_box(0);
                    if v_isShared_7150_ == 0 {
                        lean_ctor_set(v___x_7149_, 0, v___x_7166_);
                        v___x_7168_ = v___x_7149_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7169_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7169_, 0, v___x_7166_);
                        v___x_7168_ = v_reuseFailAlloc_7169_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7159_;
            }
            3 => {
                return v___x_7168_;
            }
            4 => {
                if v_isShared_7174_ == 0 {
                    v___x_7176_ = v___x_7173_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7177_, 0, v_a_7171_);
                    v___x_7176_ = v_reuseFailAlloc_7177_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(
    mut v_f_7181_: *mut LeanObject,
    mut v_a_7182_: *mut LeanObject,
    mut v_a_7183_: *mut LeanObject,
    mut v_a_7184_: *mut LeanObject,
    mut v_a_7185_: *mut LeanObject,
    mut v_a_7186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7187_: *mut LeanObject = core::ptr::null_mut();
    v_res_7187_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(
        v_f_7181_, v_a_7182_, v_a_7183_, v_a_7184_, v_a_7185_,
    );
    lean_dec(v_a_7185_);
    lean_dec_ref(v_a_7184_);
    lean_dec(v_a_7183_);
    lean_dec_ref(v_a_7182_);
    return v_res_7187_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(
    mut v_upperBound_7188_: *mut LeanObject,
    mut v_val_7189_: *mut LeanObject,
    mut v_xs_7190_: *mut LeanObject,
    mut v___x_7191_: *mut LeanObject,
    mut v___x_7192_: *mut LeanObject,
    mut v___x_7193_: u8,
    mut v_inst_7194_: *mut LeanObject,
    mut v_R_7195_: *mut LeanObject,
    mut v_a_7196_: *mut LeanObject,
    mut v_b_7197_: *mut LeanObject,
    mut v_c_7198_: *mut LeanObject,
    mut v___y_7199_: *mut LeanObject,
    mut v___y_7200_: *mut LeanObject,
    mut v___y_7201_: *mut LeanObject,
    mut v___y_7202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7204_: *mut LeanObject = core::ptr::null_mut();
    v___x_7204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_7188_, v_val_7189_, v_xs_7190_, v___x_7191_, v___x_7192_, v___x_7193_, v_a_7196_, v_b_7197_, v___y_7199_, v___y_7201_, v___y_7202_);
    return v___x_7204_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(
    mut v_upperBound_7205_: *mut LeanObject,
    mut v_val_7206_: *mut LeanObject,
    mut v_xs_7207_: *mut LeanObject,
    mut v___x_7208_: *mut LeanObject,
    mut v___x_7209_: *mut LeanObject,
    mut v___x_7210_: *mut LeanObject,
    mut v_inst_7211_: *mut LeanObject,
    mut v_R_7212_: *mut LeanObject,
    mut v_a_7213_: *mut LeanObject,
    mut v_b_7214_: *mut LeanObject,
    mut v_c_7215_: *mut LeanObject,
    mut v___y_7216_: *mut LeanObject,
    mut v___y_7217_: *mut LeanObject,
    mut v___y_7218_: *mut LeanObject,
    mut v___y_7219_: *mut LeanObject,
    mut v___y_7220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6330__boxed_7221_: u8 = 0;
    let mut v_res_7222_: *mut LeanObject = core::ptr::null_mut();
    v___x_6330__boxed_7221_ = (lean_unbox(v___x_7210_) as u8);
    v_res_7222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_7205_, v_val_7206_, v_xs_7207_, v___x_7208_, v___x_7209_, v___x_6330__boxed_7221_, v_inst_7211_, v_R_7212_, v_a_7213_, v_b_7214_, v_c_7215_, v___y_7216_, v___y_7217_, v___y_7218_, v___y_7219_);
    lean_dec(v___y_7219_);
    lean_dec_ref(v___y_7218_);
    lean_dec(v___y_7217_);
    lean_dec_ref(v___y_7216_);
    lean_dec_ref(v_xs_7207_);
    lean_dec_ref(v_val_7206_);
    lean_dec(v_upperBound_7205_);
    return v_res_7222_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(
    mut v_00_u03b1_7223_: *mut LeanObject,
    mut v_constName_7224_: *mut LeanObject,
    mut v___y_7225_: *mut LeanObject,
    mut v___y_7226_: *mut LeanObject,
    mut v___y_7227_: *mut LeanObject,
    mut v___y_7228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7230_: *mut LeanObject = core::ptr::null_mut();
    v___x_7230_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_7224_, v___y_7225_, v___y_7226_, v___y_7227_, v___y_7228_);
    return v___x_7230_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_7231_: *mut LeanObject,
    mut v_constName_7232_: *mut LeanObject,
    mut v___y_7233_: *mut LeanObject,
    mut v___y_7234_: *mut LeanObject,
    mut v___y_7235_: *mut LeanObject,
    mut v___y_7236_: *mut LeanObject,
    mut v___y_7237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7238_: *mut LeanObject = core::ptr::null_mut();
    v_res_7238_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_7231_, v_constName_7232_, v___y_7233_, v___y_7234_, v___y_7235_, v___y_7236_);
    lean_dec(v___y_7236_);
    lean_dec_ref(v___y_7235_);
    lean_dec(v___y_7234_);
    lean_dec_ref(v___y_7233_);
    return v_res_7238_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b1_7239_: *mut LeanObject,
    mut v_ref_7240_: *mut LeanObject,
    mut v_constName_7241_: *mut LeanObject,
    mut v___y_7242_: *mut LeanObject,
    mut v___y_7243_: *mut LeanObject,
    mut v___y_7244_: *mut LeanObject,
    mut v___y_7245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    v___x_7247_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_7240_, v_constName_7241_, v___y_7242_, v___y_7243_, v___y_7244_, v___y_7245_);
    return v___x_7247_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_7248_: *mut LeanObject,
    mut v_ref_7249_: *mut LeanObject,
    mut v_constName_7250_: *mut LeanObject,
    mut v___y_7251_: *mut LeanObject,
    mut v___y_7252_: *mut LeanObject,
    mut v___y_7253_: *mut LeanObject,
    mut v___y_7254_: *mut LeanObject,
    mut v___y_7255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7256_: *mut LeanObject = core::ptr::null_mut();
    v_res_7256_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_7248_, v_ref_7249_, v_constName_7250_, v___y_7251_, v___y_7252_, v___y_7253_, v___y_7254_);
    lean_dec(v___y_7254_);
    lean_dec_ref(v___y_7253_);
    lean_dec(v___y_7252_);
    lean_dec_ref(v___y_7251_);
    lean_dec(v_ref_7249_);
    return v_res_7256_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b1_7257_: *mut LeanObject,
    mut v_ref_7258_: *mut LeanObject,
    mut v_msg_7259_: *mut LeanObject,
    mut v_declHint_7260_: *mut LeanObject,
    mut v___y_7261_: *mut LeanObject,
    mut v___y_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
    mut v___y_7264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    v___x_7266_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_7258_, v_msg_7259_, v_declHint_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_);
    return v___x_7266_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b1_7267_: *mut LeanObject,
    mut v_ref_7268_: *mut LeanObject,
    mut v_msg_7269_: *mut LeanObject,
    mut v_declHint_7270_: *mut LeanObject,
    mut v___y_7271_: *mut LeanObject,
    mut v___y_7272_: *mut LeanObject,
    mut v___y_7273_: *mut LeanObject,
    mut v___y_7274_: *mut LeanObject,
    mut v___y_7275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7276_: *mut LeanObject = core::ptr::null_mut();
    v_res_7276_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_7267_, v_ref_7268_, v_msg_7269_, v_declHint_7270_, v___y_7271_, v___y_7272_, v___y_7273_, v___y_7274_);
    lean_dec(v___y_7274_);
    lean_dec_ref(v___y_7273_);
    lean_dec(v___y_7272_);
    lean_dec_ref(v___y_7271_);
    lean_dec(v_ref_7268_);
    return v_res_7276_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(
    mut v_msg_7277_: *mut LeanObject,
    mut v_declHint_7278_: *mut LeanObject,
    mut v___y_7279_: *mut LeanObject,
    mut v___y_7280_: *mut LeanObject,
    mut v___y_7281_: *mut LeanObject,
    mut v___y_7282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
    v___x_7284_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_7277_, v_declHint_7278_, v___y_7282_);
    return v___x_7284_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(
    mut v_msg_7285_: *mut LeanObject,
    mut v_declHint_7286_: *mut LeanObject,
    mut v___y_7287_: *mut LeanObject,
    mut v___y_7288_: *mut LeanObject,
    mut v___y_7289_: *mut LeanObject,
    mut v___y_7290_: *mut LeanObject,
    mut v___y_7291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7292_: *mut LeanObject = core::ptr::null_mut();
    v_res_7292_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_7285_, v_declHint_7286_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_);
    lean_dec(v___y_7290_);
    lean_dec_ref(v___y_7289_);
    lean_dec(v___y_7288_);
    lean_dec_ref(v___y_7287_);
    return v_res_7292_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(
    mut v_00_u03b1_7293_: *mut LeanObject,
    mut v_ref_7294_: *mut LeanObject,
    mut v_msg_7295_: *mut LeanObject,
    mut v___y_7296_: *mut LeanObject,
    mut v___y_7297_: *mut LeanObject,
    mut v___y_7298_: *mut LeanObject,
    mut v___y_7299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    v___x_7301_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_7294_, v_msg_7295_, v___y_7296_, v___y_7297_, v___y_7298_, v___y_7299_);
    return v___x_7301_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_7302_: *mut LeanObject,
    mut v_ref_7303_: *mut LeanObject,
    mut v_msg_7304_: *mut LeanObject,
    mut v___y_7305_: *mut LeanObject,
    mut v___y_7306_: *mut LeanObject,
    mut v___y_7307_: *mut LeanObject,
    mut v___y_7308_: *mut LeanObject,
    mut v___y_7309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7310_: *mut LeanObject = core::ptr::null_mut();
    v_res_7310_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_7302_, v_ref_7303_, v_msg_7304_, v___y_7305_, v___y_7306_, v___y_7307_, v___y_7308_);
    lean_dec(v___y_7308_);
    lean_dec_ref(v___y_7307_);
    lean_dec(v___y_7306_);
    lean_dec_ref(v___y_7305_);
    lean_dec(v_ref_7303_);
    return v_res_7310_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(
    mut v_info_7311_: *mut LeanObject,
    mut v_a_7312_: *mut LeanObject,
    mut v_____r_7313_: *mut LeanObject,
    mut v_result_7314_: *mut LeanObject,
    mut v___y_7315_: *mut LeanObject,
    mut v___y_7316_: *mut LeanObject,
    mut v___y_7317_: *mut LeanObject,
    mut v___y_7318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7320_: u8 = 0;
    v___x_7320_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(
        v_info_7311_,
        v_result_7314_,
        v_a_7312_,
    );
    if v___x_7320_ == 0 {
        let mut v___x_7321_: u8 = 0;
        let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
        v___x_7321_ = 0;
        v___x_7322_ = lean_box((v___x_7321_) as usize);
        v___x_7323_ = lean_array_push(v_result_7314_, v___x_7322_);
        v___x_7324_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7324_, 0, v___x_7323_);
        v___x_7325_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7325_, 0, v___x_7324_);
        return v___x_7325_;
    } else {
        let mut v___x_7326_: u8 = 0;
        let mut v___x_7327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7330_: *mut LeanObject = core::ptr::null_mut();
        v___x_7326_ = 5;
        v___x_7327_ = lean_box((v___x_7326_) as usize);
        v___x_7328_ = lean_array_push(v_result_7314_, v___x_7327_);
        v___x_7329_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_7329_, 0, v___x_7328_);
        v___x_7330_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7330_, 0, v___x_7329_);
        return v___x_7330_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(
    mut v_info_7331_: *mut LeanObject,
    mut v_a_7332_: *mut LeanObject,
    mut v_____r_7333_: *mut LeanObject,
    mut v_result_7334_: *mut LeanObject,
    mut v___y_7335_: *mut LeanObject,
    mut v___y_7336_: *mut LeanObject,
    mut v___y_7337_: *mut LeanObject,
    mut v___y_7338_: *mut LeanObject,
    mut v___y_7339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7340_: *mut LeanObject = core::ptr::null_mut();
    v_res_7340_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_7331_, v_a_7332_, v_____r_7333_, v_result_7334_, v___y_7335_, v___y_7336_, v___y_7337_, v___y_7338_);
    lean_dec(v___y_7338_);
    lean_dec_ref(v___y_7337_);
    lean_dec(v___y_7336_);
    lean_dec_ref(v___y_7335_);
    lean_dec(v_a_7332_);
    lean_dec_ref(v_info_7331_);
    return v_res_7340_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(
    mut v_info_7341_: *mut LeanObject,
    mut v_upperBound_7342_: *mut LeanObject,
    mut v___x_7343_: *mut LeanObject,
    mut v_a_7344_: *mut LeanObject,
    mut v_a_7345_: *mut LeanObject,
    mut v_b_7346_: *mut LeanObject,
    mut v___y_7347_: *mut LeanObject,
    mut v___y_7348_: *mut LeanObject,
    mut v___y_7349_: *mut LeanObject,
    mut v___y_7350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7362_: u8 = 0;
    let mut v_a_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7368_: u8 = 0;
    let mut v_a_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7372_: u8 = 0;
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7376_: u8 = 0;
    let mut v___x_7377_: u8 = 0;
    let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultDeps_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: u8 = 0;
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isProp_7382_: u8 = 0;
    let mut v_isInstance_7383_: u8 = 0;
    let mut v___x_7384_: u8 = 0;
    let mut v___x_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: u8 = 0;
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: u8 = 0;
    let mut v___x_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: u8 = 0;
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: u8 = 0;
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: u8 = 0;
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7377_ = lean_nat_dec_lt(v_a_7345_, v_upperBound_7342_);
                if v___x_7377_ == 0 {
                    lean_dec(v_a_7345_);
                    v___x_7378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7378_, 0, v_b_7346_);
                    return v___x_7378_;
                } else {
                    v_resultDeps_7379_ = lean_ctor_get(v_info_7341_, 1);
                    v___x_7380_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_7379_, v_a_7345_);
                    if v___x_7380_ == 0 {
                        v___x_7381_ = lean_array_fget_borrowed(v___x_7343_, v_a_7345_);
                        v_isProp_7382_ = lean_ctor_get_uint8(
                            v___x_7381_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        );
                        if v_isProp_7382_ == 0 {
                            v_isInstance_7383_ = lean_ctor_get_uint8(
                                v___x_7381_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                            );
                            if v_isInstance_7383_ == 0 {
                                v___x_7384_ = 2;
                                v___x_7385_ = lean_box((v___x_7384_) as usize);
                                v___x_7386_ = lean_array_push(v_b_7346_, v___x_7385_);
                                v_a_7353_ = v___x_7386_;
                                state = 1;
                                continue;
                            } else {
                                if lean_obj_tag(v_a_7344_) == 1 {
                                    v_val_7387_ = lean_ctor_get(v_a_7344_, 0);
                                    v___x_7388_ = lean_array_get_size(v_val_7387_);
                                    v___x_7389_ = lean_nat_dec_lt(v_a_7345_, v___x_7388_);
                                    if v___x_7389_ == 0 {
                                        v___x_7390_ = lean_box(0);
                                        v___x_7391_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_7341_, v_a_7345_, v___x_7390_, v_b_7346_, v___y_7347_, v___y_7348_, v___y_7349_, v___y_7350_);
                                        v___y_7358_ = v___x_7391_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_7392_ =
                                            lean_array_fget_borrowed(v_val_7387_, v_a_7345_);
                                        v___x_7393_ = (lean_unbox(v___x_7392_) as u8);
                                        if v___x_7393_ == 0 {
                                            v___x_7394_ = lean_box(0);
                                            v___x_7395_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_7341_, v_a_7345_, v___x_7394_, v_b_7346_, v___y_7347_, v___y_7348_, v___y_7349_, v___y_7350_);
                                            v___y_7358_ = v___x_7395_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_7396_ = 2;
                                            v___x_7397_ = lean_box((v___x_7396_) as usize);
                                            v___x_7398_ = lean_array_push(v_b_7346_, v___x_7397_);
                                            v_a_7353_ = v___x_7398_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_7399_ = lean_box(0);
                                    v___x_7400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_7341_, v_a_7345_, v___x_7399_, v_b_7346_, v___y_7347_, v___y_7348_, v___y_7349_, v___y_7350_);
                                    v___y_7358_ = v___x_7400_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            v___x_7401_ = 3;
                            v___x_7402_ = lean_box((v___x_7401_) as usize);
                            v___x_7403_ = lean_array_push(v_b_7346_, v___x_7402_);
                            v_a_7353_ = v___x_7403_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7404_ = 0;
                        v___x_7405_ = lean_box((v___x_7404_) as usize);
                        v___x_7406_ = lean_array_push(v_b_7346_, v___x_7405_);
                        v_a_7353_ = v___x_7406_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7354_ = lean_unsigned_to_nat(1);
                v___x_7355_ = lean_nat_add(v_a_7345_, v___x_7354_);
                lean_dec(v_a_7345_);
                v_a_7345_ = v___x_7355_;
                v_b_7346_ = v_a_7353_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_7358_) == 0 {
                    v_a_7359_ = lean_ctor_get(v___y_7358_, 0);
                    v_isSharedCheck_7368_ = (!lean_is_exclusive(v___y_7358_)) as u8;
                    if v_isSharedCheck_7368_ == 0 {
                        v___x_7361_ = v___y_7358_;
                        v_isShared_7362_ = v_isSharedCheck_7368_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7359_);
                        lean_dec(v___y_7358_);
                        v___x_7361_ = lean_box(0);
                        v_isShared_7362_ = v_isSharedCheck_7368_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_7345_);
                    v_a_7369_ = lean_ctor_get(v___y_7358_, 0);
                    v_isSharedCheck_7376_ = (!lean_is_exclusive(v___y_7358_)) as u8;
                    if v_isSharedCheck_7376_ == 0 {
                        v___x_7371_ = v___y_7358_;
                        v_isShared_7372_ = v_isSharedCheck_7376_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7369_);
                        lean_dec(v___y_7358_);
                        v___x_7371_ = lean_box(0);
                        v_isShared_7372_ = v_isSharedCheck_7376_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_7359_) == 0 {
                    lean_dec(v_a_7345_);
                    v_a_7363_ = lean_ctor_get(v_a_7359_, 0);
                    lean_inc(v_a_7363_);
                    lean_dec_ref_known(v_a_7359_, 1);
                    if v_isShared_7362_ == 0 {
                        lean_ctor_set(v___x_7361_, 0, v_a_7363_);
                        v___x_7365_ = v___x_7361_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7366_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7366_, 0, v_a_7363_);
                        v___x_7365_ = v_reuseFailAlloc_7366_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7361_);
                    v_a_7367_ = lean_ctor_get(v_a_7359_, 0);
                    lean_inc(v_a_7367_);
                    lean_dec_ref_known(v_a_7359_, 1);
                    v_a_7353_ = v_a_7367_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_7365_;
            }
            5 => {
                if v_isShared_7372_ == 0 {
                    v___x_7374_ = v___x_7371_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7375_, 0, v_a_7369_);
                    v___x_7374_ = v_reuseFailAlloc_7375_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(
    mut v_info_7407_: *mut LeanObject,
    mut v_upperBound_7408_: *mut LeanObject,
    mut v___x_7409_: *mut LeanObject,
    mut v_a_7410_: *mut LeanObject,
    mut v_a_7411_: *mut LeanObject,
    mut v_b_7412_: *mut LeanObject,
    mut v___y_7413_: *mut LeanObject,
    mut v___y_7414_: *mut LeanObject,
    mut v___y_7415_: *mut LeanObject,
    mut v___y_7416_: *mut LeanObject,
    mut v___y_7417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7418_: *mut LeanObject = core::ptr::null_mut();
    v_res_7418_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(
            v_info_7407_,
            v_upperBound_7408_,
            v___x_7409_,
            v_a_7410_,
            v_a_7411_,
            v_b_7412_,
            v___y_7413_,
            v___y_7414_,
            v___y_7415_,
            v___y_7416_,
        );
    lean_dec(v___y_7416_);
    lean_dec_ref(v___y_7415_);
    lean_dec(v___y_7414_);
    lean_dec_ref(v___y_7413_);
    lean_dec(v_a_7410_);
    lean_dec_ref(v___x_7409_);
    lean_dec(v_upperBound_7408_);
    lean_dec_ref(v_info_7407_);
    return v_res_7418_;
}
pub unsafe fn l_Lean_Meta_getCongrSimpKinds(
    mut v_f_7421_: *mut LeanObject,
    mut v_info_7422_: *mut LeanObject,
    mut v_a_7423_: *mut LeanObject,
    mut v_a_7424_: *mut LeanObject,
    mut v_a_7425_: *mut LeanObject,
    mut v_a_7426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_7430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_7433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7438_: u8 = 0;
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7443_: u8 = 0;
    let mut v_a_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7447_: u8 = 0;
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7428_ =
                    l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(
                        v_f_7421_, v_a_7423_, v_a_7424_, v_a_7425_, v_a_7426_,
                    );
                if lean_obj_tag(v___x_7428_) == 0 {
                    v_a_7429_ = lean_ctor_get(v___x_7428_, 0);
                    lean_inc(v_a_7429_);
                    lean_dec_ref_known(v___x_7428_, 1);
                    v_paramInfo_7430_ = lean_ctor_get(v_info_7422_, 0);
                    v___x_7431_ = lean_array_get_size(v_paramInfo_7430_);
                    v___x_7432_ = lean_unsigned_to_nat(0);
                    v_result_7433_ = l_Lean_Meta_getCongrSimpKinds___closed__0;
                    v___x_7434_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_7422_, v___x_7431_, v_paramInfo_7430_, v_a_7429_, v___x_7432_, v_result_7433_, v_a_7423_, v_a_7424_, v_a_7425_, v_a_7426_);
                    lean_dec(v_a_7429_);
                    if lean_obj_tag(v___x_7434_) == 0 {
                        v_a_7435_ = lean_ctor_get(v___x_7434_, 0);
                        v_isSharedCheck_7443_ = (!lean_is_exclusive(v___x_7434_)) as u8;
                        if v_isSharedCheck_7443_ == 0 {
                            v___x_7437_ = v___x_7434_;
                            v_isShared_7438_ = v_isSharedCheck_7443_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7435_);
                            lean_dec(v___x_7434_);
                            v___x_7437_ = lean_box(0);
                            v_isShared_7438_ = v_isSharedCheck_7443_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_7434_;
                    }
                } else {
                    v_a_7444_ = lean_ctor_get(v___x_7428_, 0);
                    v_isSharedCheck_7451_ = (!lean_is_exclusive(v___x_7428_)) as u8;
                    if v_isSharedCheck_7451_ == 0 {
                        v___x_7446_ = v___x_7428_;
                        v_isShared_7447_ = v_isSharedCheck_7451_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7444_);
                        lean_dec(v___x_7428_);
                        v___x_7446_ = lean_box(0);
                        v_isShared_7447_ = v_isSharedCheck_7451_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7439_ =
                    l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(
                        v_info_7422_,
                        v_a_7435_,
                    );
                if v_isShared_7438_ == 0 {
                    lean_ctor_set(v___x_7437_, 0, v___x_7439_);
                    v___x_7441_ = v___x_7437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7442_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7442_, 0, v___x_7439_);
                    v___x_7441_ = v_reuseFailAlloc_7442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7441_;
            }
            3 => {
                if v_isShared_7447_ == 0 {
                    v___x_7449_ = v___x_7446_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7450_, 0, v_a_7444_);
                    v___x_7449_ = v_reuseFailAlloc_7450_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getCongrSimpKinds___boxed(
    mut v_f_7452_: *mut LeanObject,
    mut v_info_7453_: *mut LeanObject,
    mut v_a_7454_: *mut LeanObject,
    mut v_a_7455_: *mut LeanObject,
    mut v_a_7456_: *mut LeanObject,
    mut v_a_7457_: *mut LeanObject,
    mut v_a_7458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7459_: *mut LeanObject = core::ptr::null_mut();
    v_res_7459_ = l_Lean_Meta_getCongrSimpKinds(
        v_f_7452_,
        v_info_7453_,
        v_a_7454_,
        v_a_7455_,
        v_a_7456_,
        v_a_7457_,
    );
    lean_dec(v_a_7457_);
    lean_dec_ref(v_a_7456_);
    lean_dec(v_a_7455_);
    lean_dec_ref(v_a_7454_);
    lean_dec_ref(v_info_7453_);
    return v_res_7459_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(
    mut v_info_7460_: *mut LeanObject,
    mut v_upperBound_7461_: *mut LeanObject,
    mut v___x_7462_: *mut LeanObject,
    mut v_a_7463_: *mut LeanObject,
    mut v_inst_7464_: *mut LeanObject,
    mut v_R_7465_: *mut LeanObject,
    mut v_a_7466_: *mut LeanObject,
    mut v_b_7467_: *mut LeanObject,
    mut v_c_7468_: *mut LeanObject,
    mut v___y_7469_: *mut LeanObject,
    mut v___y_7470_: *mut LeanObject,
    mut v___y_7471_: *mut LeanObject,
    mut v___y_7472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7474_: *mut LeanObject = core::ptr::null_mut();
    v___x_7474_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(
            v_info_7460_,
            v_upperBound_7461_,
            v___x_7462_,
            v_a_7463_,
            v_a_7466_,
            v_b_7467_,
            v___y_7469_,
            v___y_7470_,
            v___y_7471_,
            v___y_7472_,
        );
    return v___x_7474_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(
    mut v_info_7475_: *mut LeanObject,
    mut v_upperBound_7476_: *mut LeanObject,
    mut v___x_7477_: *mut LeanObject,
    mut v_a_7478_: *mut LeanObject,
    mut v_inst_7479_: *mut LeanObject,
    mut v_R_7480_: *mut LeanObject,
    mut v_a_7481_: *mut LeanObject,
    mut v_b_7482_: *mut LeanObject,
    mut v_c_7483_: *mut LeanObject,
    mut v___y_7484_: *mut LeanObject,
    mut v___y_7485_: *mut LeanObject,
    mut v___y_7486_: *mut LeanObject,
    mut v___y_7487_: *mut LeanObject,
    mut v___y_7488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7489_: *mut LeanObject = core::ptr::null_mut();
    v_res_7489_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(
        v_info_7475_,
        v_upperBound_7476_,
        v___x_7477_,
        v_a_7478_,
        v_inst_7479_,
        v_R_7480_,
        v_a_7481_,
        v_b_7482_,
        v_c_7483_,
        v___y_7484_,
        v___y_7485_,
        v___y_7486_,
        v___y_7487_,
    );
    lean_dec(v___y_7487_);
    lean_dec_ref(v___y_7486_);
    lean_dec(v___y_7485_);
    lean_dec_ref(v___y_7484_);
    lean_dec(v_a_7478_);
    lean_dec_ref(v___x_7477_);
    lean_dec(v_upperBound_7476_);
    lean_dec_ref(v_info_7475_);
    return v_res_7489_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(
    mut v_upperBound_7490_: *mut LeanObject,
    mut v_info_7491_: *mut LeanObject,
    mut v___x_7492_: *mut LeanObject,
    mut v_a_7493_: *mut LeanObject,
    mut v_b_7494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: u8 = 0;
    let mut v___x_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultDeps_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: u8 = 0;
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: u8 = 0;
    let mut v___x_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isProp_7508_: u8 = 0;
    let mut v_isInstance_7509_: u8 = 0;
    let mut v___x_7510_: u8 = 0;
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: u8 = 0;
    let mut v___x_7514_: u8 = 0;
    let mut v___x_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: u8 = 0;
    let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: u8 = 0;
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: u8 = 0;
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: u8 = 0;
    let mut v___x_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7501_ = lean_nat_dec_lt(v_a_7493_, v_upperBound_7490_);
                if v___x_7501_ == 0 {
                    lean_dec(v_a_7493_);
                    v___x_7502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7502_, 0, v_b_7494_);
                    return v___x_7502_;
                } else {
                    v_resultDeps_7503_ = lean_ctor_get(v_info_7491_, 1);
                    v___x_7504_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_7503_, v_a_7493_);
                    if v___x_7504_ == 0 {
                        v___x_7505_ = lean_unsigned_to_nat(0);
                        v___x_7506_ = lean_nat_dec_eq(v_a_7493_, v___x_7505_);
                        if v___x_7506_ == 0 {
                            v___x_7507_ = lean_array_fget_borrowed(v___x_7492_, v_a_7493_);
                            v_isProp_7508_ = lean_ctor_get_uint8(
                                v___x_7507_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                            );
                            if v_isProp_7508_ == 0 {
                                v_isInstance_7509_ = lean_ctor_get_uint8(
                                    v___x_7507_,
                                    (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                                );
                                if v_isInstance_7509_ == 0 {
                                    v___x_7510_ = 0;
                                    v___x_7511_ = lean_box((v___x_7510_) as usize);
                                    v___x_7512_ = lean_array_push(v_b_7494_, v___x_7511_);
                                    v_a_7497_ = v___x_7512_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_7513_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_7491_, v_b_7494_, v_a_7493_);
                                    if v___x_7513_ == 0 {
                                        v___x_7514_ = 0;
                                        v___x_7515_ = lean_box((v___x_7514_) as usize);
                                        v___x_7516_ = lean_array_push(v_b_7494_, v___x_7515_);
                                        v_a_7497_ = v___x_7516_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_7517_ = 5;
                                        v___x_7518_ = lean_box((v___x_7517_) as usize);
                                        v___x_7519_ = lean_array_push(v_b_7494_, v___x_7518_);
                                        v_a_7497_ = v___x_7519_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_7520_ = 3;
                                v___x_7521_ = lean_box((v___x_7520_) as usize);
                                v___x_7522_ = lean_array_push(v_b_7494_, v___x_7521_);
                                v_a_7497_ = v___x_7522_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_7523_ = 2;
                            v___x_7524_ = lean_box((v___x_7523_) as usize);
                            v___x_7525_ = lean_array_push(v_b_7494_, v___x_7524_);
                            v_a_7497_ = v___x_7525_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7526_ = 0;
                        v___x_7527_ = lean_box((v___x_7526_) as usize);
                        v___x_7528_ = lean_array_push(v_b_7494_, v___x_7527_);
                        v_a_7497_ = v___x_7528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7498_ = lean_unsigned_to_nat(1);
                v___x_7499_ = lean_nat_add(v_a_7493_, v___x_7498_);
                lean_dec(v_a_7493_);
                v_a_7493_ = v___x_7499_;
                v_b_7494_ = v_a_7497_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(
    mut v_upperBound_7529_: *mut LeanObject,
    mut v_info_7530_: *mut LeanObject,
    mut v___x_7531_: *mut LeanObject,
    mut v_a_7532_: *mut LeanObject,
    mut v_b_7533_: *mut LeanObject,
    mut v___y_7534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7535_: *mut LeanObject = core::ptr::null_mut();
    v_res_7535_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_7529_, v_info_7530_, v___x_7531_, v_a_7532_, v_b_7533_);
    lean_dec_ref(v___x_7531_);
    lean_dec_ref(v_info_7530_);
    lean_dec(v_upperBound_7529_);
    return v_res_7535_;
}
pub unsafe fn l_Lean_Meta_getCongrSimpKindsForArgZero(
    mut v_info_7536_: *mut LeanObject,
    mut v_a_7537_: *mut LeanObject,
    mut v_a_7538_: *mut LeanObject,
    mut v_a_7539_: *mut LeanObject,
    mut v_a_7540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_paramInfo_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7550_: u8 = 0;
    let mut v___x_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_paramInfo_7542_ = lean_ctor_get(v_info_7536_, 0);
                v___x_7543_ = lean_array_get_size(v_paramInfo_7542_);
                v___x_7544_ = lean_unsigned_to_nat(0);
                v_result_7545_ = l_Lean_Meta_getCongrSimpKinds___closed__0;
                v___x_7546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_7543_, v_info_7536_, v_paramInfo_7542_, v___x_7544_, v_result_7545_);
                if lean_obj_tag(v___x_7546_) == 0 {
                    v_a_7547_ = lean_ctor_get(v___x_7546_, 0);
                    v_isSharedCheck_7555_ = (!lean_is_exclusive(v___x_7546_)) as u8;
                    if v_isSharedCheck_7555_ == 0 {
                        v___x_7549_ = v___x_7546_;
                        v_isShared_7550_ = v_isSharedCheck_7555_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7547_);
                        lean_dec(v___x_7546_);
                        v___x_7549_ = lean_box(0);
                        v_isShared_7550_ = v_isSharedCheck_7555_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_7546_;
                }
            }
            1 => {
                v___x_7551_ =
                    l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(
                        v_info_7536_,
                        v_a_7547_,
                    );
                if v_isShared_7550_ == 0 {
                    lean_ctor_set(v___x_7549_, 0, v___x_7551_);
                    v___x_7553_ = v___x_7549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7554_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7554_, 0, v___x_7551_);
                    v___x_7553_ = v_reuseFailAlloc_7554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(
    mut v_info_7556_: *mut LeanObject,
    mut v_a_7557_: *mut LeanObject,
    mut v_a_7558_: *mut LeanObject,
    mut v_a_7559_: *mut LeanObject,
    mut v_a_7560_: *mut LeanObject,
    mut v_a_7561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7562_: *mut LeanObject = core::ptr::null_mut();
    v_res_7562_ = l_Lean_Meta_getCongrSimpKindsForArgZero(
        v_info_7556_,
        v_a_7557_,
        v_a_7558_,
        v_a_7559_,
        v_a_7560_,
    );
    lean_dec(v_a_7560_);
    lean_dec_ref(v_a_7559_);
    lean_dec(v_a_7558_);
    lean_dec_ref(v_a_7557_);
    lean_dec_ref(v_info_7556_);
    return v_res_7562_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(
    mut v_upperBound_7563_: *mut LeanObject,
    mut v_info_7564_: *mut LeanObject,
    mut v___x_7565_: *mut LeanObject,
    mut v_inst_7566_: *mut LeanObject,
    mut v_R_7567_: *mut LeanObject,
    mut v_a_7568_: *mut LeanObject,
    mut v_b_7569_: *mut LeanObject,
    mut v_c_7570_: *mut LeanObject,
    mut v___y_7571_: *mut LeanObject,
    mut v___y_7572_: *mut LeanObject,
    mut v___y_7573_: *mut LeanObject,
    mut v___y_7574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    v___x_7576_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_7563_, v_info_7564_, v___x_7565_, v_a_7568_, v_b_7569_);
    return v___x_7576_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(
    mut v_upperBound_7577_: *mut LeanObject,
    mut v_info_7578_: *mut LeanObject,
    mut v___x_7579_: *mut LeanObject,
    mut v_inst_7580_: *mut LeanObject,
    mut v_R_7581_: *mut LeanObject,
    mut v_a_7582_: *mut LeanObject,
    mut v_b_7583_: *mut LeanObject,
    mut v_c_7584_: *mut LeanObject,
    mut v___y_7585_: *mut LeanObject,
    mut v___y_7586_: *mut LeanObject,
    mut v___y_7587_: *mut LeanObject,
    mut v___y_7588_: *mut LeanObject,
    mut v___y_7589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7590_: *mut LeanObject = core::ptr::null_mut();
    v_res_7590_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(
            v_upperBound_7577_,
            v_info_7578_,
            v___x_7579_,
            v_inst_7580_,
            v_R_7581_,
            v_a_7582_,
            v_b_7583_,
            v_c_7584_,
            v___y_7585_,
            v___y_7586_,
            v___y_7587_,
            v___y_7588_,
        );
    lean_dec(v___y_7588_);
    lean_dec_ref(v___y_7587_);
    lean_dec(v___y_7586_);
    lean_dec_ref(v___y_7585_);
    lean_dec_ref(v___x_7579_);
    lean_dec_ref(v_info_7578_);
    lean_dec(v_upperBound_7577_);
    return v_res_7590_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(
    mut v_x_7591_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_7591_) == 0 {
        let mut v___x_7592_: *mut LeanObject = core::ptr::null_mut();
        v___x_7592_ = lean_unsigned_to_nat(0);
        return v___x_7592_;
    } else {
        let mut v___x_7593_: *mut LeanObject = core::ptr::null_mut();
        v___x_7593_ = lean_unsigned_to_nat(1);
        return v___x_7593_;
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(
    mut v_x_7594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7595_: *mut LeanObject = core::ptr::null_mut();
    v_res_7595_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(v_x_7594_);
    lean_dec_ref(v_x_7594_);
    return v_res_7595_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(
    mut v_t_7596_: *mut LeanObject,
    mut v_k_7597_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_7596_) == 0 {
        let mut v_fvarId_7598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7599_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_7598_ = lean_ctor_get(v_t_7596_, 0);
        lean_inc(v_fvarId_7598_);
        lean_dec_ref_known(v_t_7596_, 1);
        v___x_7599_ = lean_apply_1(v_k_7597_, v_fvarId_7598_);
        return v___x_7599_;
    } else {
        let mut v_lhs_7600_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_7601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
        v_lhs_7600_ = lean_ctor_get(v_t_7596_, 0);
        lean_inc(v_lhs_7600_);
        v_rhs_7601_ = lean_ctor_get(v_t_7596_, 1);
        lean_inc(v_rhs_7601_);
        lean_dec_ref_known(v_t_7596_, 2);
        v___x_7602_ = lean_apply_2(v_k_7597_, v_lhs_7600_, v_rhs_7601_);
        return v___x_7602_;
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(
    mut v_motive_7603_: *mut LeanObject,
    mut v_ctorIdx_7604_: *mut LeanObject,
    mut v_t_7605_: *mut LeanObject,
    mut v_h_7606_: *mut LeanObject,
    mut v_k_7607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7608_: *mut LeanObject = core::ptr::null_mut();
    v___x_7608_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(
        v_t_7605_, v_k_7607_,
    );
    return v___x_7608_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(
    mut v_motive_7609_: *mut LeanObject,
    mut v_ctorIdx_7610_: *mut LeanObject,
    mut v_t_7611_: *mut LeanObject,
    mut v_h_7612_: *mut LeanObject,
    mut v_k_7613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7614_: *mut LeanObject = core::ptr::null_mut();
    v_res_7614_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(
        v_motive_7609_,
        v_ctorIdx_7610_,
        v_t_7611_,
        v_h_7612_,
        v_k_7613_,
    );
    lean_dec(v_ctorIdx_7610_);
    return v_res_7614_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(
    mut v_t_7615_: *mut LeanObject,
    mut v_hyp_7616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7617_: *mut LeanObject = core::ptr::null_mut();
    v___x_7617_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(
        v_t_7615_,
        v_hyp_7616_,
    );
    return v___x_7617_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(
    mut v_motive_7618_: *mut LeanObject,
    mut v_t_7619_: *mut LeanObject,
    mut v_h_7620_: *mut LeanObject,
    mut v_hyp_7621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7622_: *mut LeanObject = core::ptr::null_mut();
    v___x_7622_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(
        v_t_7619_,
        v_hyp_7621_,
    );
    return v___x_7622_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(
    mut v_t_7623_: *mut LeanObject,
    mut v_decSubsingleton_7624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7625_: *mut LeanObject = core::ptr::null_mut();
    v___x_7625_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(
        v_t_7623_,
        v_decSubsingleton_7624_,
    );
    return v___x_7625_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(
    mut v_motive_7626_: *mut LeanObject,
    mut v_t_7627_: *mut LeanObject,
    mut v_h_7628_: *mut LeanObject,
    mut v_decSubsingleton_7629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    v___x_7630_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(
        v_t_7627_,
        v_decSubsingleton_7629_,
    );
    return v___x_7630_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(
    mut v_s_7631_: *mut LeanObject,
    mut v_fvarId_7632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7633_: *mut LeanObject = core::ptr::null_mut();
    v___x_7633_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_7631_, v_fvarId_7632_);
    if lean_obj_tag(v___x_7633_) == 1 {
        let mut v_val_7634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7635_: *mut LeanObject = core::ptr::null_mut();
        v_val_7634_ = lean_ctor_get(v___x_7633_, 0);
        lean_inc(v_val_7634_);
        lean_dec_ref_known(v___x_7633_, 1);
        v___x_7635_ = l_Lean_Expr_fvarId_x21(v_val_7634_);
        lean_dec(v_val_7634_);
        return v___x_7635_;
    } else {
        lean_dec(v___x_7633_);
        lean_inc(v_fvarId_7632_);
        return v_fvarId_7632_;
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(
    mut v_s_7636_: *mut LeanObject,
    mut v_fvarId_7637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7638_: *mut LeanObject = core::ptr::null_mut();
    v_res_7638_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_7636_, v_fvarId_7637_);
    lean_dec(v_fvarId_7637_);
    lean_dec(v_s_7636_);
    return v_res_7638_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(
    mut v_mvarId_7639_: *mut LeanObject,
    mut v_x_7640_: *mut LeanObject,
    mut v___y_7641_: *mut LeanObject,
    mut v___y_7642_: *mut LeanObject,
    mut v___y_7643_: *mut LeanObject,
    mut v___y_7644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7650_: u8 = 0;
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7654_: u8 = 0;
    let mut v_a_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7658_: u8 = 0;
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7646_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_7639_,
                    v_x_7640_,
                    v___y_7641_,
                    v___y_7642_,
                    v___y_7643_,
                    v___y_7644_,
                );
                if lean_obj_tag(v___x_7646_) == 0 {
                    v_a_7647_ = lean_ctor_get(v___x_7646_, 0);
                    v_isSharedCheck_7654_ = (!lean_is_exclusive(v___x_7646_)) as u8;
                    if v_isSharedCheck_7654_ == 0 {
                        v___x_7649_ = v___x_7646_;
                        v_isShared_7650_ = v_isSharedCheck_7654_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7647_);
                        lean_dec(v___x_7646_);
                        v___x_7649_ = lean_box(0);
                        v_isShared_7650_ = v_isSharedCheck_7654_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7655_ = lean_ctor_get(v___x_7646_, 0);
                    v_isSharedCheck_7662_ = (!lean_is_exclusive(v___x_7646_)) as u8;
                    if v_isSharedCheck_7662_ == 0 {
                        v___x_7657_ = v___x_7646_;
                        v_isShared_7658_ = v_isSharedCheck_7662_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7655_);
                        lean_dec(v___x_7646_);
                        v___x_7657_ = lean_box(0);
                        v_isShared_7658_ = v_isSharedCheck_7662_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7650_ == 0 {
                    v___x_7652_ = v___x_7649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7653_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 0, v_a_7647_);
                    v___x_7652_ = v_reuseFailAlloc_7653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7652_;
            }
            3 => {
                if v_isShared_7658_ == 0 {
                    v___x_7660_ = v___x_7657_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7661_, 0, v_a_7655_);
                    v___x_7660_ = v_reuseFailAlloc_7661_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(
    mut v_mvarId_7663_: *mut LeanObject,
    mut v_x_7664_: *mut LeanObject,
    mut v___y_7665_: *mut LeanObject,
    mut v___y_7666_: *mut LeanObject,
    mut v___y_7667_: *mut LeanObject,
    mut v___y_7668_: *mut LeanObject,
    mut v___y_7669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7670_: *mut LeanObject = core::ptr::null_mut();
    v_res_7670_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_7663_, v_x_7664_, v___y_7665_, v___y_7666_, v___y_7667_, v___y_7668_);
    lean_dec(v___y_7668_);
    lean_dec_ref(v___y_7667_);
    lean_dec(v___y_7666_);
    lean_dec_ref(v___y_7665_);
    return v_res_7670_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(
    mut v_00_u03b1_7671_: *mut LeanObject,
    mut v_mvarId_7672_: *mut LeanObject,
    mut v_x_7673_: *mut LeanObject,
    mut v___y_7674_: *mut LeanObject,
    mut v___y_7675_: *mut LeanObject,
    mut v___y_7676_: *mut LeanObject,
    mut v___y_7677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    v___x_7679_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_7672_, v_x_7673_, v___y_7674_, v___y_7675_, v___y_7676_, v___y_7677_);
    return v___x_7679_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(
    mut v_00_u03b1_7680_: *mut LeanObject,
    mut v_mvarId_7681_: *mut LeanObject,
    mut v_x_7682_: *mut LeanObject,
    mut v___y_7683_: *mut LeanObject,
    mut v___y_7684_: *mut LeanObject,
    mut v___y_7685_: *mut LeanObject,
    mut v___y_7686_: *mut LeanObject,
    mut v___y_7687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7688_: *mut LeanObject = core::ptr::null_mut();
    v_res_7688_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_7680_, v_mvarId_7681_, v_x_7682_, v___y_7683_, v___y_7684_, v___y_7685_, v___y_7686_);
    lean_dec(v___y_7686_);
    lean_dec_ref(v___y_7685_);
    lean_dec(v___y_7684_);
    lean_dec_ref(v___y_7683_);
    return v_res_7688_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(
    mut v_e_7689_: *mut LeanObject,
    mut v___y_7690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7692_: u8 = 0;
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7706_: u8 = 0;
    let mut v___x_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7712_: u8 = 0;
    let mut v_unused_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7692_ = l_Lean_Expr_hasMVar(v_e_7689_);
                if v___x_7692_ == 0 {
                    v___x_7693_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7693_, 0, v_e_7689_);
                    return v___x_7693_;
                } else {
                    v___x_7694_ = lean_st_ref_get(v___y_7690_);
                    v_mctx_7695_ = lean_ctor_get(v___x_7694_, 0);
                    lean_inc_ref(v_mctx_7695_);
                    lean_dec(v___x_7694_);
                    v___x_7696_ = l_Lean_instantiateMVarsCore(v_mctx_7695_, v_e_7689_);
                    v_fst_7697_ = lean_ctor_get(v___x_7696_, 0);
                    lean_inc(v_fst_7697_);
                    v_snd_7698_ = lean_ctor_get(v___x_7696_, 1);
                    lean_inc(v_snd_7698_);
                    lean_dec_ref(v___x_7696_);
                    v___x_7699_ = lean_st_ref_take(v___y_7690_);
                    v_cache_7700_ = lean_ctor_get(v___x_7699_, 1);
                    v_zetaDeltaFVarIds_7701_ = lean_ctor_get(v___x_7699_, 2);
                    v_postponed_7702_ = lean_ctor_get(v___x_7699_, 3);
                    v_diag_7703_ = lean_ctor_get(v___x_7699_, 4);
                    v_isSharedCheck_7712_ = (!lean_is_exclusive(v___x_7699_)) as u8;
                    if v_isSharedCheck_7712_ == 0 {
                        v_unused_7713_ = lean_ctor_get(v___x_7699_, 0);
                        lean_dec(v_unused_7713_);
                        v___x_7705_ = v___x_7699_;
                        v_isShared_7706_ = v_isSharedCheck_7712_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_7703_);
                        lean_inc(v_postponed_7702_);
                        lean_inc(v_zetaDeltaFVarIds_7701_);
                        lean_inc(v_cache_7700_);
                        lean_dec(v___x_7699_);
                        v___x_7705_ = lean_box(0);
                        v_isShared_7706_ = v_isSharedCheck_7712_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7706_ == 0 {
                    lean_ctor_set(v___x_7705_, 0, v_snd_7698_);
                    v___x_7708_ = v___x_7705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7711_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7711_, 0, v_snd_7698_);
                    lean_ctor_set(v_reuseFailAlloc_7711_, 1, v_cache_7700_);
                    lean_ctor_set(v_reuseFailAlloc_7711_, 2, v_zetaDeltaFVarIds_7701_);
                    lean_ctor_set(v_reuseFailAlloc_7711_, 3, v_postponed_7702_);
                    lean_ctor_set(v_reuseFailAlloc_7711_, 4, v_diag_7703_);
                    v___x_7708_ = v_reuseFailAlloc_7711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7709_ = lean_st_ref_set(v___y_7690_, v___x_7708_);
                v___x_7710_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7710_, 0, v_fst_7697_);
                return v___x_7710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(
    mut v_e_7714_: *mut LeanObject,
    mut v___y_7715_: *mut LeanObject,
    mut v___y_7716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7717_: *mut LeanObject = core::ptr::null_mut();
    v_res_7717_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_7714_, v___y_7715_);
    lean_dec(v___y_7715_);
    return v_res_7717_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(
    mut v_e_7718_: *mut LeanObject,
    mut v___y_7719_: *mut LeanObject,
    mut v___y_7720_: *mut LeanObject,
    mut v___y_7721_: *mut LeanObject,
    mut v___y_7722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7724_: *mut LeanObject = core::ptr::null_mut();
    v___x_7724_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_7718_, v___y_7720_);
    return v___x_7724_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(
    mut v_e_7725_: *mut LeanObject,
    mut v___y_7726_: *mut LeanObject,
    mut v___y_7727_: *mut LeanObject,
    mut v___y_7728_: *mut LeanObject,
    mut v___y_7729_: *mut LeanObject,
    mut v___y_7730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7731_: *mut LeanObject = core::ptr::null_mut();
    v_res_7731_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_7725_, v___y_7726_, v___y_7727_, v___y_7728_, v___y_7729_);
    lean_dec(v___y_7729_);
    lean_dec_ref(v___y_7728_);
    lean_dec(v___y_7727_);
    lean_dec_ref(v___y_7726_);
    return v_res_7731_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(
    mut v_x_7732_: *mut LeanObject,
    mut v_x_7733_: *mut LeanObject,
    mut v_x_7734_: *mut LeanObject,
    mut v_x_7735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7740_: u8 = 0;
    let mut v___x_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7742_: u8 = 0;
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: u8 = 0;
    let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_7736_ = lean_ctor_get(v_x_7732_, 0);
                v_vs_7737_ = lean_ctor_get(v_x_7732_, 1);
                v_isSharedCheck_7761_ = (!lean_is_exclusive(v_x_7732_)) as u8;
                if v_isSharedCheck_7761_ == 0 {
                    v___x_7739_ = v_x_7732_;
                    v_isShared_7740_ = v_isSharedCheck_7761_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_7737_);
                    lean_inc(v_ks_7736_);
                    lean_dec(v_x_7732_);
                    v___x_7739_ = lean_box(0);
                    v_isShared_7740_ = v_isSharedCheck_7761_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7741_ = lean_array_get_size(v_ks_7736_);
                v___x_7742_ = lean_nat_dec_lt(v_x_7733_, v___x_7741_);
                if v___x_7742_ == 0 {
                    lean_dec(v_x_7733_);
                    v___x_7743_ = lean_array_push(v_ks_7736_, v_x_7734_);
                    v___x_7744_ = lean_array_push(v_vs_7737_, v_x_7735_);
                    if v_isShared_7740_ == 0 {
                        lean_ctor_set(v___x_7739_, 1, v___x_7744_);
                        lean_ctor_set(v___x_7739_, 0, v___x_7743_);
                        v___x_7746_ = v___x_7739_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7747_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7747_, 0, v___x_7743_);
                        lean_ctor_set(v_reuseFailAlloc_7747_, 1, v___x_7744_);
                        v___x_7746_ = v_reuseFailAlloc_7747_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_7748_ = lean_array_fget_borrowed(v_ks_7736_, v_x_7733_);
                    v___x_7749_ = l_Lean_instBEqMVarId_beq(v_x_7734_, v_k_x27_7748_);
                    if v___x_7749_ == 0 {
                        if v_isShared_7740_ == 0 {
                            v___x_7751_ = v___x_7739_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7755_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7755_, 0, v_ks_7736_);
                            lean_ctor_set(v_reuseFailAlloc_7755_, 1, v_vs_7737_);
                            v___x_7751_ = v_reuseFailAlloc_7755_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_7756_ = lean_array_fset(v_ks_7736_, v_x_7733_, v_x_7734_);
                        v___x_7757_ = lean_array_fset(v_vs_7737_, v_x_7733_, v_x_7735_);
                        lean_dec(v_x_7733_);
                        if v_isShared_7740_ == 0 {
                            lean_ctor_set(v___x_7739_, 1, v___x_7757_);
                            lean_ctor_set(v___x_7739_, 0, v___x_7756_);
                            v___x_7759_ = v___x_7739_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7760_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7760_, 0, v___x_7756_);
                            lean_ctor_set(v_reuseFailAlloc_7760_, 1, v___x_7757_);
                            v___x_7759_ = v_reuseFailAlloc_7760_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7746_;
            }
            3 => {
                v___x_7752_ = lean_unsigned_to_nat(1);
                v___x_7753_ = lean_nat_add(v_x_7733_, v___x_7752_);
                lean_dec(v_x_7733_);
                v_x_7732_ = v___x_7751_;
                v_x_7733_ = v___x_7753_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_7759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(
    mut v_n_7762_: *mut LeanObject,
    mut v_k_7763_: *mut LeanObject,
    mut v_v_7764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7766_: *mut LeanObject = core::ptr::null_mut();
    v___x_7765_ = lean_unsigned_to_nat(0);
    v___x_7766_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_7762_, v___x_7765_, v_k_7763_, v_v_7764_);
    return v___x_7766_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_7767_: usize = 0;
    let mut v___x_7768_: usize = 0;
    let mut v___x_7769_: usize = 0;
    v___x_7767_ = 5usize;
    v___x_7768_ = 1usize;
    v___x_7769_ = lean_usize_shift_left(v___x_7768_, v___x_7767_);
    return v___x_7769_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_7770_: usize = 0;
    let mut v___x_7771_: usize = 0;
    let mut v___x_7772_: usize = 0;
    v___x_7770_ = 1usize;
    v___x_7771_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
    v___x_7772_ = lean_usize_sub(v___x_7771_, v___x_7770_);
    return v___x_7772_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    v___x_7773_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_7773_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(
    mut v_x_7774_: *mut LeanObject,
    mut v_x_7775_: usize,
    mut v_x_7776_: usize,
    mut v_x_7777_: *mut LeanObject,
    mut v_x_7778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7780_: usize = 0;
    let mut v___x_7781_: usize = 0;
    let mut v___x_7782_: usize = 0;
    let mut v___x_7783_: usize = 0;
    let mut v_j_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: u8 = 0;
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7789_: u8 = 0;
    let mut v_v_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7803_: u8 = 0;
    let mut v___x_7804_: u8 = 0;
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7810_: u8 = 0;
    let mut v_node_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7814_: u8 = 0;
    let mut v___x_7815_: usize = 0;
    let mut v___x_7816_: usize = 0;
    let mut v___x_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7821_: u8 = 0;
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7823_: u8 = 0;
    let mut v_unused_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7829_: u8 = 0;
    let mut v___x_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7834_: u8 = 0;
    let mut v_ks_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: usize = 0;
    let mut v___x_7841_: u8 = 0;
    let mut v___x_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: u8 = 0;
    let mut v_reuseFailAlloc_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7774_) == 0 {
                    v_es_7779_ = lean_ctor_get(v_x_7774_, 0);
                    v___x_7780_ = 5usize;
                    v___x_7781_ = 1usize;
                    v___x_7782_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1);
                    v___x_7783_ = lean_usize_land(v_x_7775_, v___x_7782_);
                    v_j_7784_ = lean_usize_to_nat(v___x_7783_);
                    v___x_7785_ = lean_array_get_size(v_es_7779_);
                    v___x_7786_ = lean_nat_dec_lt(v_j_7784_, v___x_7785_);
                    if v___x_7786_ == 0 {
                        lean_dec(v_j_7784_);
                        lean_dec(v_x_7778_);
                        lean_dec(v_x_7777_);
                        return v_x_7774_;
                    } else {
                        lean_inc_ref(v_es_7779_);
                        v_isSharedCheck_7823_ = (!lean_is_exclusive(v_x_7774_)) as u8;
                        if v_isSharedCheck_7823_ == 0 {
                            v_unused_7824_ = lean_ctor_get(v_x_7774_, 0);
                            lean_dec(v_unused_7824_);
                            v___x_7788_ = v_x_7774_;
                            v_isShared_7789_ = v_isSharedCheck_7823_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_7774_);
                            v___x_7788_ = lean_box(0);
                            v_isShared_7789_ = v_isSharedCheck_7823_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_7825_ = lean_ctor_get(v_x_7774_, 0);
                    v_vs_7826_ = lean_ctor_get(v_x_7774_, 1);
                    v_isSharedCheck_7846_ = (!lean_is_exclusive(v_x_7774_)) as u8;
                    if v_isSharedCheck_7846_ == 0 {
                        v___x_7828_ = v_x_7774_;
                        v_isShared_7829_ = v_isSharedCheck_7846_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_7826_);
                        lean_inc(v_ks_7825_);
                        lean_dec(v_x_7774_);
                        v___x_7828_ = lean_box(0);
                        v_isShared_7829_ = v_isSharedCheck_7846_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_7790_ = lean_array_fget(v_es_7779_, v_j_7784_);
                v___x_7791_ = lean_box(0);
                v_xs_x27_7792_ = lean_array_fset(v_es_7779_, v_j_7784_, v___x_7791_);
                match lean_obj_tag(v_v_7790_) {
                    0 => {
                        v_key_7799_ = lean_ctor_get(v_v_7790_, 0);
                        v_val_7800_ = lean_ctor_get(v_v_7790_, 1);
                        v_isSharedCheck_7810_ = (!lean_is_exclusive(v_v_7790_)) as u8;
                        if v_isSharedCheck_7810_ == 0 {
                            v___x_7802_ = v_v_7790_;
                            v_isShared_7803_ = v_isSharedCheck_7810_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_7800_);
                            lean_inc(v_key_7799_);
                            lean_dec(v_v_7790_);
                            v___x_7802_ = lean_box(0);
                            v_isShared_7803_ = v_isSharedCheck_7810_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_7811_ = lean_ctor_get(v_v_7790_, 0);
                        v_isSharedCheck_7821_ = (!lean_is_exclusive(v_v_7790_)) as u8;
                        if v_isSharedCheck_7821_ == 0 {
                            v___x_7813_ = v_v_7790_;
                            v_isShared_7814_ = v_isSharedCheck_7821_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_7811_);
                            lean_dec(v_v_7790_);
                            v___x_7813_ = lean_box(0);
                            v_isShared_7814_ = v_isSharedCheck_7821_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_7822_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_7822_, 0, v_x_7777_);
                        lean_ctor_set(v___x_7822_, 1, v_x_7778_);
                        v___y_7794_ = v___x_7822_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7795_ = lean_array_fset(v_xs_x27_7792_, v_j_7784_, v___y_7794_);
                lean_dec(v_j_7784_);
                if v_isShared_7789_ == 0 {
                    lean_ctor_set(v___x_7788_, 0, v___x_7795_);
                    v___x_7797_ = v___x_7788_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7798_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7798_, 0, v___x_7795_);
                    v___x_7797_ = v_reuseFailAlloc_7798_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7797_;
            }
            4 => {
                v___x_7804_ = l_Lean_instBEqMVarId_beq(v_x_7777_, v_key_7799_);
                if v___x_7804_ == 0 {
                    lean_del_object(v___x_7802_);
                    v___x_7805_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_7799_,
                        v_val_7800_,
                        v_x_7777_,
                        v_x_7778_,
                    );
                    v___x_7806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7806_, 0, v___x_7805_);
                    v___y_7794_ = v___x_7806_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_7800_);
                    lean_dec(v_key_7799_);
                    if v_isShared_7803_ == 0 {
                        lean_ctor_set(v___x_7802_, 1, v_x_7778_);
                        lean_ctor_set(v___x_7802_, 0, v_x_7777_);
                        v___x_7808_ = v___x_7802_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7809_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7809_, 0, v_x_7777_);
                        lean_ctor_set(v_reuseFailAlloc_7809_, 1, v_x_7778_);
                        v___x_7808_ = v_reuseFailAlloc_7809_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_7794_ = v___x_7808_;
                state = 2;
                continue;
            }
            6 => {
                v___x_7815_ = lean_usize_shift_right(v_x_7775_, v___x_7780_);
                v___x_7816_ = lean_usize_add(v_x_7776_, v___x_7781_);
                v___x_7817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_7811_, v___x_7815_, v___x_7816_, v_x_7777_, v_x_7778_);
                if v_isShared_7814_ == 0 {
                    lean_ctor_set(v___x_7813_, 0, v___x_7817_);
                    v___x_7819_ = v___x_7813_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7820_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7820_, 0, v___x_7817_);
                    v___x_7819_ = v_reuseFailAlloc_7820_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_7794_ = v___x_7819_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_7829_ == 0 {
                    v___x_7831_ = v___x_7828_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7845_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7845_, 0, v_ks_7825_);
                    lean_ctor_set(v_reuseFailAlloc_7845_, 1, v_vs_7826_);
                    v___x_7831_ = v_reuseFailAlloc_7845_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_7832_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_7831_, v_x_7777_, v_x_7778_);
                v___x_7840_ = 7usize;
                v___x_7841_ = lean_usize_dec_le(v___x_7840_, v_x_7776_);
                if v___x_7841_ == 0 {
                    v___x_7842_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_7832_);
                    v___x_7843_ = lean_unsigned_to_nat(4);
                    v___x_7844_ = lean_nat_dec_lt(v___x_7842_, v___x_7843_);
                    lean_dec(v___x_7842_);
                    v___y_7834_ = v___x_7844_;
                    state = 10;
                    continue;
                } else {
                    v___y_7834_ = v___x_7841_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_7834_ == 0 {
                    v_ks_7835_ = lean_ctor_get(v_newNode_7832_, 0);
                    lean_inc_ref(v_ks_7835_);
                    v_vs_7836_ = lean_ctor_get(v_newNode_7832_, 1);
                    lean_inc_ref(v_vs_7836_);
                    lean_dec_ref(v_newNode_7832_);
                    v___x_7837_ = lean_unsigned_to_nat(0);
                    v___x_7838_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2);
                    v___x_7839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_7776_, v_ks_7835_, v_vs_7836_, v___x_7837_, v___x_7838_);
                    lean_dec_ref(v_vs_7836_);
                    lean_dec_ref(v_ks_7835_);
                    return v___x_7839_;
                } else {
                    return v_newNode_7832_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(
    mut v_depth_7847_: usize,
    mut v_keys_7848_: *mut LeanObject,
    mut v_vals_7849_: *mut LeanObject,
    mut v_i_7850_: *mut LeanObject,
    mut v_entries_7851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: u8 = 0;
    let mut v_k_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: u64 = 0;
    let mut v_h_7857_: usize = 0;
    let mut v___x_7858_: usize = 0;
    let mut v___x_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: usize = 0;
    let mut v___x_7861_: usize = 0;
    let mut v___x_7862_: usize = 0;
    let mut v_h_7863_: usize = 0;
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7852_ = lean_array_get_size(v_keys_7848_);
                v___x_7853_ = lean_nat_dec_lt(v_i_7850_, v___x_7852_);
                if v___x_7853_ == 0 {
                    lean_dec(v_i_7850_);
                    return v_entries_7851_;
                } else {
                    v_k_7854_ = lean_array_fget_borrowed(v_keys_7848_, v_i_7850_);
                    v_v_7855_ = lean_array_fget_borrowed(v_vals_7849_, v_i_7850_);
                    v___x_7856_ = l_Lean_instHashableMVarId_hash(v_k_7854_);
                    v_h_7857_ = lean_uint64_to_usize(v___x_7856_);
                    v___x_7858_ = 5usize;
                    v___x_7859_ = lean_unsigned_to_nat(1);
                    v___x_7860_ = 1usize;
                    v___x_7861_ = lean_usize_sub(v_depth_7847_, v___x_7860_);
                    v___x_7862_ = lean_usize_mul(v___x_7858_, v___x_7861_);
                    v_h_7863_ = lean_usize_shift_right(v_h_7857_, v___x_7862_);
                    v___x_7864_ = lean_nat_add(v_i_7850_, v___x_7859_);
                    lean_dec(v_i_7850_);
                    lean_inc(v_v_7855_);
                    lean_inc(v_k_7854_);
                    v___x_7865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_7851_, v_h_7863_, v_depth_7847_, v_k_7854_, v_v_7855_);
                    v_i_7850_ = v___x_7864_;
                    v_entries_7851_ = v___x_7865_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_depth_7867_: *mut LeanObject,
    mut v_keys_7868_: *mut LeanObject,
    mut v_vals_7869_: *mut LeanObject,
    mut v_i_7870_: *mut LeanObject,
    mut v_entries_7871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_7872_: usize = 0;
    let mut v_res_7873_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_7872_ = lean_unbox_usize(v_depth_7867_);
    lean_dec(v_depth_7867_);
    v_res_7873_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_7872_, v_keys_7868_, v_vals_7869_, v_i_7870_, v_entries_7871_);
    lean_dec_ref(v_vals_7869_);
    lean_dec_ref(v_keys_7868_);
    return v_res_7873_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_x_7874_: *mut LeanObject,
    mut v_x_7875_: *mut LeanObject,
    mut v_x_7876_: *mut LeanObject,
    mut v_x_7877_: *mut LeanObject,
    mut v_x_7878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4166__boxed_7879_: usize = 0;
    let mut v_x_4167__boxed_7880_: usize = 0;
    let mut v_res_7881_: *mut LeanObject = core::ptr::null_mut();
    v_x_4166__boxed_7879_ = lean_unbox_usize(v_x_7875_);
    lean_dec(v_x_7875_);
    v_x_4167__boxed_7880_ = lean_unbox_usize(v_x_7876_);
    lean_dec(v_x_7876_);
    v_res_7881_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_7874_, v_x_4166__boxed_7879_, v_x_4167__boxed_7880_, v_x_7877_, v_x_7878_);
    return v_res_7881_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(
    mut v_x_7882_: *mut LeanObject,
    mut v_x_7883_: *mut LeanObject,
    mut v_x_7884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7885_: u64 = 0;
    let mut v___x_7886_: usize = 0;
    let mut v___x_7887_: usize = 0;
    let mut v___x_7888_: *mut LeanObject = core::ptr::null_mut();
    v___x_7885_ = l_Lean_instHashableMVarId_hash(v_x_7883_);
    v___x_7886_ = lean_uint64_to_usize(v___x_7885_);
    v___x_7887_ = 1usize;
    v___x_7888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_7882_, v___x_7886_, v___x_7887_, v_x_7883_, v_x_7884_);
    return v___x_7888_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(
    mut v_mvarId_7889_: *mut LeanObject,
    mut v_val_7890_: *mut LeanObject,
    mut v___y_7891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_7897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7901_: u8 = 0;
    let mut v_depth_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_7903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_7905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_7907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_7911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7914_: u8 = 0;
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7925_: u8 = 0;
    let mut v_isSharedCheck_7926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7893_ = lean_st_ref_take(v___y_7891_);
                v_mctx_7894_ = lean_ctor_get(v___x_7893_, 0);
                v_cache_7895_ = lean_ctor_get(v___x_7893_, 1);
                v_zetaDeltaFVarIds_7896_ = lean_ctor_get(v___x_7893_, 2);
                v_postponed_7897_ = lean_ctor_get(v___x_7893_, 3);
                v_diag_7898_ = lean_ctor_get(v___x_7893_, 4);
                v_isSharedCheck_7926_ = (!lean_is_exclusive(v___x_7893_)) as u8;
                if v_isSharedCheck_7926_ == 0 {
                    v___x_7900_ = v___x_7893_;
                    v_isShared_7901_ = v_isSharedCheck_7926_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_7898_);
                    lean_inc(v_postponed_7897_);
                    lean_inc(v_zetaDeltaFVarIds_7896_);
                    lean_inc(v_cache_7895_);
                    lean_inc(v_mctx_7894_);
                    lean_dec(v___x_7893_);
                    v___x_7900_ = lean_box(0);
                    v_isShared_7901_ = v_isSharedCheck_7926_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_7902_ = lean_ctor_get(v_mctx_7894_, 0);
                v_levelAssignDepth_7903_ = lean_ctor_get(v_mctx_7894_, 1);
                v_lmvarCounter_7904_ = lean_ctor_get(v_mctx_7894_, 2);
                v_mvarCounter_7905_ = lean_ctor_get(v_mctx_7894_, 3);
                v_lDecls_7906_ = lean_ctor_get(v_mctx_7894_, 4);
                v_decls_7907_ = lean_ctor_get(v_mctx_7894_, 5);
                v_userNames_7908_ = lean_ctor_get(v_mctx_7894_, 6);
                v_lAssignment_7909_ = lean_ctor_get(v_mctx_7894_, 7);
                v_eAssignment_7910_ = lean_ctor_get(v_mctx_7894_, 8);
                v_dAssignment_7911_ = lean_ctor_get(v_mctx_7894_, 9);
                v_isSharedCheck_7925_ = (!lean_is_exclusive(v_mctx_7894_)) as u8;
                if v_isSharedCheck_7925_ == 0 {
                    v___x_7913_ = v_mctx_7894_;
                    v_isShared_7914_ = v_isSharedCheck_7925_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_7911_);
                    lean_inc(v_eAssignment_7910_);
                    lean_inc(v_lAssignment_7909_);
                    lean_inc(v_userNames_7908_);
                    lean_inc(v_decls_7907_);
                    lean_inc(v_lDecls_7906_);
                    lean_inc(v_mvarCounter_7905_);
                    lean_inc(v_lmvarCounter_7904_);
                    lean_inc(v_levelAssignDepth_7903_);
                    lean_inc(v_depth_7902_);
                    lean_dec(v_mctx_7894_);
                    v___x_7913_ = lean_box(0);
                    v_isShared_7914_ = v_isSharedCheck_7925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7915_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_7910_, v_mvarId_7889_, v_val_7890_);
                if v_isShared_7914_ == 0 {
                    lean_ctor_set(v___x_7913_, 8, v___x_7915_);
                    v___x_7917_ = v___x_7913_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7924_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 0, v_depth_7902_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 1, v_levelAssignDepth_7903_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 2, v_lmvarCounter_7904_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 3, v_mvarCounter_7905_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 4, v_lDecls_7906_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 5, v_decls_7907_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 6, v_userNames_7908_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 7, v_lAssignment_7909_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 8, v___x_7915_);
                    lean_ctor_set(v_reuseFailAlloc_7924_, 9, v_dAssignment_7911_);
                    v___x_7917_ = v_reuseFailAlloc_7924_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7901_ == 0 {
                    lean_ctor_set(v___x_7900_, 0, v___x_7917_);
                    v___x_7919_ = v___x_7900_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7923_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7923_, 0, v___x_7917_);
                    lean_ctor_set(v_reuseFailAlloc_7923_, 1, v_cache_7895_);
                    lean_ctor_set(v_reuseFailAlloc_7923_, 2, v_zetaDeltaFVarIds_7896_);
                    lean_ctor_set(v_reuseFailAlloc_7923_, 3, v_postponed_7897_);
                    lean_ctor_set(v_reuseFailAlloc_7923_, 4, v_diag_7898_);
                    v___x_7919_ = v_reuseFailAlloc_7923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7920_ = lean_st_ref_set(v___y_7891_, v___x_7919_);
                v___x_7921_ = lean_box(0);
                v___x_7922_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7922_, 0, v___x_7921_);
                return v___x_7922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(
    mut v_mvarId_7927_: *mut LeanObject,
    mut v_val_7928_: *mut LeanObject,
    mut v___y_7929_: *mut LeanObject,
    mut v___y_7930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7931_: *mut LeanObject = core::ptr::null_mut();
    v_res_7931_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_7927_, v_val_7928_, v___y_7929_);
    lean_dec(v___y_7929_);
    return v_res_7931_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(
    mut v___x_7940_: *mut LeanObject,
    mut v_as_7941_: *mut LeanObject,
    mut v_sz_7942_: usize,
    mut v_i_7943_: usize,
    mut v_b_7944_: *mut LeanObject,
    mut v___y_7945_: *mut LeanObject,
    mut v___y_7946_: *mut LeanObject,
    mut v___y_7947_: *mut LeanObject,
    mut v___y_7948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: usize = 0;
    let mut v___x_7953_: usize = 0;
    let mut v___x_7955_: u8 = 0;
    let mut v___x_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7960_: u8 = 0;
    let mut v_a_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7970_: u8 = 0;
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7974_: u8 = 0;
    let mut v_a_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7978_: u8 = 0;
    let mut v___x_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7982_: u8 = 0;
    let mut v_lhs_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8013_: u8 = 0;
    let mut v___x_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8017_: u8 = 0;
    let mut v_a_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8021_: u8 = 0;
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8025_: u8 = 0;
    let mut v_a_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8029_: u8 = 0;
    let mut v___x_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8033_: u8 = 0;
    let mut v_a_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8037_: u8 = 0;
    let mut v___x_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8041_: u8 = 0;
    let mut v_a_8042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8045_: u8 = 0;
    let mut v___x_8047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8049_: u8 = 0;
    let mut v_a_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8053_: u8 = 0;
    let mut v___x_8055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7955_ = lean_usize_dec_lt(v_i_7943_, v_sz_7942_);
                if v___x_7955_ == 0 {
                    v___x_7956_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7956_, 0, v_b_7944_);
                    return v___x_7956_;
                } else {
                    v_fst_7957_ = lean_ctor_get(v_b_7944_, 0);
                    lean_inc(v_fst_7957_);
                    v_snd_7958_ = lean_ctor_get(v_b_7944_, 1);
                    lean_inc(v_snd_7958_);
                    lean_dec_ref(v_b_7944_);
                    v___x_7959_ = lean_unsigned_to_nat(0);
                    v___x_7960_ = lean_nat_dec_eq(v___x_7940_, v___x_7959_);
                    v_a_7961_ = lean_array_uget_borrowed(v_as_7941_, v_i_7943_);
                    if lean_obj_tag(v_a_7961_) == 0 {
                        v_fvarId_7962_ = lean_ctor_get(v_a_7961_, 0);
                        v___x_7963_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(
                            v_snd_7958_,
                            v_fvarId_7962_,
                        );
                        v___x_7964_ = l_Lean_Meta_substCore(
                            v_fst_7957_,
                            v___x_7963_,
                            v___x_7955_,
                            v_snd_7958_,
                            v___x_7955_,
                            v___x_7960_,
                            v___y_7945_,
                            v___y_7946_,
                            v___y_7947_,
                            v___y_7948_,
                        );
                        if lean_obj_tag(v___x_7964_) == 0 {
                            v_a_7965_ = lean_ctor_get(v___x_7964_, 0);
                            lean_inc(v_a_7965_);
                            lean_dec_ref_known(v___x_7964_, 1);
                            v_fst_7966_ = lean_ctor_get(v_a_7965_, 0);
                            v_snd_7967_ = lean_ctor_get(v_a_7965_, 1);
                            v_isSharedCheck_7974_ = (!lean_is_exclusive(v_a_7965_)) as u8;
                            if v_isSharedCheck_7974_ == 0 {
                                v___x_7969_ = v_a_7965_;
                                v_isShared_7970_ = v_isSharedCheck_7974_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_snd_7967_);
                                lean_inc(v_fst_7966_);
                                lean_dec(v_a_7965_);
                                v___x_7969_ = lean_box(0);
                                v_isShared_7970_ = v_isSharedCheck_7974_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_7975_ = lean_ctor_get(v___x_7964_, 0);
                            v_isSharedCheck_7982_ = (!lean_is_exclusive(v___x_7964_)) as u8;
                            if v_isSharedCheck_7982_ == 0 {
                                v___x_7977_ = v___x_7964_;
                                v_isShared_7978_ = v_isSharedCheck_7982_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_7975_);
                                lean_dec(v___x_7964_);
                                v___x_7977_ = lean_box(0);
                                v_isShared_7978_ = v_isSharedCheck_7982_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_lhs_7983_ = lean_ctor_get(v_a_7961_, 0);
                        v_rhs_7984_ = lean_ctor_get(v_a_7961_, 1);
                        v___x_7985_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(
                            v_snd_7958_,
                            v_lhs_7983_,
                        );
                        v___x_7986_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(
                            v_snd_7958_,
                            v_rhs_7984_,
                        );
                        v___x_7987_ = l_Lean_mkFVar(v___x_7985_);
                        v___x_7988_ = l_Lean_mkFVar(v___x_7986_);
                        lean_inc_ref(v___x_7988_);
                        lean_inc_ref(v___x_7987_);
                        v___x_7989_ = lean_alloc_closure(
                            l_Lean_Meta_mkEq___boxed as *mut core::ffi::c_void,
                            7,
                            2,
                        );
                        lean_closure_set(v___x_7989_, 0, v___x_7987_);
                        lean_closure_set(v___x_7989_, 1, v___x_7988_);
                        lean_inc(v_fst_7957_);
                        v___x_7990_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_7957_, v___x_7989_, v___y_7945_, v___y_7946_, v___y_7947_, v___y_7948_);
                        if lean_obj_tag(v___x_7990_) == 0 {
                            v_a_7991_ = lean_ctor_get(v___x_7990_, 0);
                            lean_inc(v_a_7991_);
                            lean_dec_ref_known(v___x_7990_, 1);
                            v___x_7992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2;
                            v___x_7993_ = lean_unsigned_to_nat(2);
                            v___x_7994_ = lean_mk_empty_array_with_capacity(v___x_7993_);
                            v___x_7995_ = lean_array_push(v___x_7994_, v___x_7987_);
                            v___x_7996_ = lean_array_push(v___x_7995_, v___x_7988_);
                            v___x_7997_ = lean_alloc_closure(
                                l_Lean_Meta_mkAppM___boxed as *mut core::ffi::c_void,
                                7,
                                2,
                            );
                            lean_closure_set(v___x_7997_, 0, v___x_7992_);
                            lean_closure_set(v___x_7997_, 1, v___x_7996_);
                            lean_inc(v_fst_7957_);
                            v___x_7998_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_7957_, v___x_7997_, v___y_7945_, v___y_7946_, v___y_7947_, v___y_7948_);
                            if lean_obj_tag(v___x_7998_) == 0 {
                                v_a_7999_ = lean_ctor_get(v___x_7998_, 0);
                                lean_inc(v_a_7999_);
                                lean_dec_ref_known(v___x_7998_, 1);
                                v___x_8000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4;
                                v___x_8001_ = l_Lean_MVarId_assert(
                                    v_fst_7957_,
                                    v___x_8000_,
                                    v_a_7991_,
                                    v_a_7999_,
                                    v___y_7945_,
                                    v___y_7946_,
                                    v___y_7947_,
                                    v___y_7948_,
                                );
                                if lean_obj_tag(v___x_8001_) == 0 {
                                    v_a_8002_ = lean_ctor_get(v___x_8001_, 0);
                                    lean_inc(v_a_8002_);
                                    lean_dec_ref_known(v___x_8001_, 1);
                                    v___x_8003_ = l_Lean_Meta_intro1Core(
                                        v_a_8002_,
                                        v___x_7960_,
                                        v___y_7945_,
                                        v___y_7946_,
                                        v___y_7947_,
                                        v___y_7948_,
                                    );
                                    if lean_obj_tag(v___x_8003_) == 0 {
                                        v_a_8004_ = lean_ctor_get(v___x_8003_, 0);
                                        lean_inc(v_a_8004_);
                                        lean_dec_ref_known(v___x_8003_, 1);
                                        v_fst_8005_ = lean_ctor_get(v_a_8004_, 0);
                                        lean_inc(v_fst_8005_);
                                        v_snd_8006_ = lean_ctor_get(v_a_8004_, 1);
                                        lean_inc(v_snd_8006_);
                                        lean_dec(v_a_8004_);
                                        v___x_8007_ = l_Lean_Meta_substCore(
                                            v_snd_8006_,
                                            v_fst_8005_,
                                            v___x_7955_,
                                            v_snd_7958_,
                                            v___x_7955_,
                                            v___x_7960_,
                                            v___y_7945_,
                                            v___y_7946_,
                                            v___y_7947_,
                                            v___y_7948_,
                                        );
                                        if lean_obj_tag(v___x_8007_) == 0 {
                                            v_a_8008_ = lean_ctor_get(v___x_8007_, 0);
                                            lean_inc(v_a_8008_);
                                            lean_dec_ref_known(v___x_8007_, 1);
                                            v_fst_8009_ = lean_ctor_get(v_a_8008_, 0);
                                            v_snd_8010_ = lean_ctor_get(v_a_8008_, 1);
                                            v_isSharedCheck_8017_ =
                                                (!lean_is_exclusive(v_a_8008_)) as u8;
                                            if v_isSharedCheck_8017_ == 0 {
                                                v___x_8012_ = v_a_8008_;
                                                v_isShared_8013_ = v_isSharedCheck_8017_;
                                                state = 6;
                                                continue;
                                            } else {
                                                lean_inc(v_snd_8010_);
                                                lean_inc(v_fst_8009_);
                                                lean_dec(v_a_8008_);
                                                v___x_8012_ = lean_box(0);
                                                v_isShared_8013_ = v_isSharedCheck_8017_;
                                                state = 6;
                                                continue;
                                            }
                                        } else {
                                            v_a_8018_ = lean_ctor_get(v___x_8007_, 0);
                                            v_isSharedCheck_8025_ =
                                                (!lean_is_exclusive(v___x_8007_)) as u8;
                                            if v_isSharedCheck_8025_ == 0 {
                                                v___x_8020_ = v___x_8007_;
                                                v_isShared_8021_ = v_isSharedCheck_8025_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_inc(v_a_8018_);
                                                lean_dec(v___x_8007_);
                                                v___x_8020_ = lean_box(0);
                                                v_isShared_8021_ = v_isSharedCheck_8025_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_snd_7958_);
                                        v_a_8026_ = lean_ctor_get(v___x_8003_, 0);
                                        v_isSharedCheck_8033_ =
                                            (!lean_is_exclusive(v___x_8003_)) as u8;
                                        if v_isSharedCheck_8033_ == 0 {
                                            v___x_8028_ = v___x_8003_;
                                            v_isShared_8029_ = v_isSharedCheck_8033_;
                                            state = 10;
                                            continue;
                                        } else {
                                            lean_inc(v_a_8026_);
                                            lean_dec(v___x_8003_);
                                            v___x_8028_ = lean_box(0);
                                            v_isShared_8029_ = v_isSharedCheck_8033_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_snd_7958_);
                                    v_a_8034_ = lean_ctor_get(v___x_8001_, 0);
                                    v_isSharedCheck_8041_ = (!lean_is_exclusive(v___x_8001_)) as u8;
                                    if v_isSharedCheck_8041_ == 0 {
                                        v___x_8036_ = v___x_8001_;
                                        v_isShared_8037_ = v_isSharedCheck_8041_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_8034_);
                                        lean_dec(v___x_8001_);
                                        v___x_8036_ = lean_box(0);
                                        v_isShared_8037_ = v_isSharedCheck_8041_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_7991_);
                                lean_dec(v_snd_7958_);
                                lean_dec(v_fst_7957_);
                                v_a_8042_ = lean_ctor_get(v___x_7998_, 0);
                                v_isSharedCheck_8049_ = (!lean_is_exclusive(v___x_7998_)) as u8;
                                if v_isSharedCheck_8049_ == 0 {
                                    v___x_8044_ = v___x_7998_;
                                    v_isShared_8045_ = v_isSharedCheck_8049_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_8042_);
                                    lean_dec(v___x_7998_);
                                    v___x_8044_ = lean_box(0);
                                    v_isShared_8045_ = v_isSharedCheck_8049_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_7988_);
                            lean_dec_ref(v___x_7987_);
                            lean_dec(v_snd_7958_);
                            lean_dec(v_fst_7957_);
                            v_a_8050_ = lean_ctor_get(v___x_7990_, 0);
                            v_isSharedCheck_8057_ = (!lean_is_exclusive(v___x_7990_)) as u8;
                            if v_isSharedCheck_8057_ == 0 {
                                v___x_8052_ = v___x_7990_;
                                v_isShared_8053_ = v_isSharedCheck_8057_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_8050_);
                                lean_dec(v___x_7990_);
                                v___x_8052_ = lean_box(0);
                                v_isShared_8053_ = v_isSharedCheck_8057_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_7952_ = 1usize;
                v___x_7953_ = lean_usize_add(v_i_7943_, v___x_7952_);
                v_i_7943_ = v___x_7953_;
                v_b_7944_ = v_a_7951_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_7970_ == 0 {
                    lean_ctor_set(v___x_7969_, 1, v_fst_7966_);
                    lean_ctor_set(v___x_7969_, 0, v_snd_7967_);
                    v___x_7972_ = v___x_7969_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7973_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7973_, 0, v_snd_7967_);
                    lean_ctor_set(v_reuseFailAlloc_7973_, 1, v_fst_7966_);
                    v___x_7972_ = v_reuseFailAlloc_7973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_7951_ = v___x_7972_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_7978_ == 0 {
                    v___x_7980_ = v___x_7977_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7981_, 0, v_a_7975_);
                    v___x_7980_ = v_reuseFailAlloc_7981_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7980_;
            }
            6 => {
                if v_isShared_8013_ == 0 {
                    lean_ctor_set(v___x_8012_, 1, v_fst_8009_);
                    lean_ctor_set(v___x_8012_, 0, v_snd_8010_);
                    v___x_8015_ = v___x_8012_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8016_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 0, v_snd_8010_);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 1, v_fst_8009_);
                    v___x_8015_ = v_reuseFailAlloc_8016_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_7951_ = v___x_8015_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_8021_ == 0 {
                    v___x_8023_ = v___x_8020_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8024_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8024_, 0, v_a_8018_);
                    v___x_8023_ = v_reuseFailAlloc_8024_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8023_;
            }
            10 => {
                if v_isShared_8029_ == 0 {
                    v___x_8031_ = v___x_8028_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8032_, 0, v_a_8026_);
                    v___x_8031_ = v_reuseFailAlloc_8032_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8031_;
            }
            12 => {
                if v_isShared_8037_ == 0 {
                    v___x_8039_ = v___x_8036_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8040_, 0, v_a_8034_);
                    v___x_8039_ = v_reuseFailAlloc_8040_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8039_;
            }
            14 => {
                if v_isShared_8045_ == 0 {
                    v___x_8047_ = v___x_8044_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8048_, 0, v_a_8042_);
                    v___x_8047_ = v_reuseFailAlloc_8048_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8047_;
            }
            16 => {
                if v_isShared_8053_ == 0 {
                    v___x_8055_ = v___x_8052_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_8056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8056_, 0, v_a_8050_);
                    v___x_8055_ = v_reuseFailAlloc_8056_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_8055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(
    mut v___x_8058_: *mut LeanObject,
    mut v_as_8059_: *mut LeanObject,
    mut v_sz_8060_: *mut LeanObject,
    mut v_i_8061_: *mut LeanObject,
    mut v_b_8062_: *mut LeanObject,
    mut v___y_8063_: *mut LeanObject,
    mut v___y_8064_: *mut LeanObject,
    mut v___y_8065_: *mut LeanObject,
    mut v___y_8066_: *mut LeanObject,
    mut v___y_8067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8068_: usize = 0;
    let mut v_i_boxed_8069_: usize = 0;
    let mut v_res_8070_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8068_ = lean_unbox_usize(v_sz_8060_);
    lean_dec(v_sz_8060_);
    v_i_boxed_8069_ = lean_unbox_usize(v_i_8061_);
    lean_dec(v_i_8061_);
    v_res_8070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_8058_, v_as_8059_, v_sz_boxed_8068_, v_i_boxed_8069_, v_b_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v___y_8066_);
    lean_dec(v___y_8066_);
    lean_dec_ref(v___y_8065_);
    lean_dec(v___y_8064_);
    lean_dec_ref(v___y_8063_);
    lean_dec_ref(v_as_8059_);
    lean_dec(v___x_8058_);
    return v_res_8070_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(
    mut v_eqs_8071_: *mut LeanObject,
    mut v_as_8072_: *mut LeanObject,
    mut v_i_8073_: usize,
    mut v_stop_8074_: usize,
    mut v_b_8075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8078_: usize = 0;
    let mut v___x_8079_: usize = 0;
    let mut v___x_8081_: u8 = 0;
    let mut v___x_8082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8081_ = lean_usize_dec_eq(v_i_8073_, v_stop_8074_);
                if v___x_8081_ == 0 {
                    v___x_8082_ = lean_box(0);
                    v___x_8083_ = lean_array_uget_borrowed(v_as_8072_, v_i_8073_);
                    v___x_8084_ = lean_array_get_borrowed(v___x_8082_, v_eqs_8071_, v___x_8083_);
                    if lean_obj_tag(v___x_8084_) == 0 {
                        v___y_8077_ = v_b_8075_;
                        state = 1;
                        continue;
                    } else {
                        v_val_8085_ = lean_ctor_get(v___x_8084_, 0);
                        lean_inc(v_val_8085_);
                        v___x_8086_ = lean_array_push(v_b_8075_, v_val_8085_);
                        v___y_8077_ = v___x_8086_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_8075_;
                }
            }
            1 => {
                v___x_8078_ = 1usize;
                v___x_8079_ = lean_usize_add(v_i_8073_, v___x_8078_);
                v_i_8073_ = v___x_8079_;
                v_b_8075_ = v___y_8077_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(
    mut v_eqs_8087_: *mut LeanObject,
    mut v_as_8088_: *mut LeanObject,
    mut v_i_8089_: *mut LeanObject,
    mut v_stop_8090_: *mut LeanObject,
    mut v_b_8091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8092_: usize = 0;
    let mut v_stop_boxed_8093_: usize = 0;
    let mut v_res_8094_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8092_ = lean_unbox_usize(v_i_8089_);
    lean_dec(v_i_8089_);
    v_stop_boxed_8093_ = lean_unbox_usize(v_stop_8090_);
    lean_dec(v_stop_8090_);
    v_res_8094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_8087_, v_as_8088_, v_i_boxed_8092_, v_stop_boxed_8093_, v_b_8091_);
    lean_dec_ref(v_as_8088_);
    lean_dec_ref(v_eqs_8087_);
    return v_res_8094_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(
    mut v_eqs_8097_: *mut LeanObject,
    mut v_as_8098_: *mut LeanObject,
    mut v_start_8099_: *mut LeanObject,
    mut v_stop_8100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8102_: u8 = 0;
    v___x_8101_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0;
    v___x_8102_ = lean_nat_dec_lt(v_start_8099_, v_stop_8100_);
    if v___x_8102_ == 0 {
        return v___x_8101_;
    } else {
        let mut v___x_8103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8104_: u8 = 0;
        v___x_8103_ = lean_array_get_size(v_as_8098_);
        v___x_8104_ = lean_nat_dec_le(v_stop_8100_, v___x_8103_);
        if v___x_8104_ == 0 {
            let mut v___x_8105_: u8 = 0;
            v___x_8105_ = lean_nat_dec_lt(v_start_8099_, v___x_8103_);
            if v___x_8105_ == 0 {
                return v___x_8101_;
            } else {
                let mut v___x_8106_: usize = 0;
                let mut v___x_8107_: usize = 0;
                let mut v___x_8108_: *mut LeanObject = core::ptr::null_mut();
                v___x_8106_ = lean_usize_of_nat(v_start_8099_);
                v___x_8107_ = lean_usize_of_nat(v___x_8103_);
                v___x_8108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_8097_, v_as_8098_, v___x_8106_, v___x_8107_, v___x_8101_);
                return v___x_8108_;
            }
        } else {
            let mut v___x_8109_: usize = 0;
            let mut v___x_8110_: usize = 0;
            let mut v___x_8111_: *mut LeanObject = core::ptr::null_mut();
            v___x_8109_ = lean_usize_of_nat(v_start_8099_);
            v___x_8110_ = lean_usize_of_nat(v_stop_8100_);
            v___x_8111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_8097_, v_as_8098_, v___x_8109_, v___x_8110_, v___x_8101_);
            return v___x_8111_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(
    mut v_eqs_8112_: *mut LeanObject,
    mut v_as_8113_: *mut LeanObject,
    mut v_start_8114_: *mut LeanObject,
    mut v_stop_8115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8116_: *mut LeanObject = core::ptr::null_mut();
    v_res_8116_ =
        l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(
            v_eqs_8112_,
            v_as_8113_,
            v_start_8114_,
            v_stop_8115_,
        );
    lean_dec(v_stop_8115_);
    lean_dec(v_start_8114_);
    lean_dec_ref(v_as_8113_);
    lean_dec_ref(v_eqs_8112_);
    return v_res_8116_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(
    mut v_fvarId_8117_: *mut LeanObject,
    mut v_type_8118_: *mut LeanObject,
    mut v_deps_8119_: *mut LeanObject,
    mut v_eqs_8120_: *mut LeanObject,
    mut v_a_8121_: *mut LeanObject,
    mut v_a_8122_: *mut LeanObject,
    mut v_a_8123_: *mut LeanObject,
    mut v_a_8124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqs_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8130_: u8 = 0;
    let mut v___x_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8132_: u8 = 0;
    let mut v___x_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8139_: usize = 0;
    let mut v___x_8140_: usize = 0;
    let mut v___x_8141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8152_: u8 = 0;
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8156_: u8 = 0;
    let mut v___x_8157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8158_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8126_ = lean_unsigned_to_nat(0);
                v___x_8127_ = lean_array_get_size(v_deps_8119_);
                v_eqs_8128_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_8120_, v_deps_8119_, v___x_8126_, v___x_8127_);
                v___x_8129_ = lean_array_get_size(v_eqs_8128_);
                v___x_8130_ = lean_nat_dec_eq(v___x_8129_, v___x_8126_);
                if v___x_8130_ == 0 {
                    v___x_8131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8131_, 0, v_type_8118_);
                    v___x_8132_ = 0;
                    v___x_8133_ = lean_box(0);
                    v___x_8134_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_8131_,
                        v___x_8132_,
                        v___x_8133_,
                        v_a_8121_,
                        v_a_8122_,
                        v_a_8123_,
                        v_a_8124_,
                    );
                    if lean_obj_tag(v___x_8134_) == 0 {
                        v_a_8135_ = lean_ctor_get(v___x_8134_, 0);
                        lean_inc(v_a_8135_);
                        lean_dec_ref_known(v___x_8134_, 1);
                        v___x_8136_ = l_Lean_Expr_mvarId_x21(v_a_8135_);
                        v___x_8137_ = lean_box(0);
                        v___x_8138_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_8138_, 0, v___x_8136_);
                        lean_ctor_set(v___x_8138_, 1, v___x_8137_);
                        v_sz_8139_ = lean_array_size(v_eqs_8128_);
                        v___x_8140_ = 0usize;
                        v___x_8141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_8129_, v_eqs_8128_, v_sz_8139_, v___x_8140_, v___x_8138_, v_a_8121_, v_a_8122_, v_a_8123_, v_a_8124_);
                        lean_dec_ref(v_eqs_8128_);
                        if lean_obj_tag(v___x_8141_) == 0 {
                            v_a_8142_ = lean_ctor_get(v___x_8141_, 0);
                            lean_inc(v_a_8142_);
                            lean_dec_ref_known(v___x_8141_, 1);
                            v_fst_8143_ = lean_ctor_get(v_a_8142_, 0);
                            lean_inc(v_fst_8143_);
                            v_snd_8144_ = lean_ctor_get(v_a_8142_, 1);
                            lean_inc(v_snd_8144_);
                            lean_dec(v_a_8142_);
                            v___x_8145_ =
                                l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(
                                    v_snd_8144_,
                                    v_fvarId_8117_,
                                );
                            lean_dec(v_fvarId_8117_);
                            lean_dec(v_snd_8144_);
                            v___x_8146_ = l_Lean_mkFVar(v___x_8145_);
                            v___x_8147_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_8143_, v___x_8146_, v_a_8122_);
                            lean_dec_ref(v___x_8147_);
                            v___x_8148_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_8135_, v_a_8122_);
                            return v___x_8148_;
                        } else {
                            lean_dec(v_a_8135_);
                            lean_dec(v_fvarId_8117_);
                            v_a_8149_ = lean_ctor_get(v___x_8141_, 0);
                            v_isSharedCheck_8156_ = (!lean_is_exclusive(v___x_8141_)) as u8;
                            if v_isSharedCheck_8156_ == 0 {
                                v___x_8151_ = v___x_8141_;
                                v_isShared_8152_ = v_isSharedCheck_8156_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_8149_);
                                lean_dec(v___x_8141_);
                                v___x_8151_ = lean_box(0);
                                v_isShared_8152_ = v_isSharedCheck_8156_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_eqs_8128_);
                        lean_dec(v_fvarId_8117_);
                        return v___x_8134_;
                    }
                } else {
                    lean_dec_ref(v_eqs_8128_);
                    lean_dec_ref(v_type_8118_);
                    v___x_8157_ = l_Lean_mkFVar(v_fvarId_8117_);
                    v___x_8158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8158_, 0, v___x_8157_);
                    return v___x_8158_;
                }
            }
            1 => {
                if v_isShared_8152_ == 0 {
                    v___x_8154_ = v___x_8151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8155_, 0, v_a_8149_);
                    v___x_8154_ = v_reuseFailAlloc_8155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(
    mut v_fvarId_8159_: *mut LeanObject,
    mut v_type_8160_: *mut LeanObject,
    mut v_deps_8161_: *mut LeanObject,
    mut v_eqs_8162_: *mut LeanObject,
    mut v_a_8163_: *mut LeanObject,
    mut v_a_8164_: *mut LeanObject,
    mut v_a_8165_: *mut LeanObject,
    mut v_a_8166_: *mut LeanObject,
    mut v_a_8167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8168_: *mut LeanObject = core::ptr::null_mut();
    v_res_8168_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(
        v_fvarId_8159_,
        v_type_8160_,
        v_deps_8161_,
        v_eqs_8162_,
        v_a_8163_,
        v_a_8164_,
        v_a_8165_,
        v_a_8166_,
    );
    lean_dec(v_a_8166_);
    lean_dec_ref(v_a_8165_);
    lean_dec(v_a_8164_);
    lean_dec_ref(v_a_8163_);
    lean_dec_ref(v_eqs_8162_);
    lean_dec_ref(v_deps_8161_);
    return v_res_8168_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(
    mut v_mvarId_8169_: *mut LeanObject,
    mut v_val_8170_: *mut LeanObject,
    mut v___y_8171_: *mut LeanObject,
    mut v___y_8172_: *mut LeanObject,
    mut v___y_8173_: *mut LeanObject,
    mut v___y_8174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8176_: *mut LeanObject = core::ptr::null_mut();
    v___x_8176_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_8169_, v_val_8170_, v___y_8172_);
    return v___x_8176_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(
    mut v_mvarId_8177_: *mut LeanObject,
    mut v_val_8178_: *mut LeanObject,
    mut v___y_8179_: *mut LeanObject,
    mut v___y_8180_: *mut LeanObject,
    mut v___y_8181_: *mut LeanObject,
    mut v___y_8182_: *mut LeanObject,
    mut v___y_8183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8184_: *mut LeanObject = core::ptr::null_mut();
    v_res_8184_ =
        l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(
            v_mvarId_8177_,
            v_val_8178_,
            v___y_8179_,
            v___y_8180_,
            v___y_8181_,
            v___y_8182_,
        );
    lean_dec(v___y_8182_);
    lean_dec_ref(v___y_8181_);
    lean_dec(v___y_8180_);
    lean_dec_ref(v___y_8179_);
    return v_res_8184_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(
    mut v_00_u03b2_8185_: *mut LeanObject,
    mut v_x_8186_: *mut LeanObject,
    mut v_x_8187_: *mut LeanObject,
    mut v_x_8188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    v___x_8189_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_8186_, v_x_8187_, v_x_8188_);
    return v___x_8189_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(
    mut v_00_u03b2_8190_: *mut LeanObject,
    mut v_x_8191_: *mut LeanObject,
    mut v_x_8192_: usize,
    mut v_x_8193_: usize,
    mut v_x_8194_: *mut LeanObject,
    mut v_x_8195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8196_: *mut LeanObject = core::ptr::null_mut();
    v___x_8196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_8191_, v_x_8192_, v_x_8193_, v_x_8194_, v_x_8195_);
    return v___x_8196_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_8197_: *mut LeanObject,
    mut v_x_8198_: *mut LeanObject,
    mut v_x_8199_: *mut LeanObject,
    mut v_x_8200_: *mut LeanObject,
    mut v_x_8201_: *mut LeanObject,
    mut v_x_8202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4777__boxed_8203_: usize = 0;
    let mut v_x_4778__boxed_8204_: usize = 0;
    let mut v_res_8205_: *mut LeanObject = core::ptr::null_mut();
    v_x_4777__boxed_8203_ = lean_unbox_usize(v_x_8199_);
    lean_dec(v_x_8199_);
    v_x_4778__boxed_8204_ = lean_unbox_usize(v_x_8200_);
    lean_dec(v_x_8200_);
    v_res_8205_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_8197_, v_x_8198_, v_x_4777__boxed_8203_, v_x_4778__boxed_8204_, v_x_8201_, v_x_8202_);
    return v_res_8205_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(
    mut v_00_u03b2_8206_: *mut LeanObject,
    mut v_n_8207_: *mut LeanObject,
    mut v_k_8208_: *mut LeanObject,
    mut v_v_8209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8210_: *mut LeanObject = core::ptr::null_mut();
    v___x_8210_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_8207_, v_k_8208_, v_v_8209_);
    return v___x_8210_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(
    mut v_00_u03b2_8211_: *mut LeanObject,
    mut v_depth_8212_: usize,
    mut v_keys_8213_: *mut LeanObject,
    mut v_vals_8214_: *mut LeanObject,
    mut v_heq_8215_: *mut LeanObject,
    mut v_i_8216_: *mut LeanObject,
    mut v_entries_8217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8218_: *mut LeanObject = core::ptr::null_mut();
    v___x_8218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_8212_, v_keys_8213_, v_vals_8214_, v_i_8216_, v_entries_8217_);
    return v___x_8218_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b2_8219_: *mut LeanObject,
    mut v_depth_8220_: *mut LeanObject,
    mut v_keys_8221_: *mut LeanObject,
    mut v_vals_8222_: *mut LeanObject,
    mut v_heq_8223_: *mut LeanObject,
    mut v_i_8224_: *mut LeanObject,
    mut v_entries_8225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_8226_: usize = 0;
    let mut v_res_8227_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_8226_ = lean_unbox_usize(v_depth_8220_);
    lean_dec(v_depth_8220_);
    v_res_8227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_8219_, v_depth_boxed_8226_, v_keys_8221_, v_vals_8222_, v_heq_8223_, v_i_8224_, v_entries_8225_);
    lean_dec_ref(v_vals_8222_);
    lean_dec_ref(v_keys_8221_);
    return v_res_8227_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(
    mut v_00_u03b2_8228_: *mut LeanObject,
    mut v_x_8229_: *mut LeanObject,
    mut v_x_8230_: *mut LeanObject,
    mut v_x_8231_: *mut LeanObject,
    mut v_x_8232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8233_: *mut LeanObject = core::ptr::null_mut();
    v___x_8233_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_8229_, v_x_8230_, v_x_8231_, v_x_8232_);
    return v___x_8233_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(
    mut v_msg_8235_: *mut LeanObject,
    mut v___y_8236_: *mut LeanObject,
    mut v___y_8237_: *mut LeanObject,
    mut v___y_8238_: *mut LeanObject,
    mut v___y_8239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803__overap_8242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8243_: *mut LeanObject = core::ptr::null_mut();
    v___f_8241_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0;
    v___x_1803__overap_8242_ = lean_panic_fn_borrowed(v___f_8241_, v_msg_8235_);
    lean_inc(v___y_8239_);
    lean_inc_ref(v___y_8238_);
    lean_inc(v___y_8237_);
    lean_inc_ref(v___y_8236_);
    v___x_8243_ = lean_apply_5(
        v___x_1803__overap_8242_,
        v___y_8236_,
        v___y_8237_,
        v___y_8238_,
        v___y_8239_,
        lean_box(0),
    );
    return v___x_8243_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(
    mut v_msg_8244_: *mut LeanObject,
    mut v___y_8245_: *mut LeanObject,
    mut v___y_8246_: *mut LeanObject,
    mut v___y_8247_: *mut LeanObject,
    mut v___y_8248_: *mut LeanObject,
    mut v___y_8249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8250_: *mut LeanObject = core::ptr::null_mut();
    v_res_8250_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_8244_, v___y_8245_, v___y_8246_, v___y_8247_, v___y_8248_);
    lean_dec(v___y_8248_);
    lean_dec_ref(v___y_8247_);
    lean_dec(v___y_8246_);
    lean_dec_ref(v___y_8245_);
    return v_res_8250_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0()
-> *mut LeanObject {
    let mut v___x_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8259_: *mut LeanObject = core::ptr::null_mut();
    v___x_8254_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2;
    v___x_8255_ = lean_unsigned_to_nat(34);
    v___x_8256_ = lean_unsigned_to_nat(360);
    v___x_8257_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1;
    v___x_8258_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0;
    v___x_8259_ = l_mkPanicMessageWithDecl(
        v___x_8258_,
        v___x_8257_,
        v___x_8256_,
        v___x_8255_,
        v___x_8254_,
    );
    return v___x_8259_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(
    mut v___x_8260_: *mut LeanObject,
    mut v___x_8261_: *mut LeanObject,
    mut v___x_8262_: *mut LeanObject,
    mut v_i_8263_: *mut LeanObject,
    mut v_kinds_8264_: *mut LeanObject,
    mut v___x_8265_: *mut LeanObject,
    mut v_lhs_8266_: *mut LeanObject,
    mut v_rhs_8267_: *mut LeanObject,
    mut v_type_8268_: *mut LeanObject,
    mut v___y_8269_: *mut LeanObject,
    mut v___y_8270_: *mut LeanObject,
    mut v___y_8271_: *mut LeanObject,
    mut v___y_8272_: *mut LeanObject,
    mut v___y_8273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1990__boxed_8274_: u8 = 0;
    let mut v___x_1991__boxed_8275_: u8 = 0;
    let mut v_res_8276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1990__boxed_8274_ = (lean_unbox(v___x_8261_) as u8);
    v___x_1991__boxed_8275_ = (lean_unbox(v___x_8262_) as u8);
    v_res_8276_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(
            v___x_8260_,
            v___x_1990__boxed_8274_,
            v___x_1991__boxed_8275_,
            v_i_8263_,
            v_kinds_8264_,
            v___x_8265_,
            v_lhs_8266_,
            v_rhs_8267_,
            v_type_8268_,
            v___y_8269_,
            v___y_8270_,
            v___y_8271_,
            v___y_8272_,
        );
    lean_dec(v___y_8272_);
    lean_dec_ref(v___y_8271_);
    lean_dec(v___y_8270_);
    lean_dec_ref(v___y_8269_);
    return v_res_8276_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(
    mut v___x_8277_: *mut LeanObject,
    mut v___x_8278_: u8,
    mut v___x_8279_: u8,
    mut v_i_8280_: *mut LeanObject,
    mut v___x_8281_: *mut LeanObject,
    mut v_kinds_8282_: *mut LeanObject,
    mut v_typeSub_8283_: *mut LeanObject,
    mut v_lhs_8284_: *mut LeanObject,
    mut v_rhs_8285_: *mut LeanObject,
    mut v_type_8286_: *mut LeanObject,
    mut v___y_8287_: *mut LeanObject,
    mut v___y_8288_: *mut LeanObject,
    mut v___y_8289_: *mut LeanObject,
    mut v___y_8290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: u8 = 0;
    let mut v___x_8294_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_rhs_8285_);
    v___x_8292_ = lean_array_push(v___x_8277_, v_rhs_8285_);
    v___x_8293_ = 1;
    v___x_8294_ = l_Lean_Meta_mkLambdaFVars(
        v___x_8292_,
        v_type_8286_,
        v___x_8278_,
        v___x_8279_,
        v___x_8278_,
        v___x_8279_,
        v___x_8293_,
        v___y_8287_,
        v___y_8288_,
        v___y_8289_,
        v___y_8290_,
    );
    lean_dec_ref(v___x_8292_);
    if lean_obj_tag(v___x_8294_) == 0 {
        let mut v_a_8295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8297_: *mut LeanObject = core::ptr::null_mut();
        v_a_8295_ = lean_ctor_get(v___x_8294_, 0);
        lean_inc(v_a_8295_);
        lean_dec_ref_known(v___x_8294_, 1);
        v___x_8296_ = lean_nat_add(v_i_8280_, v___x_8281_);
        v___x_8297_ =
            l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(
                v_kinds_8282_,
                v___x_8296_,
                v_typeSub_8283_,
                v___y_8287_,
                v___y_8288_,
                v___y_8289_,
                v___y_8290_,
            );
        if lean_obj_tag(v___x_8297_) == 0 {
            let mut v_a_8298_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8299_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8301_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8303_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8304_: *mut LeanObject = core::ptr::null_mut();
            v_a_8298_ = lean_ctor_get(v___x_8297_, 0);
            lean_inc(v_a_8298_);
            lean_dec_ref_known(v___x_8297_, 1);
            v___x_8299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2;
            v___x_8300_ = lean_unsigned_to_nat(2);
            v___x_8301_ = lean_mk_empty_array_with_capacity(v___x_8300_);
            v___x_8302_ = lean_array_push(v___x_8301_, v_lhs_8284_);
            v___x_8303_ = lean_array_push(v___x_8302_, v_rhs_8285_);
            lean_inc_ref(v___x_8303_);
            v___x_8304_ = l_Lean_Meta_mkAppM(
                v___x_8299_,
                v___x_8303_,
                v___y_8287_,
                v___y_8288_,
                v___y_8289_,
                v___y_8290_,
            );
            if lean_obj_tag(v___x_8304_) == 0 {
                let mut v_a_8305_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8306_: *mut LeanObject = core::ptr::null_mut();
                v_a_8305_ = lean_ctor_get(v___x_8304_, 0);
                lean_inc(v_a_8305_);
                lean_dec_ref_known(v___x_8304_, 1);
                v___x_8306_ = l_Lean_Meta_mkEqNDRec(
                    v_a_8295_,
                    v_a_8298_,
                    v_a_8305_,
                    v___y_8287_,
                    v___y_8288_,
                    v___y_8289_,
                    v___y_8290_,
                );
                if lean_obj_tag(v___x_8306_) == 0 {
                    let mut v_a_8307_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_8308_: *mut LeanObject = core::ptr::null_mut();
                    v_a_8307_ = lean_ctor_get(v___x_8306_, 0);
                    lean_inc(v_a_8307_);
                    lean_dec_ref_known(v___x_8306_, 1);
                    v___x_8308_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_8303_,
                        v_a_8307_,
                        v___x_8278_,
                        v___x_8279_,
                        v___x_8278_,
                        v___x_8279_,
                        v___x_8293_,
                        v___y_8287_,
                        v___y_8288_,
                        v___y_8289_,
                        v___y_8290_,
                    );
                    lean_dec_ref(v___x_8303_);
                    return v___x_8308_;
                } else {
                    lean_dec_ref(v___x_8303_);
                    return v___x_8306_;
                }
            } else {
                lean_dec_ref(v___x_8303_);
                lean_dec(v_a_8298_);
                lean_dec(v_a_8295_);
                return v___x_8304_;
            }
        } else {
            lean_dec(v_a_8295_);
            lean_dec_ref(v_rhs_8285_);
            lean_dec_ref(v_lhs_8284_);
            return v___x_8297_;
        }
    } else {
        lean_dec_ref(v_rhs_8285_);
        lean_dec_ref(v_lhs_8284_);
        lean_dec_ref(v_typeSub_8283_);
        lean_dec_ref(v_kinds_8282_);
        return v___x_8294_;
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(
    mut v___x_8309_: *mut LeanObject,
    mut v___x_8310_: *mut LeanObject,
    mut v___x_8311_: *mut LeanObject,
    mut v_i_8312_: *mut LeanObject,
    mut v___x_8313_: *mut LeanObject,
    mut v_kinds_8314_: *mut LeanObject,
    mut v_typeSub_8315_: *mut LeanObject,
    mut v_lhs_8316_: *mut LeanObject,
    mut v_rhs_8317_: *mut LeanObject,
    mut v_type_8318_: *mut LeanObject,
    mut v___y_8319_: *mut LeanObject,
    mut v___y_8320_: *mut LeanObject,
    mut v___y_8321_: *mut LeanObject,
    mut v___y_8322_: *mut LeanObject,
    mut v___y_8323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2053__boxed_8324_: u8 = 0;
    let mut v___x_2054__boxed_8325_: u8 = 0;
    let mut v_res_8326_: *mut LeanObject = core::ptr::null_mut();
    v___x_2053__boxed_8324_ = (lean_unbox(v___x_8310_) as u8);
    v___x_2054__boxed_8325_ = (lean_unbox(v___x_8311_) as u8);
    v_res_8326_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(
            v___x_8309_,
            v___x_2053__boxed_8324_,
            v___x_2054__boxed_8325_,
            v_i_8312_,
            v___x_8313_,
            v_kinds_8314_,
            v_typeSub_8315_,
            v_lhs_8316_,
            v_rhs_8317_,
            v_type_8318_,
            v___y_8319_,
            v___y_8320_,
            v___y_8321_,
            v___y_8322_,
        );
    lean_dec(v___y_8322_);
    lean_dec_ref(v___y_8321_);
    lean_dec(v___y_8320_);
    lean_dec_ref(v___y_8319_);
    lean_dec(v___x_8313_);
    lean_dec(v_i_8312_);
    return v_res_8326_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(
    mut v_kinds_8327_: *mut LeanObject,
    mut v_i_8328_: *mut LeanObject,
    mut v___x_8329_: u8,
    mut v___x_8330_: u8,
    mut v_lhs_8331_: *mut LeanObject,
    mut v_type_8332_: *mut LeanObject,
    mut v___y_8333_: *mut LeanObject,
    mut v___y_8334_: *mut LeanObject,
    mut v___y_8335_: *mut LeanObject,
    mut v___y_8336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8341_: u8 = 0;
    let mut v___x_8342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8344_: u8 = 0;
    let mut v___x_8345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeSub_8362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8373_: u8 = 0;
    let mut v___x_8374_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8341_ = 0;
                v___x_8342_ = lean_box((v___x_8341_) as usize);
                v___x_8343_ = lean_array_get(v___x_8342_, v_kinds_8327_, v_i_8328_);
                lean_dec(v___x_8342_);
                v___x_8344_ = (lean_unbox(v___x_8343_) as u8);
                lean_dec(v___x_8343_);
                match v___x_8344_ {
                    1 => {
                        lean_dec_ref(v_type_8332_);
                        lean_dec_ref(v_lhs_8331_);
                        lean_dec(v_i_8328_);
                        lean_dec_ref(v_kinds_8327_);
                        state = 1;
                        continue;
                    }
                    2 => {
                        lean_inc_ref(v_lhs_8331_);
                        v___x_8345_ = l_Lean_Meta_mkEqRefl(
                            v_lhs_8331_,
                            v___y_8333_,
                            v___y_8334_,
                            v___y_8335_,
                            v___y_8336_,
                        );
                        if lean_obj_tag(v___x_8345_) == 0 {
                            v_a_8346_ = lean_ctor_get(v___x_8345_, 0);
                            lean_inc(v_a_8346_);
                            lean_dec_ref_known(v___x_8345_, 1);
                            v___x_8347_ = l_Lean_Expr_bindingBody_x21(v_type_8332_);
                            v___x_8348_ = l_Lean_Expr_bindingBody_x21(v___x_8347_);
                            lean_dec_ref(v___x_8347_);
                            v___x_8349_ = lean_unsigned_to_nat(2);
                            v___x_8350_ = lean_mk_empty_array_with_capacity(v___x_8349_);
                            lean_inc_ref(v___x_8350_);
                            v___x_8351_ = lean_array_push(v___x_8350_, v_a_8346_);
                            lean_inc_ref(v_lhs_8331_);
                            v___x_8352_ = lean_array_push(v___x_8351_, v_lhs_8331_);
                            v___x_8353_ = lean_expr_instantiate(v___x_8348_, v___x_8352_);
                            lean_dec_ref(v___x_8352_);
                            lean_dec_ref(v___x_8348_);
                            v___x_8354_ = lean_box((v___x_8329_) as usize);
                            v___x_8355_ = lean_box((v___x_8330_) as usize);
                            v___f_8356_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed as *mut core::ffi::c_void, 14, 7);
                            lean_closure_set(v___f_8356_, 0, v___x_8350_);
                            lean_closure_set(v___f_8356_, 1, v___x_8354_);
                            lean_closure_set(v___f_8356_, 2, v___x_8355_);
                            lean_closure_set(v___f_8356_, 3, v_i_8328_);
                            lean_closure_set(v___f_8356_, 4, v_kinds_8327_);
                            lean_closure_set(v___f_8356_, 5, v___x_8353_);
                            lean_closure_set(v___f_8356_, 6, v_lhs_8331_);
                            v___x_8357_ =
                                l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(
                                    v_type_8332_,
                                    v___f_8356_,
                                    v___y_8333_,
                                    v___y_8334_,
                                    v___y_8335_,
                                    v___y_8336_,
                                );
                            return v___x_8357_;
                        } else {
                            lean_dec_ref(v_type_8332_);
                            lean_dec_ref(v_lhs_8331_);
                            lean_dec(v_i_8328_);
                            lean_dec_ref(v_kinds_8327_);
                            return v___x_8345_;
                        }
                    }
                    4 => {
                        lean_dec_ref(v_type_8332_);
                        lean_dec_ref(v_lhs_8331_);
                        lean_dec(v_i_8328_);
                        lean_dec_ref(v_kinds_8327_);
                        state = 1;
                        continue;
                    }
                    5 => {
                        v___x_8358_ = l_Lean_Expr_bindingBody_x21(v_type_8332_);
                        v___x_8359_ = lean_unsigned_to_nat(1);
                        v___x_8360_ = lean_mk_empty_array_with_capacity(v___x_8359_);
                        lean_inc_ref(v_lhs_8331_);
                        lean_inc_ref(v___x_8360_);
                        v___x_8361_ = lean_array_push(v___x_8360_, v_lhs_8331_);
                        v_typeSub_8362_ = lean_expr_instantiate(v___x_8358_, v___x_8361_);
                        lean_dec_ref(v___x_8361_);
                        lean_dec_ref(v___x_8358_);
                        v___x_8363_ = lean_box((v___x_8329_) as usize);
                        v___x_8364_ = lean_box((v___x_8330_) as usize);
                        v___f_8365_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed as *mut core::ffi::c_void, 15, 8);
                        lean_closure_set(v___f_8365_, 0, v___x_8360_);
                        lean_closure_set(v___f_8365_, 1, v___x_8363_);
                        lean_closure_set(v___f_8365_, 2, v___x_8364_);
                        lean_closure_set(v___f_8365_, 3, v_i_8328_);
                        lean_closure_set(v___f_8365_, 4, v___x_8359_);
                        lean_closure_set(v___f_8365_, 5, v_kinds_8327_);
                        lean_closure_set(v___f_8365_, 6, v_typeSub_8362_);
                        lean_closure_set(v___f_8365_, 7, v_lhs_8331_);
                        v___x_8366_ =
                            l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(
                                v_type_8332_,
                                v___f_8365_,
                                v___y_8333_,
                                v___y_8334_,
                                v___y_8335_,
                                v___y_8336_,
                            );
                        return v___x_8366_;
                    }
                    _ => {
                        v___x_8367_ = lean_unsigned_to_nat(1);
                        v___x_8368_ = lean_nat_add(v_i_8328_, v___x_8367_);
                        lean_dec(v_i_8328_);
                        v___x_8369_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_8327_, v___x_8368_, v_type_8332_, v___y_8333_, v___y_8334_, v___y_8335_, v___y_8336_);
                        if lean_obj_tag(v___x_8369_) == 0 {
                            v_a_8370_ = lean_ctor_get(v___x_8369_, 0);
                            lean_inc(v_a_8370_);
                            lean_dec_ref_known(v___x_8369_, 1);
                            v___x_8371_ = lean_mk_empty_array_with_capacity(v___x_8367_);
                            v___x_8372_ = lean_array_push(v___x_8371_, v_lhs_8331_);
                            v___x_8373_ = 1;
                            v___x_8374_ = l_Lean_Meta_mkLambdaFVars(
                                v___x_8372_,
                                v_a_8370_,
                                v___x_8329_,
                                v___x_8330_,
                                v___x_8329_,
                                v___x_8330_,
                                v___x_8373_,
                                v___y_8333_,
                                v___y_8334_,
                                v___y_8335_,
                                v___y_8336_,
                            );
                            lean_dec_ref(v___x_8372_);
                            return v___x_8374_;
                        } else {
                            lean_dec_ref(v_lhs_8331_);
                            return v___x_8369_;
                        }
                    }
                }
            }
            1 => {
                v___x_8339_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
                v___x_8340_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_8339_, v___y_8333_, v___y_8334_, v___y_8335_, v___y_8336_);
                return v___x_8340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(
    mut v_kinds_8375_: *mut LeanObject,
    mut v_i_8376_: *mut LeanObject,
    mut v___x_8377_: *mut LeanObject,
    mut v___x_8378_: *mut LeanObject,
    mut v_lhs_8379_: *mut LeanObject,
    mut v_type_8380_: *mut LeanObject,
    mut v___y_8381_: *mut LeanObject,
    mut v___y_8382_: *mut LeanObject,
    mut v___y_8383_: *mut LeanObject,
    mut v___y_8384_: *mut LeanObject,
    mut v___y_8385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2090__boxed_8386_: u8 = 0;
    let mut v___x_2091__boxed_8387_: u8 = 0;
    let mut v_res_8388_: *mut LeanObject = core::ptr::null_mut();
    v___x_2090__boxed_8386_ = (lean_unbox(v___x_8377_) as u8);
    v___x_2091__boxed_8387_ = (lean_unbox(v___x_8378_) as u8);
    v_res_8388_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(
            v_kinds_8375_,
            v_i_8376_,
            v___x_2090__boxed_8386_,
            v___x_2091__boxed_8387_,
            v_lhs_8379_,
            v_type_8380_,
            v___y_8381_,
            v___y_8382_,
            v___y_8383_,
            v___y_8384_,
        );
    lean_dec(v___y_8384_);
    lean_dec_ref(v___y_8383_);
    lean_dec(v___y_8382_);
    lean_dec_ref(v___y_8381_);
    return v_res_8388_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3()
-> *mut LeanObject {
    let mut v___x_8389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    v___x_8389_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2;
    v___x_8390_ = lean_unsigned_to_nat(43);
    v___x_8391_ = lean_unsigned_to_nat(355);
    v___x_8392_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1;
    v___x_8393_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0;
    v___x_8394_ = l_mkPanicMessageWithDecl(
        v___x_8393_,
        v___x_8392_,
        v___x_8391_,
        v___x_8390_,
        v___x_8389_,
    );
    return v___x_8394_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(
    mut v_kinds_8395_: *mut LeanObject,
    mut v_i_8396_: *mut LeanObject,
    mut v_type_8397_: *mut LeanObject,
    mut v_a_8398_: *mut LeanObject,
    mut v_a_8399_: *mut LeanObject,
    mut v_a_8400_: *mut LeanObject,
    mut v_a_8401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8404_: u8 = 0;
    v___x_8403_ = lean_array_get_size(v_kinds_8395_);
    v___x_8404_ = lean_nat_dec_eq(v_i_8396_, v___x_8403_);
    if v___x_8404_ == 0 {
        let mut v___x_8405_: u8 = 0;
        let mut v___x_8406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8409_: *mut LeanObject = core::ptr::null_mut();
        v___x_8405_ = 1;
        v___x_8406_ = lean_box((v___x_8404_) as usize);
        v___x_8407_ = lean_box((v___x_8405_) as usize);
        v___f_8408_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed as *mut core::ffi::c_void, 11, 4);
        lean_closure_set(v___f_8408_, 0, v_kinds_8395_);
        lean_closure_set(v___f_8408_, 1, v_i_8396_);
        lean_closure_set(v___f_8408_, 2, v___x_8406_);
        lean_closure_set(v___f_8408_, 3, v___x_8407_);
        v___x_8409_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(
            v_type_8397_,
            v___f_8408_,
            v_a_8398_,
            v_a_8399_,
            v_a_8400_,
            v_a_8401_,
        );
        return v___x_8409_;
    } else {
        let mut v___x_8410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8412_: u8 = 0;
        lean_dec(v_i_8396_);
        lean_dec_ref(v_kinds_8395_);
        v___x_8410_ =
            l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1;
        v___x_8411_ = lean_unsigned_to_nat(3);
        v___x_8412_ = l_Lean_Expr_isAppOfArity(v_type_8397_, v___x_8410_, v___x_8411_);
        if v___x_8412_ == 0 {
            let mut v___x_8413_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_type_8397_);
            v___x_8413_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
            v___x_8414_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_8413_, v_a_8398_, v_a_8399_, v_a_8400_, v_a_8401_);
            return v___x_8414_;
        } else {
            let mut v___x_8415_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8417_: *mut LeanObject = core::ptr::null_mut();
            v___x_8415_ = l_Lean_Expr_appFn_x21(v_type_8397_);
            lean_dec_ref(v_type_8397_);
            v___x_8416_ = l_Lean_Expr_appArg_x21(v___x_8415_);
            lean_dec_ref(v___x_8415_);
            v___x_8417_ =
                l_Lean_Meta_mkEqRefl(v___x_8416_, v_a_8398_, v_a_8399_, v_a_8400_, v_a_8401_);
            return v___x_8417_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(
    mut v___x_8418_: *mut LeanObject,
    mut v_rhs_8419_: *mut LeanObject,
    mut v___x_8420_: u8,
    mut v___x_8421_: u8,
    mut v_i_8422_: *mut LeanObject,
    mut v_kinds_8423_: *mut LeanObject,
    mut v___x_8424_: *mut LeanObject,
    mut v_lhs_8425_: *mut LeanObject,
    mut v_heq_8426_: *mut LeanObject,
    mut v_type_8427_: *mut LeanObject,
    mut v___y_8428_: *mut LeanObject,
    mut v___y_8429_: *mut LeanObject,
    mut v___y_8430_: *mut LeanObject,
    mut v___y_8431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8435_: u8 = 0;
    let mut v___x_8436_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_rhs_8419_);
    v___x_8433_ = lean_array_push(v___x_8418_, v_rhs_8419_);
    lean_inc_ref(v_heq_8426_);
    v___x_8434_ = lean_array_push(v___x_8433_, v_heq_8426_);
    v___x_8435_ = 1;
    v___x_8436_ = l_Lean_Meta_mkLambdaFVars(
        v___x_8434_,
        v_type_8427_,
        v___x_8420_,
        v___x_8421_,
        v___x_8420_,
        v___x_8421_,
        v___x_8435_,
        v___y_8428_,
        v___y_8429_,
        v___y_8430_,
        v___y_8431_,
    );
    lean_dec_ref(v___x_8434_);
    if lean_obj_tag(v___x_8436_) == 0 {
        let mut v_a_8437_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8440_: *mut LeanObject = core::ptr::null_mut();
        v_a_8437_ = lean_ctor_get(v___x_8436_, 0);
        lean_inc(v_a_8437_);
        lean_dec_ref_known(v___x_8436_, 1);
        v___x_8438_ = lean_unsigned_to_nat(1);
        v___x_8439_ = lean_nat_add(v_i_8422_, v___x_8438_);
        v___x_8440_ =
            l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(
                v_kinds_8423_,
                v___x_8439_,
                v___x_8424_,
                v___y_8428_,
                v___y_8429_,
                v___y_8430_,
                v___y_8431_,
            );
        if lean_obj_tag(v___x_8440_) == 0 {
            let mut v_a_8441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8442_: *mut LeanObject = core::ptr::null_mut();
            v_a_8441_ = lean_ctor_get(v___x_8440_, 0);
            lean_inc(v_a_8441_);
            lean_dec_ref_known(v___x_8440_, 1);
            lean_inc_ref(v_heq_8426_);
            v___x_8442_ = l_Lean_Meta_mkEqRec(
                v_a_8437_,
                v_a_8441_,
                v_heq_8426_,
                v___y_8428_,
                v___y_8429_,
                v___y_8430_,
                v___y_8431_,
            );
            if lean_obj_tag(v___x_8442_) == 0 {
                let mut v_a_8443_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8444_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8445_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8446_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8447_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8448_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8449_: *mut LeanObject = core::ptr::null_mut();
                v_a_8443_ = lean_ctor_get(v___x_8442_, 0);
                lean_inc(v_a_8443_);
                lean_dec_ref_known(v___x_8442_, 1);
                v___x_8444_ = lean_unsigned_to_nat(3);
                v___x_8445_ = lean_mk_empty_array_with_capacity(v___x_8444_);
                v___x_8446_ = lean_array_push(v___x_8445_, v_lhs_8425_);
                v___x_8447_ = lean_array_push(v___x_8446_, v_rhs_8419_);
                v___x_8448_ = lean_array_push(v___x_8447_, v_heq_8426_);
                v___x_8449_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_8448_,
                    v_a_8443_,
                    v___x_8420_,
                    v___x_8421_,
                    v___x_8420_,
                    v___x_8421_,
                    v___x_8435_,
                    v___y_8428_,
                    v___y_8429_,
                    v___y_8430_,
                    v___y_8431_,
                );
                lean_dec_ref(v___x_8448_);
                return v___x_8449_;
            } else {
                lean_dec_ref(v_heq_8426_);
                lean_dec_ref(v_lhs_8425_);
                lean_dec_ref(v_rhs_8419_);
                return v___x_8442_;
            }
        } else {
            lean_dec(v_a_8437_);
            lean_dec_ref(v_heq_8426_);
            lean_dec_ref(v_lhs_8425_);
            lean_dec_ref(v_rhs_8419_);
            return v___x_8440_;
        }
    } else {
        lean_dec_ref(v_heq_8426_);
        lean_dec_ref(v_lhs_8425_);
        lean_dec_ref(v___x_8424_);
        lean_dec_ref(v_kinds_8423_);
        lean_dec_ref(v_rhs_8419_);
        return v___x_8436_;
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(
    mut v___x_8450_: *mut LeanObject,
    mut v_rhs_8451_: *mut LeanObject,
    mut v___x_8452_: *mut LeanObject,
    mut v___x_8453_: *mut LeanObject,
    mut v_i_8454_: *mut LeanObject,
    mut v_kinds_8455_: *mut LeanObject,
    mut v___x_8456_: *mut LeanObject,
    mut v_lhs_8457_: *mut LeanObject,
    mut v_heq_8458_: *mut LeanObject,
    mut v_type_8459_: *mut LeanObject,
    mut v___y_8460_: *mut LeanObject,
    mut v___y_8461_: *mut LeanObject,
    mut v___y_8462_: *mut LeanObject,
    mut v___y_8463_: *mut LeanObject,
    mut v___y_8464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2001__boxed_8465_: u8 = 0;
    let mut v___x_2002__boxed_8466_: u8 = 0;
    let mut v_res_8467_: *mut LeanObject = core::ptr::null_mut();
    v___x_2001__boxed_8465_ = (lean_unbox(v___x_8452_) as u8);
    v___x_2002__boxed_8466_ = (lean_unbox(v___x_8453_) as u8);
    v_res_8467_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(
            v___x_8450_,
            v_rhs_8451_,
            v___x_2001__boxed_8465_,
            v___x_2002__boxed_8466_,
            v_i_8454_,
            v_kinds_8455_,
            v___x_8456_,
            v_lhs_8457_,
            v_heq_8458_,
            v_type_8459_,
            v___y_8460_,
            v___y_8461_,
            v___y_8462_,
            v___y_8463_,
        );
    lean_dec(v___y_8463_);
    lean_dec_ref(v___y_8462_);
    lean_dec(v___y_8461_);
    lean_dec_ref(v___y_8460_);
    lean_dec(v_i_8454_);
    return v_res_8467_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(
    mut v___x_8468_: *mut LeanObject,
    mut v___x_8469_: u8,
    mut v___x_8470_: u8,
    mut v_i_8471_: *mut LeanObject,
    mut v_kinds_8472_: *mut LeanObject,
    mut v___x_8473_: *mut LeanObject,
    mut v_lhs_8474_: *mut LeanObject,
    mut v_rhs_8475_: *mut LeanObject,
    mut v_type_8476_: *mut LeanObject,
    mut v___y_8477_: *mut LeanObject,
    mut v___y_8478_: *mut LeanObject,
    mut v___y_8479_: *mut LeanObject,
    mut v___y_8480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8485_: *mut LeanObject = core::ptr::null_mut();
    v___x_8482_ = lean_box((v___x_8469_) as usize);
    v___x_8483_ = lean_box((v___x_8470_) as usize);
    v___f_8484_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed as *mut core::ffi::c_void, 15, 8);
    lean_closure_set(v___f_8484_, 0, v___x_8468_);
    lean_closure_set(v___f_8484_, 1, v_rhs_8475_);
    lean_closure_set(v___f_8484_, 2, v___x_8482_);
    lean_closure_set(v___f_8484_, 3, v___x_8483_);
    lean_closure_set(v___f_8484_, 4, v_i_8471_);
    lean_closure_set(v___f_8484_, 5, v_kinds_8472_);
    lean_closure_set(v___f_8484_, 6, v___x_8473_);
    lean_closure_set(v___f_8484_, 7, v_lhs_8474_);
    v___x_8485_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(
        v_type_8476_,
        v___f_8484_,
        v___y_8477_,
        v___y_8478_,
        v___y_8479_,
        v___y_8480_,
    );
    return v___x_8485_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(
    mut v_kinds_8486_: *mut LeanObject,
    mut v_i_8487_: *mut LeanObject,
    mut v_type_8488_: *mut LeanObject,
    mut v_a_8489_: *mut LeanObject,
    mut v_a_8490_: *mut LeanObject,
    mut v_a_8491_: *mut LeanObject,
    mut v_a_8492_: *mut LeanObject,
    mut v_a_8493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8494_: *mut LeanObject = core::ptr::null_mut();
    v_res_8494_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(
        v_kinds_8486_,
        v_i_8487_,
        v_type_8488_,
        v_a_8489_,
        v_a_8490_,
        v_a_8491_,
        v_a_8492_,
    );
    lean_dec(v_a_8492_);
    lean_dec_ref(v_a_8491_);
    lean_dec(v_a_8490_);
    lean_dec_ref(v_a_8489_);
    return v_res_8494_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(
    mut v_type_8495_: *mut LeanObject,
    mut v_kinds_8496_: *mut LeanObject,
    mut v_a_8497_: *mut LeanObject,
    mut v_a_8498_: *mut LeanObject,
    mut v_a_8499_: *mut LeanObject,
    mut v_a_8500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut LeanObject = core::ptr::null_mut();
    v___x_8502_ = lean_unsigned_to_nat(0);
    v___x_8503_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(
        v_kinds_8496_,
        v___x_8502_,
        v_type_8495_,
        v_a_8497_,
        v_a_8498_,
        v_a_8499_,
        v_a_8500_,
    );
    return v___x_8503_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(
    mut v_type_8504_: *mut LeanObject,
    mut v_kinds_8505_: *mut LeanObject,
    mut v_a_8506_: *mut LeanObject,
    mut v_a_8507_: *mut LeanObject,
    mut v_a_8508_: *mut LeanObject,
    mut v_a_8509_: *mut LeanObject,
    mut v_a_8510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8511_: *mut LeanObject = core::ptr::null_mut();
    v_res_8511_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(
        v_type_8504_,
        v_kinds_8505_,
        v_a_8506_,
        v_a_8507_,
        v_a_8508_,
        v_a_8509_,
    );
    lean_dec(v_a_8509_);
    lean_dec_ref(v_a_8508_);
    lean_dec(v_a_8507_);
    lean_dec_ref(v_a_8506_);
    return v_res_8511_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(
    mut v_msg_8512_: *mut LeanObject,
    mut v___y_8513_: *mut LeanObject,
    mut v___y_8514_: *mut LeanObject,
    mut v___y_8515_: *mut LeanObject,
    mut v___y_8516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082__overap_8519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8520_: *mut LeanObject = core::ptr::null_mut();
    v___f_8518_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0;
    v___x_2082__overap_8519_ = lean_panic_fn_borrowed(v___f_8518_, v_msg_8512_);
    lean_inc(v___y_8516_);
    lean_inc_ref(v___y_8515_);
    lean_inc(v___y_8514_);
    lean_inc_ref(v___y_8513_);
    v___x_8520_ = lean_apply_5(
        v___x_2082__overap_8519_,
        v___y_8513_,
        v___y_8514_,
        v___y_8515_,
        v___y_8516_,
        lean_box(0),
    );
    return v___x_8520_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(
    mut v_msg_8521_: *mut LeanObject,
    mut v___y_8522_: *mut LeanObject,
    mut v___y_8523_: *mut LeanObject,
    mut v___y_8524_: *mut LeanObject,
    mut v___y_8525_: *mut LeanObject,
    mut v___y_8526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8527_: *mut LeanObject = core::ptr::null_mut();
    v_res_8527_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_msg_8521_, v___y_8522_, v___y_8523_, v___y_8524_, v___y_8525_);
    lean_dec(v___y_8525_);
    lean_dec_ref(v___y_8524_);
    lean_dec(v___y_8523_);
    lean_dec_ref(v___y_8522_);
    return v_res_8527_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(
    mut v_bs_8528_: *mut LeanObject,
    mut v_k_8529_: *mut LeanObject,
    mut v___y_8530_: *mut LeanObject,
    mut v___y_8531_: *mut LeanObject,
    mut v___y_8532_: *mut LeanObject,
    mut v___y_8533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8539_: u8 = 0;
    let mut v___x_8541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8543_: u8 = 0;
    let mut v_a_8544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8547_: u8 = 0;
    let mut v___x_8549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8535_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(
                    lean_box(0),
                    v_bs_8528_,
                    v_k_8529_,
                    v___y_8530_,
                    v___y_8531_,
                    v___y_8532_,
                    v___y_8533_,
                );
                if lean_obj_tag(v___x_8535_) == 0 {
                    v_a_8536_ = lean_ctor_get(v___x_8535_, 0);
                    v_isSharedCheck_8543_ = (!lean_is_exclusive(v___x_8535_)) as u8;
                    if v_isSharedCheck_8543_ == 0 {
                        v___x_8538_ = v___x_8535_;
                        v_isShared_8539_ = v_isSharedCheck_8543_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8536_);
                        lean_dec(v___x_8535_);
                        v___x_8538_ = lean_box(0);
                        v_isShared_8539_ = v_isSharedCheck_8543_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8544_ = lean_ctor_get(v___x_8535_, 0);
                    v_isSharedCheck_8551_ = (!lean_is_exclusive(v___x_8535_)) as u8;
                    if v_isSharedCheck_8551_ == 0 {
                        v___x_8546_ = v___x_8535_;
                        v_isShared_8547_ = v_isSharedCheck_8551_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8544_);
                        lean_dec(v___x_8535_);
                        v___x_8546_ = lean_box(0);
                        v_isShared_8547_ = v_isSharedCheck_8551_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8539_ == 0 {
                    v___x_8541_ = v___x_8538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8542_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8542_, 0, v_a_8536_);
                    v___x_8541_ = v_reuseFailAlloc_8542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8541_;
            }
            3 => {
                if v_isShared_8547_ == 0 {
                    v___x_8549_ = v___x_8546_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8550_, 0, v_a_8544_);
                    v___x_8549_ = v_reuseFailAlloc_8550_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(
    mut v_bs_8552_: *mut LeanObject,
    mut v_k_8553_: *mut LeanObject,
    mut v___y_8554_: *mut LeanObject,
    mut v___y_8555_: *mut LeanObject,
    mut v___y_8556_: *mut LeanObject,
    mut v___y_8557_: *mut LeanObject,
    mut v___y_8558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8559_: *mut LeanObject = core::ptr::null_mut();
    v_res_8559_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_8552_, v_k_8553_, v___y_8554_, v___y_8555_, v___y_8556_, v___y_8557_);
    lean_dec(v___y_8557_);
    lean_dec_ref(v___y_8556_);
    lean_dec(v___y_8555_);
    lean_dec_ref(v___y_8554_);
    lean_dec_ref(v_bs_8552_);
    return v_res_8559_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(
    mut v_00_u03b1_8560_: *mut LeanObject,
    mut v_bs_8561_: *mut LeanObject,
    mut v_k_8562_: *mut LeanObject,
    mut v___y_8563_: *mut LeanObject,
    mut v___y_8564_: *mut LeanObject,
    mut v___y_8565_: *mut LeanObject,
    mut v___y_8566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8568_: *mut LeanObject = core::ptr::null_mut();
    v___x_8568_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_8561_, v_k_8562_, v___y_8563_, v___y_8564_, v___y_8565_, v___y_8566_);
    return v___x_8568_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(
    mut v_00_u03b1_8569_: *mut LeanObject,
    mut v_bs_8570_: *mut LeanObject,
    mut v_k_8571_: *mut LeanObject,
    mut v___y_8572_: *mut LeanObject,
    mut v___y_8573_: *mut LeanObject,
    mut v___y_8574_: *mut LeanObject,
    mut v___y_8575_: *mut LeanObject,
    mut v___y_8576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8577_: *mut LeanObject = core::ptr::null_mut();
    v_res_8577_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(v_00_u03b1_8569_, v_bs_8570_, v_k_8571_, v___y_8572_, v___y_8573_, v___y_8574_, v___y_8575_);
    lean_dec(v___y_8575_);
    lean_dec_ref(v___y_8574_);
    lean_dec(v___y_8573_);
    lean_dec_ref(v___y_8572_);
    lean_dec_ref(v_bs_8570_);
    return v_res_8577_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(
    mut v_sz_8578_: usize,
    mut v_i_8579_: usize,
    mut v_bs_8580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8581_: u8 = 0;
    let mut v_v_8582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8586_: u8 = 0;
    let mut v___x_8587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8589_: usize = 0;
    let mut v___x_8590_: usize = 0;
    let mut v___x_8591_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8581_ = lean_usize_dec_lt(v_i_8579_, v_sz_8578_);
                if v___x_8581_ == 0 {
                    return v_bs_8580_;
                } else {
                    v_v_8582_ = lean_array_uget(v_bs_8580_, v_i_8579_);
                    v___x_8583_ = lean_unsigned_to_nat(0);
                    v_bs_x27_8584_ = lean_array_uset(v_bs_8580_, v_i_8579_, v___x_8583_);
                    v___x_8585_ = l_Lean_Expr_fvarId_x21(v_v_8582_);
                    lean_dec(v_v_8582_);
                    v___x_8586_ = 1;
                    v___x_8587_ = lean_box((v___x_8586_) as usize);
                    v___x_8588_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8588_, 0, v___x_8585_);
                    lean_ctor_set(v___x_8588_, 1, v___x_8587_);
                    v___x_8589_ = 1usize;
                    v___x_8590_ = lean_usize_add(v_i_8579_, v___x_8589_);
                    v___x_8591_ = lean_array_uset(v_bs_x27_8584_, v_i_8579_, v___x_8588_);
                    v_i_8579_ = v___x_8590_;
                    v_bs_8580_ = v___x_8591_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(
    mut v_sz_8593_: *mut LeanObject,
    mut v_i_8594_: *mut LeanObject,
    mut v_bs_8595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8596_: usize = 0;
    let mut v_i_boxed_8597_: usize = 0;
    let mut v_res_8598_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8596_ = lean_unbox_usize(v_sz_8593_);
    lean_dec(v_sz_8593_);
    v_i_boxed_8597_ = lean_unbox_usize(v_i_8594_);
    lean_dec(v_i_8594_);
    v_res_8598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_boxed_8596_, v_i_boxed_8597_, v_bs_8595_);
    return v_res_8598_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(
    mut v_bs_8599_: *mut LeanObject,
    mut v_k_8600_: *mut LeanObject,
    mut v___y_8601_: *mut LeanObject,
    mut v___y_8602_: *mut LeanObject,
    mut v___y_8603_: *mut LeanObject,
    mut v___y_8604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_8606_: usize = 0;
    let mut v___x_8607_: usize = 0;
    let mut v___x_8608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8609_: *mut LeanObject = core::ptr::null_mut();
    v_sz_8606_ = lean_array_size(v_bs_8599_);
    v___x_8607_ = 0usize;
    v___x_8608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_8606_, v___x_8607_, v_bs_8599_);
    v___x_8609_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v___x_8608_, v_k_8600_, v___y_8601_, v___y_8602_, v___y_8603_, v___y_8604_);
    lean_dec_ref(v___x_8608_);
    return v___x_8609_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(
    mut v_bs_8610_: *mut LeanObject,
    mut v_k_8611_: *mut LeanObject,
    mut v___y_8612_: *mut LeanObject,
    mut v___y_8613_: *mut LeanObject,
    mut v___y_8614_: *mut LeanObject,
    mut v___y_8615_: *mut LeanObject,
    mut v___y_8616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8617_: *mut LeanObject = core::ptr::null_mut();
    v_res_8617_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_8610_, v_k_8611_, v___y_8612_, v___y_8613_, v___y_8614_, v___y_8615_);
    lean_dec(v___y_8615_);
    lean_dec_ref(v___y_8614_);
    lean_dec(v___y_8613_);
    lean_dec_ref(v___y_8612_);
    return v_res_8617_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(
    mut v_00_u03b1_8618_: *mut LeanObject,
    mut v_bs_8619_: *mut LeanObject,
    mut v_k_8620_: *mut LeanObject,
    mut v___y_8621_: *mut LeanObject,
    mut v___y_8622_: *mut LeanObject,
    mut v___y_8623_: *mut LeanObject,
    mut v___y_8624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8626_: *mut LeanObject = core::ptr::null_mut();
    v___x_8626_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_8619_, v_k_8620_, v___y_8621_, v___y_8622_, v___y_8623_, v___y_8624_);
    return v___x_8626_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(
    mut v_00_u03b1_8627_: *mut LeanObject,
    mut v_bs_8628_: *mut LeanObject,
    mut v_k_8629_: *mut LeanObject,
    mut v___y_8630_: *mut LeanObject,
    mut v___y_8631_: *mut LeanObject,
    mut v___y_8632_: *mut LeanObject,
    mut v___y_8633_: *mut LeanObject,
    mut v___y_8634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8635_: *mut LeanObject = core::ptr::null_mut();
    v_res_8635_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_00_u03b1_8627_, v_bs_8628_, v_k_8629_, v___y_8630_, v___y_8631_, v___y_8632_, v___y_8633_);
    lean_dec(v___y_8633_);
    lean_dec_ref(v___y_8632_);
    lean_dec(v___y_8631_);
    lean_dec_ref(v___y_8630_);
    return v_res_8635_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(
    mut v_i_8636_: *mut LeanObject,
    mut v_rhss_8637_: *mut LeanObject,
    mut v_lhs_8638_: *mut LeanObject,
    mut v_eqs_8639_: *mut LeanObject,
    mut v_hyps_8640_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8641_: u8,
    mut v_f_8642_: *mut LeanObject,
    mut v_info_8643_: *mut LeanObject,
    mut v_kinds_8644_: *mut LeanObject,
    mut v_lhss_8645_: *mut LeanObject,
    mut v_b_8646_: *mut LeanObject,
    mut v___y_8647_: *mut LeanObject,
    mut v___y_8648_: *mut LeanObject,
    mut v___y_8649_: *mut LeanObject,
    mut v___y_8650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8661_: *mut LeanObject = core::ptr::null_mut();
    v___x_8652_ = lean_unsigned_to_nat(1);
    v___x_8653_ = lean_nat_add(v_i_8636_, v___x_8652_);
    lean_inc_ref(v_b_8646_);
    v___x_8654_ = lean_array_push(v_rhss_8637_, v_b_8646_);
    v___x_8655_ = l_Lean_Expr_fvarId_x21(v_lhs_8638_);
    v___x_8656_ = l_Lean_Expr_fvarId_x21(v_b_8646_);
    v___x_8657_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8657_, 0, v___x_8655_);
    lean_ctor_set(v___x_8657_, 1, v___x_8656_);
    v___x_8658_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8658_, 0, v___x_8657_);
    v___x_8659_ = lean_array_push(v_eqs_8639_, v___x_8658_);
    v___x_8660_ = lean_array_push(v_hyps_8640_, v_b_8646_);
    v___x_8661_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(
        v_subsingletonInstImplicitRhs_8641_,
        v_f_8642_,
        v_info_8643_,
        v_kinds_8644_,
        v_lhss_8645_,
        v___x_8653_,
        v___x_8654_,
        v___x_8659_,
        v___x_8660_,
        v___y_8647_,
        v___y_8648_,
        v___y_8649_,
        v___y_8650_,
    );
    return v___x_8661_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(
    mut v_i_8662_: *mut LeanObject,
    mut v_rhss_8663_: *mut LeanObject,
    mut v_lhs_8664_: *mut LeanObject,
    mut v_eqs_8665_: *mut LeanObject,
    mut v_hyps_8666_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8667_: *mut LeanObject,
    mut v_f_8668_: *mut LeanObject,
    mut v_info_8669_: *mut LeanObject,
    mut v_kinds_8670_: *mut LeanObject,
    mut v_lhss_8671_: *mut LeanObject,
    mut v_b_8672_: *mut LeanObject,
    mut v___y_8673_: *mut LeanObject,
    mut v___y_8674_: *mut LeanObject,
    mut v___y_8675_: *mut LeanObject,
    mut v___y_8676_: *mut LeanObject,
    mut v___y_8677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_8678_: u8 = 0;
    let mut v_res_8679_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_8678_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_8667_) as u8);
    v_res_8679_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_8662_, v_rhss_8663_, v_lhs_8664_, v_eqs_8665_, v_hyps_8666_, v_subsingletonInstImplicitRhs_boxed_8678_, v_f_8668_, v_info_8669_, v_kinds_8670_, v_lhss_8671_, v_b_8672_, v___y_8673_, v___y_8674_, v___y_8675_, v___y_8676_);
    lean_dec(v___y_8676_);
    lean_dec_ref(v___y_8675_);
    lean_dec(v___y_8674_);
    lean_dec_ref(v___y_8673_);
    lean_dec_ref(v_lhs_8664_);
    lean_dec(v_i_8662_);
    return v_res_8679_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(
    mut v_i_8680_: *mut LeanObject,
    mut v_rhss_8681_: *mut LeanObject,
    mut v_lhs_8682_: *mut LeanObject,
    mut v_eqs_8683_: *mut LeanObject,
    mut v_hyps_8684_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8685_: u8,
    mut v_f_8686_: *mut LeanObject,
    mut v_info_8687_: *mut LeanObject,
    mut v_kinds_8688_: *mut LeanObject,
    mut v_lhss_8689_: *mut LeanObject,
    mut v_name_8690_: *mut LeanObject,
    mut v_bi_8691_: u8,
    mut v_type_8692_: *mut LeanObject,
    mut v_kind_8693_: u8,
    mut v___y_8694_: *mut LeanObject,
    mut v___y_8695_: *mut LeanObject,
    mut v___y_8696_: *mut LeanObject,
    mut v___y_8697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8705_: u8 = 0;
    let mut v___x_8707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8709_: u8 = 0;
    let mut v_a_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8713_: u8 = 0;
    let mut v___x_8715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8699_ = lean_box((v_subsingletonInstImplicitRhs_8685_) as usize);
                v___f_8700_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed as *mut core::ffi::c_void, 16, 10);
                lean_closure_set(v___f_8700_, 0, v_i_8680_);
                lean_closure_set(v___f_8700_, 1, v_rhss_8681_);
                lean_closure_set(v___f_8700_, 2, v_lhs_8682_);
                lean_closure_set(v___f_8700_, 3, v_eqs_8683_);
                lean_closure_set(v___f_8700_, 4, v_hyps_8684_);
                lean_closure_set(v___f_8700_, 5, v___x_8699_);
                lean_closure_set(v___f_8700_, 6, v_f_8686_);
                lean_closure_set(v___f_8700_, 7, v_info_8687_);
                lean_closure_set(v___f_8700_, 8, v_kinds_8688_);
                lean_closure_set(v___f_8700_, 9, v_lhss_8689_);
                v___x_8701_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_8690_,
                    v_bi_8691_,
                    v_type_8692_,
                    v___f_8700_,
                    v_kind_8693_,
                    v___y_8694_,
                    v___y_8695_,
                    v___y_8696_,
                    v___y_8697_,
                );
                if lean_obj_tag(v___x_8701_) == 0 {
                    v_a_8702_ = lean_ctor_get(v___x_8701_, 0);
                    v_isSharedCheck_8709_ = (!lean_is_exclusive(v___x_8701_)) as u8;
                    if v_isSharedCheck_8709_ == 0 {
                        v___x_8704_ = v___x_8701_;
                        v_isShared_8705_ = v_isSharedCheck_8709_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8702_);
                        lean_dec(v___x_8701_);
                        v___x_8704_ = lean_box(0);
                        v_isShared_8705_ = v_isSharedCheck_8709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8710_ = lean_ctor_get(v___x_8701_, 0);
                    v_isSharedCheck_8717_ = (!lean_is_exclusive(v___x_8701_)) as u8;
                    if v_isSharedCheck_8717_ == 0 {
                        v___x_8712_ = v___x_8701_;
                        v_isShared_8713_ = v_isSharedCheck_8717_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8710_);
                        lean_dec(v___x_8701_);
                        v___x_8712_ = lean_box(0);
                        v_isShared_8713_ = v_isSharedCheck_8717_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8705_ == 0 {
                    v___x_8707_ = v___x_8704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8708_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8708_, 0, v_a_8702_);
                    v___x_8707_ = v_reuseFailAlloc_8708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8707_;
            }
            3 => {
                if v_isShared_8713_ == 0 {
                    v___x_8715_ = v___x_8712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8716_, 0, v_a_8710_);
                    v___x_8715_ = v_reuseFailAlloc_8716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(
    mut v_lhs_8718_: *mut LeanObject,
    mut v_rhss_8719_: *mut LeanObject,
    mut v_lhss_8720_: *mut LeanObject,
    mut v_i_8721_: *mut LeanObject,
    mut v_eqs_8722_: *mut LeanObject,
    mut v_hyps_8723_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8724_: u8,
    mut v_f_8725_: *mut LeanObject,
    mut v_info_8726_: *mut LeanObject,
    mut v_kinds_8727_: *mut LeanObject,
    mut v___y_8728_: *mut LeanObject,
    mut v___y_8729_: *mut LeanObject,
    mut v___y_8730_: *mut LeanObject,
    mut v___y_8731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8741_: u8 = 0;
    let mut v___x_8742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8746_: u8 = 0;
    let mut v___x_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8751_: u8 = 0;
    let mut v___x_8753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8755_: u8 = 0;
    let mut v___x_8756_: u8 = 0;
    let mut v___x_8757_: u8 = 0;
    let mut v_a_8758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8761_: u8 = 0;
    let mut v___x_8763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_8731_);
                lean_inc_ref(v___y_8730_);
                lean_inc(v___y_8729_);
                lean_inc_ref(v___y_8728_);
                lean_inc_ref(v_lhs_8718_);
                v___x_8733_ = lean_infer_type(
                    v_lhs_8718_,
                    v___y_8728_,
                    v___y_8729_,
                    v___y_8730_,
                    v___y_8731_,
                );
                if lean_obj_tag(v___x_8733_) == 0 {
                    v_a_8734_ = lean_ctor_get(v___x_8733_, 0);
                    lean_inc(v_a_8734_);
                    lean_dec_ref_known(v___x_8733_, 1);
                    v___x_8735_ = lean_array_get_size(v_rhss_8719_);
                    v___x_8736_ = lean_unsigned_to_nat(0);
                    lean_inc_ref(v_lhss_8720_);
                    v___x_8737_ =
                        l_Array_toSubarray___redArg(v_lhss_8720_, v___x_8736_, v___x_8735_);
                    v___x_8738_ = l_Subarray_copy___redArg(v___x_8737_);
                    v___x_8739_ = l_Lean_Expr_replaceFVars(v_a_8734_, v___x_8738_, v_rhss_8719_);
                    lean_dec_ref(v___x_8738_);
                    lean_dec(v_a_8734_);
                    if v_subsingletonInstImplicitRhs_8724_ == 0 {
                        v___x_8756_ = 1;
                        v___y_8741_ = v___x_8756_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8757_ = 3;
                        v___y_8741_ = v___x_8757_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_8731_);
                    lean_dec_ref(v___y_8730_);
                    lean_dec(v___y_8729_);
                    lean_dec_ref(v___y_8728_);
                    lean_dec_ref(v_kinds_8727_);
                    lean_dec_ref(v_info_8726_);
                    lean_dec_ref(v_f_8725_);
                    lean_dec_ref(v_hyps_8723_);
                    lean_dec_ref(v_eqs_8722_);
                    lean_dec(v_i_8721_);
                    lean_dec_ref(v_lhss_8720_);
                    lean_dec_ref(v_rhss_8719_);
                    lean_dec_ref(v_lhs_8718_);
                    v_a_8758_ = lean_ctor_get(v___x_8733_, 0);
                    v_isSharedCheck_8765_ = (!lean_is_exclusive(v___x_8733_)) as u8;
                    if v_isSharedCheck_8765_ == 0 {
                        v___x_8760_ = v___x_8733_;
                        v_isShared_8761_ = v_isSharedCheck_8765_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8758_);
                        lean_dec(v___x_8733_);
                        v___x_8760_ = lean_box(0);
                        v_isShared_8761_ = v_isSharedCheck_8765_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8742_ = l_Lean_Expr_fvarId_x21(v_lhs_8718_);
                v___x_8743_ = l_Lean_FVarId_getDecl___redArg(
                    v___x_8742_,
                    v___y_8728_,
                    v___y_8730_,
                    v___y_8731_,
                );
                if lean_obj_tag(v___x_8743_) == 0 {
                    v_a_8744_ = lean_ctor_get(v___x_8743_, 0);
                    lean_inc(v_a_8744_);
                    lean_dec_ref_known(v___x_8743_, 1);
                    v___x_8745_ = l_Lean_LocalDecl_userName(v_a_8744_);
                    lean_dec(v_a_8744_);
                    v___x_8746_ = 0;
                    v___x_8747_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_8721_, v_rhss_8719_, v_lhs_8718_, v_eqs_8722_, v_hyps_8723_, v_subsingletonInstImplicitRhs_8724_, v_f_8725_, v_info_8726_, v_kinds_8727_, v_lhss_8720_, v___x_8745_, v___y_8741_, v___x_8739_, v___x_8746_, v___y_8728_, v___y_8729_, v___y_8730_, v___y_8731_);
                    lean_dec(v___y_8731_);
                    lean_dec_ref(v___y_8730_);
                    lean_dec(v___y_8729_);
                    lean_dec_ref(v___y_8728_);
                    return v___x_8747_;
                } else {
                    lean_dec_ref(v___x_8739_);
                    lean_dec(v___y_8731_);
                    lean_dec_ref(v___y_8730_);
                    lean_dec(v___y_8729_);
                    lean_dec_ref(v___y_8728_);
                    lean_dec_ref(v_kinds_8727_);
                    lean_dec_ref(v_info_8726_);
                    lean_dec_ref(v_f_8725_);
                    lean_dec_ref(v_hyps_8723_);
                    lean_dec_ref(v_eqs_8722_);
                    lean_dec(v_i_8721_);
                    lean_dec_ref(v_lhss_8720_);
                    lean_dec_ref(v_rhss_8719_);
                    lean_dec_ref(v_lhs_8718_);
                    v_a_8748_ = lean_ctor_get(v___x_8743_, 0);
                    v_isSharedCheck_8755_ = (!lean_is_exclusive(v___x_8743_)) as u8;
                    if v_isSharedCheck_8755_ == 0 {
                        v___x_8750_ = v___x_8743_;
                        v_isShared_8751_ = v_isSharedCheck_8755_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8748_);
                        lean_dec(v___x_8743_);
                        v___x_8750_ = lean_box(0);
                        v_isShared_8751_ = v_isSharedCheck_8755_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8751_ == 0 {
                    v___x_8753_ = v___x_8750_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8754_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8754_, 0, v_a_8748_);
                    v___x_8753_ = v_reuseFailAlloc_8754_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8753_;
            }
            4 => {
                if v_isShared_8761_ == 0 {
                    v___x_8763_ = v___x_8760_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8764_, 0, v_a_8758_);
                    v___x_8763_ = v_reuseFailAlloc_8764_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8763_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(
    mut v_lhs_8766_: *mut LeanObject,
    mut v_rhss_8767_: *mut LeanObject,
    mut v_lhss_8768_: *mut LeanObject,
    mut v_i_8769_: *mut LeanObject,
    mut v_eqs_8770_: *mut LeanObject,
    mut v_hyps_8771_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8772_: *mut LeanObject,
    mut v_f_8773_: *mut LeanObject,
    mut v_info_8774_: *mut LeanObject,
    mut v_kinds_8775_: *mut LeanObject,
    mut v___y_8776_: *mut LeanObject,
    mut v___y_8777_: *mut LeanObject,
    mut v___y_8778_: *mut LeanObject,
    mut v___y_8779_: *mut LeanObject,
    mut v___y_8780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_8781_: u8 = 0;
    let mut v_res_8782_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_8781_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_8772_) as u8);
    v_res_8782_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(
            v_lhs_8766_,
            v_rhss_8767_,
            v_lhss_8768_,
            v_i_8769_,
            v_eqs_8770_,
            v_hyps_8771_,
            v_subsingletonInstImplicitRhs_boxed_8781_,
            v_f_8773_,
            v_info_8774_,
            v_kinds_8775_,
            v___y_8776_,
            v___y_8777_,
            v___y_8778_,
            v___y_8779_,
        );
    return v_res_8782_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1()
-> *mut LeanObject {
    let mut v___x_8784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8789_: *mut LeanObject = core::ptr::null_mut();
    v___x_8784_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2;
    v___x_8785_ = lean_unsigned_to_nat(38);
    v___x_8786_ = lean_unsigned_to_nat(328);
    v___x_8787_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0;
    v___x_8788_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0;
    v___x_8789_ = l_mkPanicMessageWithDecl(
        v___x_8788_,
        v___x_8787_,
        v___x_8786_,
        v___x_8785_,
        v___x_8784_,
    );
    return v___x_8789_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(
    mut v_subsingletonInstImplicitRhs_8790_: u8,
    mut v_f_8791_: *mut LeanObject,
    mut v_info_8792_: *mut LeanObject,
    mut v_kinds_8793_: *mut LeanObject,
    mut v_lhss_8794_: *mut LeanObject,
    mut v_i_8795_: *mut LeanObject,
    mut v_rhss_8796_: *mut LeanObject,
    mut v_eqs_8797_: *mut LeanObject,
    mut v_hyps_8798_: *mut LeanObject,
    mut v_a_8799_: *mut LeanObject,
    mut v_a_8800_: *mut LeanObject,
    mut v_a_8801_: *mut LeanObject,
    mut v_a_8802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8805_: u8 = 0;
    let mut v___x_8806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_8807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_8808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8809_: u8 = 0;
    let mut v___x_8810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8812_: u8 = 0;
    let mut v___x_8813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8823_: u8 = 0;
    let mut v___x_8824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8825_: u8 = 0;
    let mut v___x_8826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8830_: u8 = 0;
    let mut v___x_8832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8834_: u8 = 0;
    let mut v___x_8835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_8837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backDeps_8840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8858_: u8 = 0;
    let mut v___x_8860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8862_: u8 = 0;
    let mut v_a_8863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8866_: u8 = 0;
    let mut v___x_8868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8870_: u8 = 0;
    let mut v___x_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_8879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_8880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8883_: u8 = 0;
    let mut v___x_8884_: u8 = 0;
    let mut v___x_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8891_: u8 = 0;
    let mut v___x_8892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8896_: u8 = 0;
    let mut v_a_8897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8900_: u8 = 0;
    let mut v___x_8902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8904_: u8 = 0;
    let mut v_a_8905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8908_: u8 = 0;
    let mut v___x_8910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8912_: u8 = 0;
    let mut v_a_8913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8916_: u8 = 0;
    let mut v___x_8918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8804_ = lean_array_get_size(v_kinds_8793_);
                v___x_8805_ = lean_nat_dec_eq(v_i_8795_, v___x_8804_);
                if v___x_8805_ == 0 {
                    v___x_8806_ = l_Lean_instInhabitedExpr;
                    v_lhs_8807_ = lean_array_get_borrowed(v___x_8806_, v_lhss_8794_, v_i_8795_);
                    lean_inc(v_lhs_8807_);
                    v_hyps_8808_ = lean_array_push(v_hyps_8798_, v_lhs_8807_);
                    v___x_8809_ = 0;
                    v___x_8810_ = lean_box((v___x_8809_) as usize);
                    v___x_8811_ = lean_array_get(v___x_8810_, v_kinds_8793_, v_i_8795_);
                    lean_dec(v___x_8810_);
                    v___x_8812_ = (lean_unbox(v___x_8811_) as u8);
                    lean_dec(v___x_8811_);
                    match v___x_8812_ {
                        0 => {
                            v___x_8813_ = lean_unsigned_to_nat(1);
                            v___x_8814_ = lean_nat_add(v_i_8795_, v___x_8813_);
                            lean_dec(v_i_8795_);
                            lean_inc(v_lhs_8807_);
                            v___x_8815_ = lean_array_push(v_rhss_8796_, v_lhs_8807_);
                            v___x_8816_ = lean_box(0);
                            v___x_8817_ = lean_array_push(v_eqs_8797_, v___x_8816_);
                            v_i_8795_ = v___x_8814_;
                            v_rhss_8796_ = v___x_8815_;
                            v_eqs_8797_ = v___x_8817_;
                            v_hyps_8798_ = v_hyps_8808_;
                            state = 0;
                            continue;
                        }
                        2 => {
                            lean_inc(v_lhs_8807_);
                            v___x_8819_ = l_Lean_Expr_fvarId_x21(v_lhs_8807_);
                            v___x_8820_ = l_Lean_FVarId_getDecl___redArg(
                                v___x_8819_,
                                v_a_8799_,
                                v_a_8801_,
                                v_a_8802_,
                            );
                            if lean_obj_tag(v___x_8820_) == 0 {
                                v_a_8821_ = lean_ctor_get(v___x_8820_, 0);
                                lean_inc(v_a_8821_);
                                lean_dec_ref_known(v___x_8820_, 1);
                                v___x_8822_ = l_Lean_LocalDecl_userName(v_a_8821_);
                                v___x_8823_ = l_Lean_LocalDecl_binderInfo(v_a_8821_);
                                v___x_8824_ = l_Lean_LocalDecl_type(v_a_8821_);
                                lean_dec(v_a_8821_);
                                v___x_8825_ = 0;
                                lean_inc(v___x_8822_);
                                v___x_8826_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_8795_, v_rhss_8796_, v_eqs_8797_, v_hyps_8808_, v_subsingletonInstImplicitRhs_8790_, v_f_8791_, v_info_8792_, v_kinds_8793_, v_lhss_8794_, v_lhs_8807_, v___x_8822_, v___x_8822_, v___x_8823_, v___x_8824_, v___x_8825_, v_a_8799_, v_a_8800_, v_a_8801_, v_a_8802_);
                                return v___x_8826_;
                            } else {
                                lean_dec_ref(v_hyps_8808_);
                                lean_dec(v_lhs_8807_);
                                lean_dec_ref(v_eqs_8797_);
                                lean_dec_ref(v_rhss_8796_);
                                lean_dec(v_i_8795_);
                                lean_dec_ref(v_lhss_8794_);
                                lean_dec_ref(v_kinds_8793_);
                                lean_dec_ref(v_info_8792_);
                                lean_dec_ref(v_f_8791_);
                                v_a_8827_ = lean_ctor_get(v___x_8820_, 0);
                                v_isSharedCheck_8834_ = (!lean_is_exclusive(v___x_8820_)) as u8;
                                if v_isSharedCheck_8834_ == 0 {
                                    v___x_8829_ = v___x_8820_;
                                    v_isShared_8830_ = v_isSharedCheck_8834_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_8827_);
                                    lean_dec(v___x_8820_);
                                    v___x_8829_ = lean_box(0);
                                    v_isShared_8830_ = v_isSharedCheck_8834_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        3 => {
                            lean_inc(v_a_8802_);
                            lean_inc_ref(v_a_8801_);
                            lean_inc(v_a_8800_);
                            lean_inc_ref(v_a_8799_);
                            lean_inc(v_lhs_8807_);
                            v___x_8835_ = lean_infer_type(
                                v_lhs_8807_,
                                v_a_8799_,
                                v_a_8800_,
                                v_a_8801_,
                                v_a_8802_,
                            );
                            if lean_obj_tag(v___x_8835_) == 0 {
                                v_a_8836_ = lean_ctor_get(v___x_8835_, 0);
                                lean_inc(v_a_8836_);
                                lean_dec_ref_known(v___x_8835_, 1);
                                v_paramInfo_8837_ = lean_ctor_get(v_info_8792_, 0);
                                v___x_8838_ = l_Lean_Meta_instInhabitedParamInfo_default;
                                v___x_8839_ = lean_array_get_borrowed(
                                    v___x_8838_,
                                    v_paramInfo_8837_,
                                    v_i_8795_,
                                );
                                v_backDeps_8840_ = lean_ctor_get(v___x_8839_, 0);
                                v___x_8841_ = lean_array_get_size(v_rhss_8796_);
                                v___x_8842_ = lean_unsigned_to_nat(0);
                                lean_inc_ref(v_lhss_8794_);
                                v___x_8843_ = l_Array_toSubarray___redArg(
                                    v_lhss_8794_,
                                    v___x_8842_,
                                    v___x_8841_,
                                );
                                v___x_8844_ = l_Subarray_copy___redArg(v___x_8843_);
                                v___x_8845_ =
                                    l_Lean_Expr_replaceFVars(v_a_8836_, v___x_8844_, v_rhss_8796_);
                                lean_dec_ref(v___x_8844_);
                                lean_dec(v_a_8836_);
                                v___x_8846_ = l_Lean_Expr_fvarId_x21(v_lhs_8807_);
                                v___x_8847_ =
                                    l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(
                                        v___x_8846_,
                                        v___x_8845_,
                                        v_backDeps_8840_,
                                        v_eqs_8797_,
                                        v_a_8799_,
                                        v_a_8800_,
                                        v_a_8801_,
                                        v_a_8802_,
                                    );
                                if lean_obj_tag(v___x_8847_) == 0 {
                                    v_a_8848_ = lean_ctor_get(v___x_8847_, 0);
                                    lean_inc(v_a_8848_);
                                    lean_dec_ref_known(v___x_8847_, 1);
                                    v___x_8849_ = lean_unsigned_to_nat(1);
                                    v___x_8850_ = lean_nat_add(v_i_8795_, v___x_8849_);
                                    lean_dec(v_i_8795_);
                                    v___x_8851_ = lean_array_push(v_rhss_8796_, v_a_8848_);
                                    v___x_8852_ = lean_box(0);
                                    v___x_8853_ = lean_array_push(v_eqs_8797_, v___x_8852_);
                                    v_i_8795_ = v___x_8850_;
                                    v_rhss_8796_ = v___x_8851_;
                                    v_eqs_8797_ = v___x_8853_;
                                    v_hyps_8798_ = v_hyps_8808_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_hyps_8808_);
                                    lean_dec_ref(v_eqs_8797_);
                                    lean_dec_ref(v_rhss_8796_);
                                    lean_dec(v_i_8795_);
                                    lean_dec_ref(v_lhss_8794_);
                                    lean_dec_ref(v_kinds_8793_);
                                    lean_dec_ref(v_info_8792_);
                                    lean_dec_ref(v_f_8791_);
                                    v_a_8855_ = lean_ctor_get(v___x_8847_, 0);
                                    v_isSharedCheck_8862_ = (!lean_is_exclusive(v___x_8847_)) as u8;
                                    if v_isSharedCheck_8862_ == 0 {
                                        v___x_8857_ = v___x_8847_;
                                        v_isShared_8858_ = v_isSharedCheck_8862_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_8855_);
                                        lean_dec(v___x_8847_);
                                        v___x_8857_ = lean_box(0);
                                        v_isShared_8858_ = v_isSharedCheck_8862_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_hyps_8808_);
                                lean_dec_ref(v_eqs_8797_);
                                lean_dec_ref(v_rhss_8796_);
                                lean_dec(v_i_8795_);
                                lean_dec_ref(v_lhss_8794_);
                                lean_dec_ref(v_kinds_8793_);
                                lean_dec_ref(v_info_8792_);
                                lean_dec_ref(v_f_8791_);
                                v_a_8863_ = lean_ctor_get(v___x_8835_, 0);
                                v_isSharedCheck_8870_ = (!lean_is_exclusive(v___x_8835_)) as u8;
                                if v_isSharedCheck_8870_ == 0 {
                                    v___x_8865_ = v___x_8835_;
                                    v_isShared_8866_ = v_isSharedCheck_8870_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_8863_);
                                    lean_dec(v___x_8835_);
                                    v___x_8865_ = lean_box(0);
                                    v_isShared_8866_ = v_isSharedCheck_8870_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                        5 => {
                            lean_inc_n(v_lhs_8807_, 2);
                            v___x_8871_ = lean_box((v_subsingletonInstImplicitRhs_8790_) as usize);
                            v___f_8872_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed as *mut core::ffi::c_void, 15, 10);
                            lean_closure_set(v___f_8872_, 0, v_lhs_8807_);
                            lean_closure_set(v___f_8872_, 1, v_rhss_8796_);
                            lean_closure_set(v___f_8872_, 2, v_lhss_8794_);
                            lean_closure_set(v___f_8872_, 3, v_i_8795_);
                            lean_closure_set(v___f_8872_, 4, v_eqs_8797_);
                            lean_closure_set(v___f_8872_, 5, v_hyps_8808_);
                            lean_closure_set(v___f_8872_, 6, v___x_8871_);
                            lean_closure_set(v___f_8872_, 7, v_f_8791_);
                            lean_closure_set(v___f_8872_, 8, v_info_8792_);
                            lean_closure_set(v___f_8872_, 9, v_kinds_8793_);
                            v___x_8873_ = lean_unsigned_to_nat(1);
                            v___x_8874_ = lean_mk_empty_array_with_capacity(v___x_8873_);
                            v___x_8875_ = lean_array_push(v___x_8874_, v_lhs_8807_);
                            v___x_8876_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v___x_8875_, v___f_8872_, v_a_8799_, v_a_8800_, v_a_8801_, v_a_8802_);
                            return v___x_8876_;
                        }
                        _ => {
                            lean_dec_ref(v_hyps_8808_);
                            lean_dec_ref(v_eqs_8797_);
                            lean_dec_ref(v_rhss_8796_);
                            lean_dec(v_i_8795_);
                            lean_dec_ref(v_lhss_8794_);
                            lean_dec_ref(v_kinds_8793_);
                            lean_dec_ref(v_info_8792_);
                            lean_dec_ref(v_f_8791_);
                            v___x_8877_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
                            v___x_8878_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v___x_8877_, v_a_8799_, v_a_8800_, v_a_8801_, v_a_8802_);
                            return v___x_8878_;
                        }
                    }
                } else {
                    lean_dec_ref(v_eqs_8797_);
                    lean_dec(v_i_8795_);
                    lean_dec_ref(v_info_8792_);
                    lean_inc_ref(v_f_8791_);
                    v_lhs_8879_ = l_Lean_mkAppN(v_f_8791_, v_lhss_8794_);
                    lean_dec_ref(v_lhss_8794_);
                    v_rhs_8880_ = l_Lean_mkAppN(v_f_8791_, v_rhss_8796_);
                    lean_dec_ref(v_rhss_8796_);
                    v___x_8881_ = l_Lean_Meta_mkEq(
                        v_lhs_8879_,
                        v_rhs_8880_,
                        v_a_8799_,
                        v_a_8800_,
                        v_a_8801_,
                        v_a_8802_,
                    );
                    if lean_obj_tag(v___x_8881_) == 0 {
                        v_a_8882_ = lean_ctor_get(v___x_8881_, 0);
                        lean_inc(v_a_8882_);
                        lean_dec_ref_known(v___x_8881_, 1);
                        v___x_8883_ = 0;
                        v___x_8884_ = 1;
                        v___x_8885_ = l_Lean_Meta_mkForallFVars(
                            v_hyps_8798_,
                            v_a_8882_,
                            v___x_8883_,
                            v___x_8805_,
                            v___x_8805_,
                            v___x_8884_,
                            v_a_8799_,
                            v_a_8800_,
                            v_a_8801_,
                            v_a_8802_,
                        );
                        lean_dec_ref(v_hyps_8798_);
                        if lean_obj_tag(v___x_8885_) == 0 {
                            v_a_8886_ = lean_ctor_get(v___x_8885_, 0);
                            lean_inc_n(v_a_8886_, 2);
                            lean_dec_ref_known(v___x_8885_, 1);
                            lean_inc_ref(v_kinds_8793_);
                            v___x_8887_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_8886_, v_kinds_8793_, v_a_8799_, v_a_8800_, v_a_8801_, v_a_8802_);
                            if lean_obj_tag(v___x_8887_) == 0 {
                                v_a_8888_ = lean_ctor_get(v___x_8887_, 0);
                                v_isSharedCheck_8896_ = (!lean_is_exclusive(v___x_8887_)) as u8;
                                if v_isSharedCheck_8896_ == 0 {
                                    v___x_8890_ = v___x_8887_;
                                    v_isShared_8891_ = v_isSharedCheck_8896_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_8888_);
                                    lean_dec(v___x_8887_);
                                    v___x_8890_ = lean_box(0);
                                    v_isShared_8891_ = v_isSharedCheck_8896_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_8886_);
                                lean_dec_ref(v_kinds_8793_);
                                v_a_8897_ = lean_ctor_get(v___x_8887_, 0);
                                v_isSharedCheck_8904_ = (!lean_is_exclusive(v___x_8887_)) as u8;
                                if v_isSharedCheck_8904_ == 0 {
                                    v___x_8899_ = v___x_8887_;
                                    v_isShared_8900_ = v_isSharedCheck_8904_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_8897_);
                                    lean_dec(v___x_8887_);
                                    v___x_8899_ = lean_box(0);
                                    v_isShared_8900_ = v_isSharedCheck_8904_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_kinds_8793_);
                            v_a_8905_ = lean_ctor_get(v___x_8885_, 0);
                            v_isSharedCheck_8912_ = (!lean_is_exclusive(v___x_8885_)) as u8;
                            if v_isSharedCheck_8912_ == 0 {
                                v___x_8907_ = v___x_8885_;
                                v_isShared_8908_ = v_isSharedCheck_8912_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_8905_);
                                lean_dec(v___x_8885_);
                                v___x_8907_ = lean_box(0);
                                v_isShared_8908_ = v_isSharedCheck_8912_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_hyps_8798_);
                        lean_dec_ref(v_kinds_8793_);
                        v_a_8913_ = lean_ctor_get(v___x_8881_, 0);
                        v_isSharedCheck_8920_ = (!lean_is_exclusive(v___x_8881_)) as u8;
                        if v_isSharedCheck_8920_ == 0 {
                            v___x_8915_ = v___x_8881_;
                            v_isShared_8916_ = v_isSharedCheck_8920_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_8913_);
                            lean_dec(v___x_8881_);
                            v___x_8915_ = lean_box(0);
                            v_isShared_8916_ = v_isSharedCheck_8920_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8830_ == 0 {
                    v___x_8832_ = v___x_8829_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8833_, 0, v_a_8827_);
                    v___x_8832_ = v_reuseFailAlloc_8833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8832_;
            }
            3 => {
                if v_isShared_8858_ == 0 {
                    v___x_8860_ = v___x_8857_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8861_, 0, v_a_8855_);
                    v___x_8860_ = v_reuseFailAlloc_8861_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8860_;
            }
            5 => {
                if v_isShared_8866_ == 0 {
                    v___x_8868_ = v___x_8865_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8869_, 0, v_a_8863_);
                    v___x_8868_ = v_reuseFailAlloc_8869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8868_;
            }
            7 => {
                v___x_8892_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_8892_, 0, v_a_8886_);
                lean_ctor_set(v___x_8892_, 1, v_a_8888_);
                lean_ctor_set(v___x_8892_, 2, v_kinds_8793_);
                if v_isShared_8891_ == 0 {
                    lean_ctor_set(v___x_8890_, 0, v___x_8892_);
                    v___x_8894_ = v___x_8890_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8895_, 0, v___x_8892_);
                    v___x_8894_ = v_reuseFailAlloc_8895_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8894_;
            }
            9 => {
                if v_isShared_8900_ == 0 {
                    v___x_8902_ = v___x_8899_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8903_, 0, v_a_8897_);
                    v___x_8902_ = v_reuseFailAlloc_8903_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8902_;
            }
            11 => {
                if v_isShared_8908_ == 0 {
                    v___x_8910_ = v___x_8907_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8911_, 0, v_a_8905_);
                    v___x_8910_ = v_reuseFailAlloc_8911_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8910_;
            }
            13 => {
                if v_isShared_8916_ == 0 {
                    v___x_8918_ = v___x_8915_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_8919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8919_, 0, v_a_8913_);
                    v___x_8918_ = v_reuseFailAlloc_8919_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_8918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(
    mut v_i_8921_: *mut LeanObject,
    mut v_rhss_8922_: *mut LeanObject,
    mut v_b_8923_: *mut LeanObject,
    mut v_eqs_8924_: *mut LeanObject,
    mut v_hyps_8925_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8926_: u8,
    mut v_f_8927_: *mut LeanObject,
    mut v_info_8928_: *mut LeanObject,
    mut v_kinds_8929_: *mut LeanObject,
    mut v_lhss_8930_: *mut LeanObject,
    mut v_eq_8931_: *mut LeanObject,
    mut v___y_8932_: *mut LeanObject,
    mut v___y_8933_: *mut LeanObject,
    mut v___y_8934_: *mut LeanObject,
    mut v___y_8935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8946_: *mut LeanObject = core::ptr::null_mut();
    v___x_8937_ = lean_unsigned_to_nat(1);
    v___x_8938_ = lean_nat_add(v_i_8921_, v___x_8937_);
    lean_inc_ref(v_b_8923_);
    v___x_8939_ = lean_array_push(v_rhss_8922_, v_b_8923_);
    v___x_8940_ = l_Lean_Expr_fvarId_x21(v_eq_8931_);
    v___x_8941_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8941_, 0, v___x_8940_);
    v___x_8942_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8942_, 0, v___x_8941_);
    v___x_8943_ = lean_array_push(v_eqs_8924_, v___x_8942_);
    v___x_8944_ = lean_array_push(v_hyps_8925_, v_b_8923_);
    v___x_8945_ = lean_array_push(v___x_8944_, v_eq_8931_);
    v___x_8946_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(
        v_subsingletonInstImplicitRhs_8926_,
        v_f_8927_,
        v_info_8928_,
        v_kinds_8929_,
        v_lhss_8930_,
        v___x_8938_,
        v___x_8939_,
        v___x_8943_,
        v___x_8945_,
        v___y_8932_,
        v___y_8933_,
        v___y_8934_,
        v___y_8935_,
    );
    return v___x_8946_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(
    mut v_i_8947_: *mut LeanObject,
    mut v_rhss_8948_: *mut LeanObject,
    mut v_b_8949_: *mut LeanObject,
    mut v_eqs_8950_: *mut LeanObject,
    mut v_hyps_8951_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8952_: *mut LeanObject,
    mut v_f_8953_: *mut LeanObject,
    mut v_info_8954_: *mut LeanObject,
    mut v_kinds_8955_: *mut LeanObject,
    mut v_lhss_8956_: *mut LeanObject,
    mut v_eq_8957_: *mut LeanObject,
    mut v___y_8958_: *mut LeanObject,
    mut v___y_8959_: *mut LeanObject,
    mut v___y_8960_: *mut LeanObject,
    mut v___y_8961_: *mut LeanObject,
    mut v___y_8962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_8963_: u8 = 0;
    let mut v_res_8964_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_8963_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_8952_) as u8);
    v_res_8964_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_8947_, v_rhss_8948_, v_b_8949_, v_eqs_8950_, v_hyps_8951_, v_subsingletonInstImplicitRhs_boxed_8963_, v_f_8953_, v_info_8954_, v_kinds_8955_, v_lhss_8956_, v_eq_8957_, v___y_8958_, v___y_8959_, v___y_8960_, v___y_8961_);
    lean_dec(v___y_8961_);
    lean_dec_ref(v___y_8960_);
    lean_dec(v___y_8959_);
    lean_dec_ref(v___y_8958_);
    lean_dec(v_i_8947_);
    return v_res_8964_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(
    mut v_lhs_8966_: *mut LeanObject,
    mut v_i_8967_: *mut LeanObject,
    mut v_rhss_8968_: *mut LeanObject,
    mut v_eqs_8969_: *mut LeanObject,
    mut v_hyps_8970_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_8971_: u8,
    mut v_f_8972_: *mut LeanObject,
    mut v_info_8973_: *mut LeanObject,
    mut v_kinds_8974_: *mut LeanObject,
    mut v_lhss_8975_: *mut LeanObject,
    mut v___x_8976_: *mut LeanObject,
    mut v_b_8977_: *mut LeanObject,
    mut v___y_8978_: *mut LeanObject,
    mut v___y_8979_: *mut LeanObject,
    mut v___y_8980_: *mut LeanObject,
    mut v___y_8981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8993_: u8 = 0;
    let mut v___x_8995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_b_8977_);
                v___x_8983_ = l_Lean_Meta_mkEq(
                    v_lhs_8966_,
                    v_b_8977_,
                    v___y_8978_,
                    v___y_8979_,
                    v___y_8980_,
                    v___y_8981_,
                );
                if lean_obj_tag(v___x_8983_) == 0 {
                    v_a_8984_ = lean_ctor_get(v___x_8983_, 0);
                    lean_inc(v_a_8984_);
                    lean_dec_ref_known(v___x_8983_, 1);
                    v___x_8985_ = lean_box((v_subsingletonInstImplicitRhs_8971_) as usize);
                    v___f_8986_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed as *mut core::ffi::c_void, 16, 10);
                    lean_closure_set(v___f_8986_, 0, v_i_8967_);
                    lean_closure_set(v___f_8986_, 1, v_rhss_8968_);
                    lean_closure_set(v___f_8986_, 2, v_b_8977_);
                    lean_closure_set(v___f_8986_, 3, v_eqs_8969_);
                    lean_closure_set(v___f_8986_, 4, v_hyps_8970_);
                    lean_closure_set(v___f_8986_, 5, v___x_8985_);
                    lean_closure_set(v___f_8986_, 6, v_f_8972_);
                    lean_closure_set(v___f_8986_, 7, v_info_8973_);
                    lean_closure_set(v___f_8986_, 8, v_kinds_8974_);
                    lean_closure_set(v___f_8986_, 9, v_lhss_8975_);
                    v___x_8987_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0;
                    v___x_8988_ = lean_name_append_before(v___x_8976_, v___x_8987_);
                    v___x_8989_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_8988_, v_a_8984_, v___f_8986_, v___y_8978_, v___y_8979_, v___y_8980_, v___y_8981_);
                    return v___x_8989_;
                } else {
                    lean_dec_ref(v_b_8977_);
                    lean_dec(v___x_8976_);
                    lean_dec_ref(v_lhss_8975_);
                    lean_dec_ref(v_kinds_8974_);
                    lean_dec_ref(v_info_8973_);
                    lean_dec_ref(v_f_8972_);
                    lean_dec_ref(v_hyps_8970_);
                    lean_dec_ref(v_eqs_8969_);
                    lean_dec_ref(v_rhss_8968_);
                    lean_dec(v_i_8967_);
                    v_a_8990_ = lean_ctor_get(v___x_8983_, 0);
                    v_isSharedCheck_8997_ = (!lean_is_exclusive(v___x_8983_)) as u8;
                    if v_isSharedCheck_8997_ == 0 {
                        v___x_8992_ = v___x_8983_;
                        v_isShared_8993_ = v_isSharedCheck_8997_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8990_);
                        lean_dec(v___x_8983_);
                        v___x_8992_ = lean_box(0);
                        v_isShared_8993_ = v_isSharedCheck_8997_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8993_ == 0 {
                    v___x_8995_ = v___x_8992_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8996_, 0, v_a_8990_);
                    v___x_8995_ = v_reuseFailAlloc_8996_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_8998_: *mut LeanObject = *_args.add(0);
    let mut v_i_8999_: *mut LeanObject = *_args.add(1);
    let mut v_rhss_9000_: *mut LeanObject = *_args.add(2);
    let mut v_eqs_9001_: *mut LeanObject = *_args.add(3);
    let mut v_hyps_9002_: *mut LeanObject = *_args.add(4);
    let mut v_subsingletonInstImplicitRhs_9003_: *mut LeanObject = *_args.add(5);
    let mut v_f_9004_: *mut LeanObject = *_args.add(6);
    let mut v_info_9005_: *mut LeanObject = *_args.add(7);
    let mut v_kinds_9006_: *mut LeanObject = *_args.add(8);
    let mut v_lhss_9007_: *mut LeanObject = *_args.add(9);
    let mut v___x_9008_: *mut LeanObject = *_args.add(10);
    let mut v_b_9009_: *mut LeanObject = *_args.add(11);
    let mut v___y_9010_: *mut LeanObject = *_args.add(12);
    let mut v___y_9011_: *mut LeanObject = *_args.add(13);
    let mut v___y_9012_: *mut LeanObject = *_args.add(14);
    let mut v___y_9013_: *mut LeanObject = *_args.add(15);
    let mut v___y_9014_: *mut LeanObject = *_args.add(16);
    let mut v_subsingletonInstImplicitRhs_boxed_9015_: u8 = 0;
    let mut v_res_9016_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9015_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9003_) as u8);
    v_res_9016_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(v_lhs_8998_, v_i_8999_, v_rhss_9000_, v_eqs_9001_, v_hyps_9002_, v_subsingletonInstImplicitRhs_boxed_9015_, v_f_9004_, v_info_9005_, v_kinds_9006_, v_lhss_9007_, v___x_9008_, v_b_9009_, v___y_9010_, v___y_9011_, v___y_9012_, v___y_9013_);
    lean_dec(v___y_9013_);
    lean_dec_ref(v___y_9012_);
    lean_dec(v___y_9011_);
    lean_dec_ref(v___y_9010_);
    return v_res_9016_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(
    mut v_i_9017_: *mut LeanObject,
    mut v_rhss_9018_: *mut LeanObject,
    mut v_eqs_9019_: *mut LeanObject,
    mut v_hyps_9020_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_9021_: u8,
    mut v_f_9022_: *mut LeanObject,
    mut v_info_9023_: *mut LeanObject,
    mut v_kinds_9024_: *mut LeanObject,
    mut v_lhss_9025_: *mut LeanObject,
    mut v_lhs_9026_: *mut LeanObject,
    mut v___x_9027_: *mut LeanObject,
    mut v_name_9028_: *mut LeanObject,
    mut v_bi_9029_: u8,
    mut v_type_9030_: *mut LeanObject,
    mut v_kind_9031_: u8,
    mut v___y_9032_: *mut LeanObject,
    mut v___y_9033_: *mut LeanObject,
    mut v___y_9034_: *mut LeanObject,
    mut v___y_9035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9043_: u8 = 0;
    let mut v___x_9045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9047_: u8 = 0;
    let mut v_a_9048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9051_: u8 = 0;
    let mut v___x_9053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9037_ = lean_box((v_subsingletonInstImplicitRhs_9021_) as usize);
                v___f_9038_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed as *mut core::ffi::c_void, 17, 11);
                lean_closure_set(v___f_9038_, 0, v_lhs_9026_);
                lean_closure_set(v___f_9038_, 1, v_i_9017_);
                lean_closure_set(v___f_9038_, 2, v_rhss_9018_);
                lean_closure_set(v___f_9038_, 3, v_eqs_9019_);
                lean_closure_set(v___f_9038_, 4, v_hyps_9020_);
                lean_closure_set(v___f_9038_, 5, v___x_9037_);
                lean_closure_set(v___f_9038_, 6, v_f_9022_);
                lean_closure_set(v___f_9038_, 7, v_info_9023_);
                lean_closure_set(v___f_9038_, 8, v_kinds_9024_);
                lean_closure_set(v___f_9038_, 9, v_lhss_9025_);
                lean_closure_set(v___f_9038_, 10, v___x_9027_);
                v___x_9039_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_9028_,
                    v_bi_9029_,
                    v_type_9030_,
                    v___f_9038_,
                    v_kind_9031_,
                    v___y_9032_,
                    v___y_9033_,
                    v___y_9034_,
                    v___y_9035_,
                );
                if lean_obj_tag(v___x_9039_) == 0 {
                    v_a_9040_ = lean_ctor_get(v___x_9039_, 0);
                    v_isSharedCheck_9047_ = (!lean_is_exclusive(v___x_9039_)) as u8;
                    if v_isSharedCheck_9047_ == 0 {
                        v___x_9042_ = v___x_9039_;
                        v_isShared_9043_ = v_isSharedCheck_9047_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9040_);
                        lean_dec(v___x_9039_);
                        v___x_9042_ = lean_box(0);
                        v_isShared_9043_ = v_isSharedCheck_9047_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9048_ = lean_ctor_get(v___x_9039_, 0);
                    v_isSharedCheck_9055_ = (!lean_is_exclusive(v___x_9039_)) as u8;
                    if v_isSharedCheck_9055_ == 0 {
                        v___x_9050_ = v___x_9039_;
                        v_isShared_9051_ = v_isSharedCheck_9055_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9048_);
                        lean_dec(v___x_9039_);
                        v___x_9050_ = lean_box(0);
                        v_isShared_9051_ = v_isSharedCheck_9055_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9043_ == 0 {
                    v___x_9045_ = v___x_9042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9046_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9046_, 0, v_a_9040_);
                    v___x_9045_ = v_reuseFailAlloc_9046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9045_;
            }
            3 => {
                if v_isShared_9051_ == 0 {
                    v___x_9053_ = v___x_9050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9054_, 0, v_a_9048_);
                    v___x_9053_ = v_reuseFailAlloc_9054_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_9056_: *mut LeanObject = *_args.add(0);
    let mut v_rhss_9057_: *mut LeanObject = *_args.add(1);
    let mut v_eqs_9058_: *mut LeanObject = *_args.add(2);
    let mut v_hyps_9059_: *mut LeanObject = *_args.add(3);
    let mut v_subsingletonInstImplicitRhs_9060_: *mut LeanObject = *_args.add(4);
    let mut v_f_9061_: *mut LeanObject = *_args.add(5);
    let mut v_info_9062_: *mut LeanObject = *_args.add(6);
    let mut v_kinds_9063_: *mut LeanObject = *_args.add(7);
    let mut v_lhss_9064_: *mut LeanObject = *_args.add(8);
    let mut v_lhs_9065_: *mut LeanObject = *_args.add(9);
    let mut v___x_9066_: *mut LeanObject = *_args.add(10);
    let mut v_name_9067_: *mut LeanObject = *_args.add(11);
    let mut v_bi_9068_: *mut LeanObject = *_args.add(12);
    let mut v_type_9069_: *mut LeanObject = *_args.add(13);
    let mut v_kind_9070_: *mut LeanObject = *_args.add(14);
    let mut v___y_9071_: *mut LeanObject = *_args.add(15);
    let mut v___y_9072_: *mut LeanObject = *_args.add(16);
    let mut v___y_9073_: *mut LeanObject = *_args.add(17);
    let mut v___y_9074_: *mut LeanObject = *_args.add(18);
    let mut v___y_9075_: *mut LeanObject = *_args.add(19);
    let mut v_subsingletonInstImplicitRhs_boxed_9076_: u8 = 0;
    let mut v_bi_boxed_9077_: u8 = 0;
    let mut v_kind_boxed_9078_: u8 = 0;
    let mut v_res_9079_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9076_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9060_) as u8);
    v_bi_boxed_9077_ = (lean_unbox(v_bi_9068_) as u8);
    v_kind_boxed_9078_ = (lean_unbox(v_kind_9070_) as u8);
    v_res_9079_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_9056_, v_rhss_9057_, v_eqs_9058_, v_hyps_9059_, v_subsingletonInstImplicitRhs_boxed_9076_, v_f_9061_, v_info_9062_, v_kinds_9063_, v_lhss_9064_, v_lhs_9065_, v___x_9066_, v_name_9067_, v_bi_boxed_9077_, v_type_9069_, v_kind_boxed_9078_, v___y_9071_, v___y_9072_, v___y_9073_, v___y_9074_);
    lean_dec(v___y_9074_);
    lean_dec_ref(v___y_9073_);
    lean_dec(v___y_9072_);
    lean_dec_ref(v___y_9071_);
    return v_res_9079_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_9080_: *mut LeanObject = *_args.add(0);
    let mut v_rhss_9081_: *mut LeanObject = *_args.add(1);
    let mut v_lhs_9082_: *mut LeanObject = *_args.add(2);
    let mut v_eqs_9083_: *mut LeanObject = *_args.add(3);
    let mut v_hyps_9084_: *mut LeanObject = *_args.add(4);
    let mut v_subsingletonInstImplicitRhs_9085_: *mut LeanObject = *_args.add(5);
    let mut v_f_9086_: *mut LeanObject = *_args.add(6);
    let mut v_info_9087_: *mut LeanObject = *_args.add(7);
    let mut v_kinds_9088_: *mut LeanObject = *_args.add(8);
    let mut v_lhss_9089_: *mut LeanObject = *_args.add(9);
    let mut v_name_9090_: *mut LeanObject = *_args.add(10);
    let mut v_bi_9091_: *mut LeanObject = *_args.add(11);
    let mut v_type_9092_: *mut LeanObject = *_args.add(12);
    let mut v_kind_9093_: *mut LeanObject = *_args.add(13);
    let mut v___y_9094_: *mut LeanObject = *_args.add(14);
    let mut v___y_9095_: *mut LeanObject = *_args.add(15);
    let mut v___y_9096_: *mut LeanObject = *_args.add(16);
    let mut v___y_9097_: *mut LeanObject = *_args.add(17);
    let mut v___y_9098_: *mut LeanObject = *_args.add(18);
    let mut v_subsingletonInstImplicitRhs_boxed_9099_: u8 = 0;
    let mut v_bi_boxed_9100_: u8 = 0;
    let mut v_kind_boxed_9101_: u8 = 0;
    let mut v_res_9102_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9099_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9085_) as u8);
    v_bi_boxed_9100_ = (lean_unbox(v_bi_9091_) as u8);
    v_kind_boxed_9101_ = (lean_unbox(v_kind_9093_) as u8);
    v_res_9102_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_9080_, v_rhss_9081_, v_lhs_9082_, v_eqs_9083_, v_hyps_9084_, v_subsingletonInstImplicitRhs_boxed_9099_, v_f_9086_, v_info_9087_, v_kinds_9088_, v_lhss_9089_, v_name_9090_, v_bi_boxed_9100_, v_type_9092_, v_kind_boxed_9101_, v___y_9094_, v___y_9095_, v___y_9096_, v___y_9097_);
    lean_dec(v___y_9097_);
    lean_dec_ref(v___y_9096_);
    lean_dec(v___y_9095_);
    lean_dec_ref(v___y_9094_);
    return v_res_9102_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(
    mut v_subsingletonInstImplicitRhs_9103_: *mut LeanObject,
    mut v_f_9104_: *mut LeanObject,
    mut v_info_9105_: *mut LeanObject,
    mut v_kinds_9106_: *mut LeanObject,
    mut v_lhss_9107_: *mut LeanObject,
    mut v_i_9108_: *mut LeanObject,
    mut v_rhss_9109_: *mut LeanObject,
    mut v_eqs_9110_: *mut LeanObject,
    mut v_hyps_9111_: *mut LeanObject,
    mut v_a_9112_: *mut LeanObject,
    mut v_a_9113_: *mut LeanObject,
    mut v_a_9114_: *mut LeanObject,
    mut v_a_9115_: *mut LeanObject,
    mut v_a_9116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_9117_: u8 = 0;
    let mut v_res_9118_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9117_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9103_) as u8);
    v_res_9118_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(
        v_subsingletonInstImplicitRhs_boxed_9117_,
        v_f_9104_,
        v_info_9105_,
        v_kinds_9106_,
        v_lhss_9107_,
        v_i_9108_,
        v_rhss_9109_,
        v_eqs_9110_,
        v_hyps_9111_,
        v_a_9112_,
        v_a_9113_,
        v_a_9114_,
        v_a_9115_,
    );
    lean_dec(v_a_9115_);
    lean_dec_ref(v_a_9114_);
    lean_dec(v_a_9113_);
    lean_dec_ref(v_a_9112_);
    return v_res_9118_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(
    mut v___x_9119_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_9120_: u8,
    mut v_f_9121_: *mut LeanObject,
    mut v_info_9122_: *mut LeanObject,
    mut v_kinds_9123_: *mut LeanObject,
    mut v_lhss_9124_: *mut LeanObject,
    mut v_x_9125_: *mut LeanObject,
    mut v___y_9126_: *mut LeanObject,
    mut v___y_9127_: *mut LeanObject,
    mut v___y_9128_: *mut LeanObject,
    mut v___y_9129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9132_: u8 = 0;
    let mut v___x_9133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9141_: u8 = 0;
    let mut v___x_9142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9146_: u8 = 0;
    let mut v_a_9147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9150_: u8 = 0;
    let mut v___x_9152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9131_ = lean_array_get_size(v_lhss_9124_);
                v___x_9132_ = lean_nat_dec_eq(v___x_9131_, v___x_9119_);
                if v___x_9132_ == 0 {
                    lean_dec_ref(v_lhss_9124_);
                    lean_dec_ref(v_kinds_9123_);
                    lean_dec_ref(v_info_9122_);
                    lean_dec_ref(v_f_9121_);
                    v___x_9133_ = lean_box(0);
                    v___x_9134_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9134_, 0, v___x_9133_);
                    return v___x_9134_;
                } else {
                    v___x_9135_ = lean_unsigned_to_nat(0);
                    v___x_9136_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0;
                    v___x_9137_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_9120_, v_f_9121_, v_info_9122_, v_kinds_9123_, v_lhss_9124_, v___x_9135_, v___x_9136_, v___x_9136_, v___x_9136_, v___y_9126_, v___y_9127_, v___y_9128_, v___y_9129_);
                    if lean_obj_tag(v___x_9137_) == 0 {
                        v_a_9138_ = lean_ctor_get(v___x_9137_, 0);
                        v_isSharedCheck_9146_ = (!lean_is_exclusive(v___x_9137_)) as u8;
                        if v_isSharedCheck_9146_ == 0 {
                            v___x_9140_ = v___x_9137_;
                            v_isShared_9141_ = v_isSharedCheck_9146_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9138_);
                            lean_dec(v___x_9137_);
                            v___x_9140_ = lean_box(0);
                            v_isShared_9141_ = v_isSharedCheck_9146_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_9147_ = lean_ctor_get(v___x_9137_, 0);
                        v_isSharedCheck_9154_ = (!lean_is_exclusive(v___x_9137_)) as u8;
                        if v_isSharedCheck_9154_ == 0 {
                            v___x_9149_ = v___x_9137_;
                            v_isShared_9150_ = v_isSharedCheck_9154_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_9147_);
                            lean_dec(v___x_9137_);
                            v___x_9149_ = lean_box(0);
                            v_isShared_9150_ = v_isSharedCheck_9154_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_9142_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9142_, 0, v_a_9138_);
                if v_isShared_9141_ == 0 {
                    lean_ctor_set(v___x_9140_, 0, v___x_9142_);
                    v___x_9144_ = v___x_9140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9145_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9145_, 0, v___x_9142_);
                    v___x_9144_ = v_reuseFailAlloc_9145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9144_;
            }
            3 => {
                if v_isShared_9150_ == 0 {
                    v___x_9152_ = v___x_9149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9153_, 0, v_a_9147_);
                    v___x_9152_ = v_reuseFailAlloc_9153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(
    mut v___x_9155_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_9156_: *mut LeanObject,
    mut v_f_9157_: *mut LeanObject,
    mut v_info_9158_: *mut LeanObject,
    mut v_kinds_9159_: *mut LeanObject,
    mut v_lhss_9160_: *mut LeanObject,
    mut v_x_9161_: *mut LeanObject,
    mut v___y_9162_: *mut LeanObject,
    mut v___y_9163_: *mut LeanObject,
    mut v___y_9164_: *mut LeanObject,
    mut v___y_9165_: *mut LeanObject,
    mut v___y_9166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_9167_: u8 = 0;
    let mut v_res_9168_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9167_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9156_) as u8);
    v_res_9168_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(
            v___x_9155_,
            v_subsingletonInstImplicitRhs_boxed_9167_,
            v_f_9157_,
            v_info_9158_,
            v_kinds_9159_,
            v_lhss_9160_,
            v_x_9161_,
            v___y_9162_,
            v___y_9163_,
            v___y_9164_,
            v___y_9165_,
        );
    lean_dec(v___y_9165_);
    lean_dec_ref(v___y_9164_);
    lean_dec(v___y_9163_);
    lean_dec_ref(v___y_9162_);
    lean_dec_ref(v_x_9161_);
    lean_dec(v___x_9155_);
    return v_res_9168_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(
    mut v_subsingletonInstImplicitRhs_9169_: u8,
    mut v_f_9170_: *mut LeanObject,
    mut v_info_9171_: *mut LeanObject,
    mut v_kinds_9172_: *mut LeanObject,
    mut v_a_9173_: *mut LeanObject,
    mut v_a_9174_: *mut LeanObject,
    mut v_a_9175_: *mut LeanObject,
    mut v_a_9176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_9179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9180_: u8 = 0;
    let mut v___x_9181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9186_: u8 = 0;
    let mut v___x_9187_: u8 = 0;
    let mut v___x_9188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9192_: u8 = 0;
    let mut v___x_9193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9198_: u8 = 0;
    let mut v___x_9199_: u8 = 0;
    let mut v___x_9200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9203_: u8 = 0;
    let mut v_a_9204_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_9176_);
                lean_inc_ref(v_a_9175_);
                lean_inc(v_a_9174_);
                lean_inc_ref(v_a_9173_);
                lean_inc_ref(v_f_9170_);
                v___x_9188_ =
                    lean_infer_type(v_f_9170_, v_a_9173_, v_a_9174_, v_a_9175_, v_a_9176_);
                if lean_obj_tag(v___x_9188_) == 0 {
                    v_a_9189_ = lean_ctor_get(v___x_9188_, 0);
                    v_isSharedCheck_9203_ = (!lean_is_exclusive(v___x_9188_)) as u8;
                    if v_isSharedCheck_9203_ == 0 {
                        v___x_9191_ = v___x_9188_;
                        v_isShared_9192_ = v_isSharedCheck_9203_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9189_);
                        lean_dec(v___x_9188_);
                        v___x_9191_ = lean_box(0);
                        v_isShared_9192_ = v_isSharedCheck_9203_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_kinds_9172_);
                    lean_dec_ref(v_info_9171_);
                    lean_dec_ref(v_f_9170_);
                    v_a_9204_ = lean_ctor_get(v___x_9188_, 0);
                    lean_inc(v_a_9204_);
                    lean_dec_ref_known(v___x_9188_, 1);
                    v_a_9185_ = v_a_9204_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_9180_ == 0 {
                    lean_dec_ref(v___y_9179_);
                    v___x_9181_ = lean_box(0);
                    v___x_9182_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9182_, 0, v___x_9181_);
                    return v___x_9182_;
                } else {
                    v___x_9183_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9183_, 0, v___y_9179_);
                    return v___x_9183_;
                }
            }
            2 => {
                v___x_9186_ = l_Lean_Exception_isInterrupt(v_a_9185_);
                if v___x_9186_ == 0 {
                    lean_inc_ref(v_a_9185_);
                    v___x_9187_ = l_Lean_Exception_isRuntime(v_a_9185_);
                    v___y_9179_ = v_a_9185_;
                    v___y_9180_ = v___x_9187_;
                    state = 1;
                    continue;
                } else {
                    v___y_9179_ = v_a_9185_;
                    v___y_9180_ = v___x_9186_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_9193_ = lean_array_get_size(v_kinds_9172_);
                v___x_9194_ = lean_box((v_subsingletonInstImplicitRhs_9169_) as usize);
                v___f_9195_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed as *mut core::ffi::c_void, 12, 5);
                lean_closure_set(v___f_9195_, 0, v___x_9193_);
                lean_closure_set(v___f_9195_, 1, v___x_9194_);
                lean_closure_set(v___f_9195_, 2, v_f_9170_);
                lean_closure_set(v___f_9195_, 3, v_info_9171_);
                lean_closure_set(v___f_9195_, 4, v_kinds_9172_);
                if v_isShared_9192_ == 0 {
                    lean_ctor_set_tag(v___x_9191_, 1);
                    lean_ctor_set(v___x_9191_, 0, v___x_9193_);
                    v___x_9197_ = v___x_9191_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9202_, 0, v___x_9193_);
                    v___x_9197_ = v_reuseFailAlloc_9202_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9198_ = 1;
                v___x_9199_ = 0;
                v___x_9200_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_9189_, v___x_9197_, v___f_9195_, v___x_9198_, v___x_9199_, v_a_9173_, v_a_9174_, v_a_9175_, v_a_9176_);
                if lean_obj_tag(v___x_9200_) == 0 {
                    return v___x_9200_;
                } else {
                    v_a_9201_ = lean_ctor_get(v___x_9200_, 0);
                    lean_inc(v_a_9201_);
                    lean_dec_ref_known(v___x_9200_, 1);
                    v_a_9185_ = v_a_9201_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(
    mut v_subsingletonInstImplicitRhs_9205_: *mut LeanObject,
    mut v_f_9206_: *mut LeanObject,
    mut v_info_9207_: *mut LeanObject,
    mut v_kinds_9208_: *mut LeanObject,
    mut v_a_9209_: *mut LeanObject,
    mut v_a_9210_: *mut LeanObject,
    mut v_a_9211_: *mut LeanObject,
    mut v_a_9212_: *mut LeanObject,
    mut v_a_9213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_9214_: u8 = 0;
    let mut v_res_9215_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9214_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9205_) as u8);
    v_res_9215_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(
        v_subsingletonInstImplicitRhs_boxed_9214_,
        v_f_9206_,
        v_info_9207_,
        v_kinds_9208_,
        v_a_9209_,
        v_a_9210_,
        v_a_9211_,
        v_a_9212_,
    );
    lean_dec(v_a_9212_);
    lean_dec_ref(v_a_9211_);
    lean_dec(v_a_9210_);
    lean_dec_ref(v_a_9209_);
    return v_res_9215_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(
    mut v_sz_9216_: usize,
    mut v_i_9217_: usize,
    mut v_bs_9218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9219_: u8 = 0;
    let mut v_v_9220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_9222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9224_: u8 = 0;
    let mut v___x_9225_: usize = 0;
    let mut v___x_9226_: usize = 0;
    let mut v___x_9227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9230_: u8 = 0;
    let mut v___x_9231_: u8 = 0;
    let mut v___x_9232_: u8 = 0;
    let mut v___x_9233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9219_ = lean_usize_dec_lt(v_i_9217_, v_sz_9216_);
                if v___x_9219_ == 0 {
                    return v_bs_9218_;
                } else {
                    v_v_9220_ = lean_array_uget(v_bs_9218_, v_i_9217_);
                    v___x_9221_ = lean_unsigned_to_nat(0);
                    v_bs_x27_9222_ = lean_array_uset(v_bs_9218_, v_i_9217_, v___x_9221_);
                    v___x_9230_ = (lean_unbox(v_v_9220_) as u8);
                    match v___x_9230_ {
                        3 => {
                            lean_dec(v_v_9220_);
                            v___x_9231_ = 0;
                            v___y_9224_ = v___x_9231_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            lean_dec(v_v_9220_);
                            v___x_9232_ = 0;
                            v___y_9224_ = v___x_9232_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___x_9233_ = (lean_unbox(v_v_9220_) as u8);
                            lean_dec(v_v_9220_);
                            v___y_9224_ = v___x_9233_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_9225_ = 1usize;
                v___x_9226_ = lean_usize_add(v_i_9217_, v___x_9225_);
                v___x_9227_ = lean_box((v___y_9224_) as usize);
                v___x_9228_ = lean_array_uset(v_bs_x27_9222_, v_i_9217_, v___x_9227_);
                v_i_9217_ = v___x_9226_;
                v_bs_9218_ = v___x_9228_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(
    mut v_sz_9234_: *mut LeanObject,
    mut v_i_9235_: *mut LeanObject,
    mut v_bs_9236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9237_: usize = 0;
    let mut v_i_boxed_9238_: usize = 0;
    let mut v_res_9239_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9237_ = lean_unbox_usize(v_sz_9234_);
    lean_dec(v_sz_9234_);
    v_i_boxed_9238_ = lean_unbox_usize(v_i_9235_);
    lean_dec(v_i_9235_);
    v_res_9239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_9237_, v_i_boxed_9238_, v_bs_9236_);
    return v_res_9239_;
}
pub unsafe fn l_Lean_Meta_mkCongrSimpCore_x3f(
    mut v_f_9240_: *mut LeanObject,
    mut v_info_9241_: *mut LeanObject,
    mut v_kinds_9242_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_9243_: u8,
    mut v_a_9244_: *mut LeanObject,
    mut v_a_9245_: *mut LeanObject,
    mut v_a_9246_: *mut LeanObject,
    mut v_a_9247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9253_: u8 = 0;
    let mut v___x_9254_: u8 = 0;
    let mut v___x_9255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9259_: usize = 0;
    let mut v___x_9260_: usize = 0;
    let mut v___x_9261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9263_: u8 = 0;
    let mut v_unused_9264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_kinds_9242_);
                lean_inc_ref(v_info_9241_);
                lean_inc_ref(v_f_9240_);
                v___x_9249_ =
                    l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(
                        v_subsingletonInstImplicitRhs_9243_,
                        v_f_9240_,
                        v_info_9241_,
                        v_kinds_9242_,
                        v_a_9244_,
                        v_a_9245_,
                        v_a_9246_,
                        v_a_9247_,
                    );
                if lean_obj_tag(v___x_9249_) == 0 {
                    v_a_9250_ = lean_ctor_get(v___x_9249_, 0);
                    lean_inc(v_a_9250_);
                    if lean_obj_tag(v_a_9250_) == 1 {
                        lean_dec_ref_known(v_a_9250_, 1);
                        lean_dec_ref(v_kinds_9242_);
                        lean_dec_ref(v_info_9241_);
                        lean_dec_ref(v_f_9240_);
                        return v___x_9249_;
                    } else {
                        lean_dec(v_a_9250_);
                        v_isSharedCheck_9263_ = (!lean_is_exclusive(v___x_9249_)) as u8;
                        if v_isSharedCheck_9263_ == 0 {
                            v_unused_9264_ = lean_ctor_get(v___x_9249_, 0);
                            lean_dec(v_unused_9264_);
                            v___x_9252_ = v___x_9249_;
                            v_isShared_9253_ = v_isSharedCheck_9263_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_9249_);
                            v___x_9252_ = lean_box(0);
                            v_isShared_9253_ = v_isSharedCheck_9263_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_kinds_9242_);
                    lean_dec_ref(v_info_9241_);
                    lean_dec_ref(v_f_9240_);
                    return v___x_9249_;
                }
            }
            1 => {
                v___x_9254_ =
                    l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_9242_);
                if v___x_9254_ == 0 {
                    lean_dec_ref(v_kinds_9242_);
                    lean_dec_ref(v_info_9241_);
                    lean_dec_ref(v_f_9240_);
                    v___x_9255_ = lean_box(0);
                    if v_isShared_9253_ == 0 {
                        lean_ctor_set(v___x_9252_, 0, v___x_9255_);
                        v___x_9257_ = v___x_9252_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9258_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9258_, 0, v___x_9255_);
                        v___x_9257_ = v_reuseFailAlloc_9258_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9252_);
                    v_sz_9259_ = lean_array_size(v_kinds_9242_);
                    v___x_9260_ = 0usize;
                    v___x_9261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_9259_, v___x_9260_, v_kinds_9242_);
                    v___x_9262_ =
                        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(
                            v_subsingletonInstImplicitRhs_9243_,
                            v_f_9240_,
                            v_info_9241_,
                            v___x_9261_,
                            v_a_9244_,
                            v_a_9245_,
                            v_a_9246_,
                            v_a_9247_,
                        );
                    return v___x_9262_;
                }
            }
            2 => {
                return v___x_9257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkCongrSimpCore_x3f___boxed(
    mut v_f_9265_: *mut LeanObject,
    mut v_info_9266_: *mut LeanObject,
    mut v_kinds_9267_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_9268_: *mut LeanObject,
    mut v_a_9269_: *mut LeanObject,
    mut v_a_9270_: *mut LeanObject,
    mut v_a_9271_: *mut LeanObject,
    mut v_a_9272_: *mut LeanObject,
    mut v_a_9273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_9274_: u8 = 0;
    let mut v_res_9275_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9274_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9268_) as u8);
    v_res_9275_ = l_Lean_Meta_mkCongrSimpCore_x3f(
        v_f_9265_,
        v_info_9266_,
        v_kinds_9267_,
        v_subsingletonInstImplicitRhs_boxed_9274_,
        v_a_9269_,
        v_a_9270_,
        v_a_9271_,
        v_a_9272_,
    );
    lean_dec(v_a_9272_);
    lean_dec_ref(v_a_9271_);
    lean_dec(v_a_9270_);
    lean_dec_ref(v_a_9269_);
    return v_res_9275_;
}
pub unsafe fn l_Lean_Meta_mkCongrSimp_x3f(
    mut v_f_9276_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_9277_: u8,
    mut v_maxArgs_x3f_9278_: *mut LeanObject,
    mut v_a_9279_: *mut LeanObject,
    mut v_a_9280_: *mut LeanObject,
    mut v_a_9281_: *mut LeanObject,
    mut v_a_9282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9295_: u8 = 0;
    let mut v___x_9297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9299_: u8 = 0;
    let mut v_a_9300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9303_: u8 = 0;
    let mut v___x_9305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9284_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_9276_, v_a_9280_);
                v_a_9285_ = lean_ctor_get(v___x_9284_, 0);
                lean_inc(v_a_9285_);
                lean_dec_ref(v___x_9284_);
                v___x_9286_ = l_Lean_Expr_cleanupAnnotations(v_a_9285_);
                lean_inc_ref(v___x_9286_);
                v___x_9287_ = l_Lean_Meta_getFunInfo(
                    v___x_9286_,
                    v_maxArgs_x3f_9278_,
                    v_a_9279_,
                    v_a_9280_,
                    v_a_9281_,
                    v_a_9282_,
                );
                if lean_obj_tag(v___x_9287_) == 0 {
                    v_a_9288_ = lean_ctor_get(v___x_9287_, 0);
                    lean_inc(v_a_9288_);
                    lean_dec_ref_known(v___x_9287_, 1);
                    lean_inc_ref(v___x_9286_);
                    v___x_9289_ = l_Lean_Meta_getCongrSimpKinds(
                        v___x_9286_,
                        v_a_9288_,
                        v_a_9279_,
                        v_a_9280_,
                        v_a_9281_,
                        v_a_9282_,
                    );
                    if lean_obj_tag(v___x_9289_) == 0 {
                        v_a_9290_ = lean_ctor_get(v___x_9289_, 0);
                        lean_inc(v_a_9290_);
                        lean_dec_ref_known(v___x_9289_, 1);
                        v___x_9291_ = l_Lean_Meta_mkCongrSimpCore_x3f(
                            v___x_9286_,
                            v_a_9288_,
                            v_a_9290_,
                            v_subsingletonInstImplicitRhs_9277_,
                            v_a_9279_,
                            v_a_9280_,
                            v_a_9281_,
                            v_a_9282_,
                        );
                        return v___x_9291_;
                    } else {
                        lean_dec(v_a_9288_);
                        lean_dec_ref(v___x_9286_);
                        v_a_9292_ = lean_ctor_get(v___x_9289_, 0);
                        v_isSharedCheck_9299_ = (!lean_is_exclusive(v___x_9289_)) as u8;
                        if v_isSharedCheck_9299_ == 0 {
                            v___x_9294_ = v___x_9289_;
                            v_isShared_9295_ = v_isSharedCheck_9299_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9292_);
                            lean_dec(v___x_9289_);
                            v___x_9294_ = lean_box(0);
                            v_isShared_9295_ = v_isSharedCheck_9299_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_9286_);
                    v_a_9300_ = lean_ctor_get(v___x_9287_, 0);
                    v_isSharedCheck_9307_ = (!lean_is_exclusive(v___x_9287_)) as u8;
                    if v_isSharedCheck_9307_ == 0 {
                        v___x_9302_ = v___x_9287_;
                        v_isShared_9303_ = v_isSharedCheck_9307_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9300_);
                        lean_dec(v___x_9287_);
                        v___x_9302_ = lean_box(0);
                        v_isShared_9303_ = v_isSharedCheck_9307_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9295_ == 0 {
                    v___x_9297_ = v___x_9294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9298_, 0, v_a_9292_);
                    v___x_9297_ = v_reuseFailAlloc_9298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9297_;
            }
            3 => {
                if v_isShared_9303_ == 0 {
                    v___x_9305_ = v___x_9302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9306_, 0, v_a_9300_);
                    v___x_9305_ = v_reuseFailAlloc_9306_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkCongrSimp_x3f___boxed(
    mut v_f_9308_: *mut LeanObject,
    mut v_subsingletonInstImplicitRhs_9309_: *mut LeanObject,
    mut v_maxArgs_x3f_9310_: *mut LeanObject,
    mut v_a_9311_: *mut LeanObject,
    mut v_a_9312_: *mut LeanObject,
    mut v_a_9313_: *mut LeanObject,
    mut v_a_9314_: *mut LeanObject,
    mut v_a_9315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subsingletonInstImplicitRhs_boxed_9316_: u8 = 0;
    let mut v_res_9317_: *mut LeanObject = core::ptr::null_mut();
    v_subsingletonInstImplicitRhs_boxed_9316_ =
        (lean_unbox(v_subsingletonInstImplicitRhs_9309_) as u8);
    v_res_9317_ = l_Lean_Meta_mkCongrSimp_x3f(
        v_f_9308_,
        v_subsingletonInstImplicitRhs_boxed_9316_,
        v_maxArgs_x3f_9310_,
        v_a_9311_,
        v_a_9312_,
        v_a_9313_,
        v_a_9314_,
    );
    lean_dec(v_a_9314_);
    lean_dec_ref(v_a_9313_);
    lean_dec(v_a_9312_);
    lean_dec_ref(v_a_9311_);
    return v_res_9317_;
}
pub unsafe fn _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0() -> *mut LeanObject {
    let mut v___x_9322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9323_: *mut LeanObject = core::ptr::null_mut();
    v___x_9322_ = l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0;
    v___x_9323_ = lean_string_utf8_byte_size(v___x_9322_);
    return v___x_9323_;
}
pub unsafe fn l_Lean_Meta_isHCongrReservedNameSuffix(mut v_s_9324_: *mut LeanObject) -> u8 {
    let mut v___x_9325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9328_: u8 = 0;
    v___x_9325_ = l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0;
    v___x_9326_ = lean_string_utf8_byte_size(v_s_9324_);
    v___x_9327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_isHCongrReservedNameSuffix___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once),
        _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0,
    );
    v___x_9328_ = lean_nat_dec_le(v___x_9327_, v___x_9326_);
    if v___x_9328_ == 0 {
        lean_dec_ref(v_s_9324_);
        return v___x_9328_;
    } else {
        let mut v___x_9329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9330_: u8 = 0;
        v___x_9329_ = lean_unsigned_to_nat(0);
        v___x_9330_ = lean_string_memcmp(
            v_s_9324_,
            v___x_9325_,
            v___x_9329_,
            v___x_9329_,
            v___x_9327_,
        );
        if v___x_9330_ == 0 {
            lean_dec_ref(v_s_9324_);
            return v___x_9330_;
        } else {
            let mut v___x_9331_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9332_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9333_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9335_: u8 = 0;
            v___x_9331_ = lean_unsigned_to_nat(7);
            lean_inc_ref(v_s_9324_);
            v___x_9332_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_9332_, 0, v_s_9324_);
            lean_ctor_set(v___x_9332_, 1, v___x_9329_);
            lean_ctor_set(v___x_9332_, 2, v___x_9326_);
            v___x_9333_ = l_String_Slice_Pos_nextn(v___x_9332_, v___x_9329_, v___x_9331_);
            lean_dec_ref_known(v___x_9332_, 3);
            v___x_9334_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_9334_, 0, v_s_9324_);
            lean_ctor_set(v___x_9334_, 1, v___x_9333_);
            lean_ctor_set(v___x_9334_, 2, v___x_9326_);
            v___x_9335_ = l_String_Slice_isNat(v___x_9334_);
            lean_dec_ref_known(v___x_9334_, 3);
            return v___x_9335_;
        }
    }
}
pub unsafe fn l_Lean_Meta_isHCongrReservedNameSuffix___boxed(
    mut v_s_9336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9337_: u8 = 0;
    let mut v_r_9338_: *mut LeanObject = core::ptr::null_mut();
    v_res_9337_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_9336_);
    v_r_9338_ = lean_box((v_res_9337_) as usize);
    return v_r_9338_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9390_: *mut LeanObject = core::ptr::null_mut();
    v___x_9388_ = lean_unsigned_to_nat(3482611248);
    v___x_9389_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
    v___x_9390_ = l_Lean_Name_num___override(v___x_9389_, v___x_9388_);
    return v___x_9390_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9394_: *mut LeanObject = core::ptr::null_mut();
    v___x_9392_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
    v___x_9393_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
    v___x_9394_ = l_Lean_Name_str___override(v___x_9393_, v___x_9392_);
    return v___x_9394_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9398_: *mut LeanObject = core::ptr::null_mut();
    v___x_9396_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
    v___x_9397_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
    v___x_9398_ = l_Lean_Name_str___override(v___x_9397_, v___x_9396_);
    return v___x_9398_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9401_: *mut LeanObject = core::ptr::null_mut();
    v___x_9399_ = lean_unsigned_to_nat(2);
    v___x_9400_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
    v___x_9401_ = l_Lean_Name_num___override(v___x_9400_, v___x_9399_);
    return v___x_9401_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9404_: u8 = 0;
    let mut v___x_9405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9406_: *mut LeanObject = core::ptr::null_mut();
    v___x_9403_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
    v___x_9404_ = 0;
    v___x_9405_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
    v___x_9406_ = l_Lean_registerTraceClass(v___x_9403_, v___x_9404_, v___x_9405_);
    return v___x_9406_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(
    mut v_a_9407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9408_: *mut LeanObject = core::ptr::null_mut();
    v_res_9408_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
    return v_res_9408_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(
    mut v_env_9409_: *mut LeanObject,
    mut v_as_9410_: *mut LeanObject,
    mut v_i_9411_: usize,
    mut v_stop_9412_: usize,
    mut v_b_9413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_9415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9416_: usize = 0;
    let mut v___x_9417_: usize = 0;
    let mut v___x_9419_: u8 = 0;
    let mut v___x_9420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_9421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9422_: u8 = 0;
    let mut v___x_9423_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9419_ = lean_usize_dec_eq(v_i_9411_, v_stop_9412_);
                if v___x_9419_ == 0 {
                    v___x_9420_ = lean_array_uget_borrowed(v_as_9410_, v_i_9411_);
                    v_fst_9421_ = lean_ctor_get(v___x_9420_, 0);
                    lean_inc(v_fst_9421_);
                    lean_inc_ref(v_env_9409_);
                    v___x_9422_ =
                        l_Lean_Environment_contains(v_env_9409_, v_fst_9421_, v___x_9419_);
                    if v___x_9422_ == 0 {
                        v___y_9415_ = v_b_9413_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_9420_);
                        v___x_9423_ = lean_array_push(v_b_9413_, v___x_9420_);
                        v___y_9415_ = v___x_9423_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_9409_);
                    return v_b_9413_;
                }
            }
            1 => {
                v___x_9416_ = 1usize;
                v___x_9417_ = lean_usize_add(v_i_9411_, v___x_9416_);
                v_i_9411_ = v___x_9417_;
                v_b_9413_ = v___y_9415_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_9424_: *mut LeanObject,
    mut v_as_9425_: *mut LeanObject,
    mut v_i_9426_: *mut LeanObject,
    mut v_stop_9427_: *mut LeanObject,
    mut v_b_9428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_9429_: usize = 0;
    let mut v_stop_boxed_9430_: usize = 0;
    let mut v_res_9431_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_9429_ = lean_unbox_usize(v_i_9426_);
    lean_dec(v_i_9426_);
    v_stop_boxed_9430_ = lean_unbox_usize(v_stop_9427_);
    lean_dec(v_stop_9427_);
    v_res_9431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_9424_, v_as_9425_, v_i_boxed_9429_, v_stop_boxed_9430_, v_b_9428_);
    lean_dec_ref(v_as_9425_);
    return v_res_9431_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_9432_: *mut LeanObject,
    mut v_x_9433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_9434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_9435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_9436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_9437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9433_) == 0 {
                    v_k_9434_ = lean_ctor_get(v_x_9433_, 1);
                    v_v_9435_ = lean_ctor_get(v_x_9433_, 2);
                    v_l_9436_ = lean_ctor_get(v_x_9433_, 3);
                    v_r_9437_ = lean_ctor_get(v_x_9433_, 4);
                    v___x_9438_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_9432_, v_l_9436_);
                    lean_inc(v_v_9435_);
                    lean_inc(v_k_9434_);
                    v___x_9439_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9439_, 0, v_k_9434_);
                    lean_ctor_set(v___x_9439_, 1, v_v_9435_);
                    v___x_9440_ = lean_array_push(v___x_9438_, v___x_9439_);
                    v_init_9432_ = v___x_9440_;
                    v_x_9433_ = v_r_9437_;
                    state = 0;
                    continue;
                } else {
                    return v_init_9432_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_9442_: *mut LeanObject,
    mut v_x_9443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9444_: *mut LeanObject = core::ptr::null_mut();
    v_res_9444_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_9442_, v_x_9443_);
    lean_dec(v_x_9443_);
    return v_res_9444_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(
    mut v_env_9451_: *mut LeanObject,
    mut v_s_9452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9458_: u8 = 0;
    v___x_9453_ = lean_unsigned_to_nat(0);
    v___x_9454_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_;
    v___x_9455_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_9454_, v_s_9452_);
    v___x_9456_ = lean_array_get_size(v___x_9455_);
    v___x_9457_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_;
    v___x_9458_ = lean_nat_dec_lt(v___x_9453_, v___x_9456_);
    if v___x_9458_ == 0 {
        let mut v___x_9459_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_9455_);
        lean_dec_ref(v_env_9451_);
        v___x_9459_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_;
        return v___x_9459_;
    } else {
        let mut v___x_9460_: u8 = 0;
        v___x_9460_ = lean_nat_dec_le(v___x_9456_, v___x_9456_);
        if v___x_9460_ == 0 {
            if v___x_9458_ == 0 {
                let mut v___x_9461_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_9455_);
                lean_dec_ref(v_env_9451_);
                v___x_9461_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_;
                return v___x_9461_;
            } else {
                let mut v___x_9462_: usize = 0;
                let mut v___x_9463_: usize = 0;
                let mut v___x_9464_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_9465_: *mut LeanObject = core::ptr::null_mut();
                v___x_9462_ = 0usize;
                v___x_9463_ = lean_usize_of_nat(v___x_9456_);
                v___x_9464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_9451_, v___x_9455_, v___x_9462_, v___x_9463_, v___x_9457_);
                lean_dec_ref(v___x_9455_);
                lean_inc_ref_n(v___x_9464_, 2);
                v___x_9465_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_9465_, 0, v___x_9464_);
                lean_ctor_set(v___x_9465_, 1, v___x_9464_);
                lean_ctor_set(v___x_9465_, 2, v___x_9464_);
                return v___x_9465_;
            }
        } else {
            let mut v___x_9466_: usize = 0;
            let mut v___x_9467_: usize = 0;
            let mut v___x_9468_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9469_: *mut LeanObject = core::ptr::null_mut();
            v___x_9466_ = 0usize;
            v___x_9467_ = lean_usize_of_nat(v___x_9456_);
            v___x_9468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_9451_, v___x_9455_, v___x_9466_, v___x_9467_, v___x_9457_);
            lean_dec_ref(v___x_9455_);
            lean_inc_ref_n(v___x_9468_, 2);
            v___x_9469_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_9469_, 0, v___x_9468_);
            lean_ctor_set(v___x_9469_, 1, v___x_9468_);
            lean_ctor_set(v___x_9469_, 2, v___x_9468_);
            return v___x_9469_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(
    mut v_env_9470_: *mut LeanObject,
    mut v_s_9471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9472_: *mut LeanObject = core::ptr::null_mut();
    v_res_9472_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_9470_, v_s_9471_);
    lean_dec(v_s_9471_);
    return v_res_9472_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_9482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9485_: *mut LeanObject = core::ptr::null_mut();
    v___f_9482_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_;
    v___x_9483_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_;
    v___x_9484_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_;
    v___x_9485_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_9483_, v___x_9484_, v___f_9482_);
    return v___x_9485_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(
    mut v_a_9486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9487_: *mut LeanObject = core::ptr::null_mut();
    v_res_9487_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
    return v_res_9487_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(
    mut v_init_9488_: *mut LeanObject,
    mut v_t_9489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9490_: *mut LeanObject = core::ptr::null_mut();
    v___x_9490_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_9488_, v_t_9489_);
    return v___x_9490_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_9491_: *mut LeanObject,
    mut v_t_9492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9493_: *mut LeanObject = core::ptr::null_mut();
    v_res_9493_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_9491_, v_t_9492_);
    lean_dec(v_t_9492_);
    return v_res_9493_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(
    mut v_env_9494_: *mut LeanObject,
    mut v_n_9495_: *mut LeanObject,
) -> u8 {
    let mut v_pre_9496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_9497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9499_: u8 = 0;
    let mut v___x_9500_: u8 = 0;
    let mut v___x_9501_: u8 = 0;
    let mut v___x_9502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9503_: u8 = 0;
    let mut v___x_9504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_9495_) == 1 {
                    v_pre_9496_ = lean_ctor_get(v_n_9495_, 0);
                    lean_inc(v_pre_9496_);
                    v_str_9497_ = lean_ctor_get(v_n_9495_, 1);
                    lean_inc_ref_n(v_str_9497_, 2);
                    lean_dec_ref_known(v_n_9495_, 2);
                    v___x_9501_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_9497_);
                    if v___x_9501_ == 0 {
                        v___x_9502_ = l_Lean_Meta_congrSimpSuffix___closed__0;
                        v___x_9503_ = lean_string_dec_eq(v_str_9497_, v___x_9502_);
                        lean_dec_ref(v_str_9497_);
                        v___y_9499_ = v___x_9503_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_str_9497_);
                        v___y_9499_ = v___x_9501_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_n_9495_);
                    lean_dec_ref(v_env_9494_);
                    v___x_9504_ = 0;
                    return v___x_9504_;
                }
            }
            1 => {
                if v___y_9499_ == 0 {
                    lean_dec(v_pre_9496_);
                    lean_dec_ref(v_env_9494_);
                    return v___y_9499_;
                } else {
                    v___x_9500_ =
                        l_Lean_Environment_contains(v_env_9494_, v_pre_9496_, v___y_9499_);
                    return v___x_9500_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(
    mut v_env_9505_: *mut LeanObject,
    mut v_n_9506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9507_: u8 = 0;
    let mut v_r_9508_: *mut LeanObject = core::ptr::null_mut();
    v_res_9507_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_9505_, v_n_9506_);
    v_r_9508_ = lean_box((v_res_9507_) as usize);
    return v_r_9508_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_9511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9512_: *mut LeanObject = core::ptr::null_mut();
    v___f_9511_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_;
    v___x_9512_ = l_Lean_registerReservedNamePredicate(v___f_9511_);
    return v___x_9512_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(
    mut v_a_9513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9514_: *mut LeanObject = core::ptr::null_mut();
    v_res_9514_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
    return v_res_9514_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(
    mut v_thm_9515_: *mut LeanObject,
    mut v___y_9516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_9520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_9521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_9522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9524_: u8 = 0;
    let mut v___x_9525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9528_: u8 = 0;
    let mut v___x_9529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_9532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9533_: u8 = 0;
    let mut v___x_9534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9518_ = lean_st_ref_get(v___y_9516_);
                v_env_9519_ = lean_ctor_get(v___x_9518_, 0);
                lean_inc_ref_n(v_env_9519_, 2);
                lean_dec(v___x_9518_);
                v_toConstantVal_9520_ = lean_ctor_get(v_thm_9515_, 0);
                v_value_9521_ = lean_ctor_get(v_thm_9515_, 1);
                v_all_9522_ = lean_ctor_get(v_thm_9515_, 2);
                v_type_9532_ = lean_ctor_get(v_toConstantVal_9520_, 2);
                v___x_9533_ = l_Lean_Environment_hasUnsafe(v_env_9519_, v_type_9532_);
                if v___x_9533_ == 0 {
                    v___x_9534_ = l_Lean_Environment_hasUnsafe(v_env_9519_, v_value_9521_);
                    v___y_9524_ = v___x_9534_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_env_9519_);
                    v___y_9524_ = v___x_9533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_9524_ == 0 {
                    v___x_9525_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_9525_, 0, v_thm_9515_);
                    v___x_9526_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9526_, 0, v___x_9525_);
                    return v___x_9526_;
                } else {
                    lean_inc(v_all_9522_);
                    lean_inc_ref(v_value_9521_);
                    lean_inc_ref(v_toConstantVal_9520_);
                    lean_dec_ref(v_thm_9515_);
                    v___x_9527_ = lean_box(0);
                    v___x_9528_ = 0;
                    v___x_9529_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v___x_9529_, 0, v_toConstantVal_9520_);
                    lean_ctor_set(v___x_9529_, 1, v_value_9521_);
                    lean_ctor_set(v___x_9529_, 2, v___x_9527_);
                    lean_ctor_set(v___x_9529_, 3, v_all_9522_);
                    lean_ctor_set_uint8(
                        v___x_9529_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_9528_,
                    );
                    v___x_9530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9530_, 0, v___x_9529_);
                    v___x_9531_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9531_, 0, v___x_9530_);
                    return v___x_9531_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_thm_9535_: *mut LeanObject,
    mut v___y_9536_: *mut LeanObject,
    mut v___y_9537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9538_: *mut LeanObject = core::ptr::null_mut();
    v_res_9538_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_9535_, v___y_9536_);
    lean_dec(v___y_9536_);
    return v_res_9538_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(
    mut v_thm_9539_: *mut LeanObject,
    mut v___y_9540_: *mut LeanObject,
    mut v___y_9541_: *mut LeanObject,
    mut v___y_9542_: *mut LeanObject,
    mut v___y_9543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9545_: *mut LeanObject = core::ptr::null_mut();
    v___x_9545_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_9539_, v___y_9543_);
    return v___x_9545_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(
    mut v_thm_9546_: *mut LeanObject,
    mut v___y_9547_: *mut LeanObject,
    mut v___y_9548_: *mut LeanObject,
    mut v___y_9549_: *mut LeanObject,
    mut v___y_9550_: *mut LeanObject,
    mut v___y_9551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9552_: *mut LeanObject = core::ptr::null_mut();
    v_res_9552_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_9546_, v___y_9547_, v___y_9548_, v___y_9549_, v___y_9550_);
    lean_dec(v___y_9550_);
    lean_dec_ref(v___y_9549_);
    lean_dec(v___y_9548_);
    lean_dec_ref(v___y_9547_);
    return v_res_9552_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0()
-> f64 {
    let mut v___x_9553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9554_: f64 = 0.0;
    v___x_9553_ = lean_unsigned_to_nat(0);
    v___x_9554_ = lean_float_of_nat(v___x_9553_);
    return v___x_9554_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(
    mut v_cls_9558_: *mut LeanObject,
    mut v_msg_9559_: *mut LeanObject,
    mut v___y_9560_: *mut LeanObject,
    mut v___y_9561_: *mut LeanObject,
    mut v___y_9562_: *mut LeanObject,
    mut v___y_9563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_9565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9570_: u8 = 0;
    let mut v___x_9571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_9572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_9574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_9575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_9576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_9577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_9578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_9579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_9580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9583_: u8 = 0;
    let mut v_tid_9584_: u64 = 0;
    let mut v_traces_9585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9588_: u8 = 0;
    let mut v___x_9589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9590_: f64 = 0.0;
    let mut v___x_9591_: u8 = 0;
    let mut v___x_9592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9609_: u8 = 0;
    let mut v_isSharedCheck_9610_: u8 = 0;
    let mut v_isSharedCheck_9611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_9565_ = lean_ctor_get(v___y_9562_, 5);
                v___x_9566_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_9559_, v___y_9560_, v___y_9561_, v___y_9562_, v___y_9563_);
                v_a_9567_ = lean_ctor_get(v___x_9566_, 0);
                v_isSharedCheck_9611_ = (!lean_is_exclusive(v___x_9566_)) as u8;
                if v_isSharedCheck_9611_ == 0 {
                    v___x_9569_ = v___x_9566_;
                    v_isShared_9570_ = v_isSharedCheck_9611_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_9567_);
                    lean_dec(v___x_9566_);
                    v___x_9569_ = lean_box(0);
                    v_isShared_9570_ = v_isSharedCheck_9611_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_9571_ = lean_st_ref_take(v___y_9563_);
                v_traceState_9572_ = lean_ctor_get(v___x_9571_, 4);
                v_env_9573_ = lean_ctor_get(v___x_9571_, 0);
                v_nextMacroScope_9574_ = lean_ctor_get(v___x_9571_, 1);
                v_ngen_9575_ = lean_ctor_get(v___x_9571_, 2);
                v_auxDeclNGen_9576_ = lean_ctor_get(v___x_9571_, 3);
                v_cache_9577_ = lean_ctor_get(v___x_9571_, 5);
                v_messages_9578_ = lean_ctor_get(v___x_9571_, 6);
                v_infoState_9579_ = lean_ctor_get(v___x_9571_, 7);
                v_snapshotTasks_9580_ = lean_ctor_get(v___x_9571_, 8);
                v_isSharedCheck_9610_ = (!lean_is_exclusive(v___x_9571_)) as u8;
                if v_isSharedCheck_9610_ == 0 {
                    v___x_9582_ = v___x_9571_;
                    v_isShared_9583_ = v_isSharedCheck_9610_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_9580_);
                    lean_inc(v_infoState_9579_);
                    lean_inc(v_messages_9578_);
                    lean_inc(v_cache_9577_);
                    lean_inc(v_traceState_9572_);
                    lean_inc(v_auxDeclNGen_9576_);
                    lean_inc(v_ngen_9575_);
                    lean_inc(v_nextMacroScope_9574_);
                    lean_inc(v_env_9573_);
                    lean_dec(v___x_9571_);
                    v___x_9582_ = lean_box(0);
                    v_isShared_9583_ = v_isSharedCheck_9610_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_9584_ = lean_ctor_get_uint64(
                    v_traceState_9572_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_9585_ = lean_ctor_get(v_traceState_9572_, 0);
                v_isSharedCheck_9609_ = (!lean_is_exclusive(v_traceState_9572_)) as u8;
                if v_isSharedCheck_9609_ == 0 {
                    v___x_9587_ = v_traceState_9572_;
                    v_isShared_9588_ = v_isSharedCheck_9609_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_9585_);
                    lean_dec(v_traceState_9572_);
                    v___x_9587_ = lean_box(0);
                    v_isShared_9588_ = v_isSharedCheck_9609_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9589_ = lean_box(0);
                v___x_9590_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0);
                v___x_9591_ = 0;
                v___x_9592_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1;
                v___x_9593_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_9593_, 0, v_cls_9558_);
                lean_ctor_set(v___x_9593_, 1, v___x_9589_);
                lean_ctor_set(v___x_9593_, 2, v___x_9592_);
                lean_ctor_set_float(
                    v___x_9593_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_9590_,
                );
                lean_ctor_set_float(
                    v___x_9593_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_9590_,
                );
                lean_ctor_set_uint8(
                    v___x_9593_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_9591_,
                );
                v___x_9594_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2;
                v___x_9595_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_9595_, 0, v___x_9593_);
                lean_ctor_set(v___x_9595_, 1, v_a_9567_);
                lean_ctor_set(v___x_9595_, 2, v___x_9594_);
                lean_inc(v_ref_9565_);
                v___x_9596_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_9596_, 0, v_ref_9565_);
                lean_ctor_set(v___x_9596_, 1, v___x_9595_);
                v___x_9597_ = l_Lean_PersistentArray_push___redArg(v_traces_9585_, v___x_9596_);
                if v_isShared_9588_ == 0 {
                    lean_ctor_set(v___x_9587_, 0, v___x_9597_);
                    v___x_9599_ = v___x_9587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9608_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9608_, 0, v___x_9597_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_9608_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_9584_,
                    );
                    v___x_9599_ = v_reuseFailAlloc_9608_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_9583_ == 0 {
                    lean_ctor_set(v___x_9582_, 4, v___x_9599_);
                    v___x_9601_ = v___x_9582_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9607_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 0, v_env_9573_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 1, v_nextMacroScope_9574_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 2, v_ngen_9575_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 3, v_auxDeclNGen_9576_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 4, v___x_9599_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 5, v_cache_9577_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 6, v_messages_9578_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 7, v_infoState_9579_);
                    lean_ctor_set(v_reuseFailAlloc_9607_, 8, v_snapshotTasks_9580_);
                    v___x_9601_ = v_reuseFailAlloc_9607_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_9602_ = lean_st_ref_set(v___y_9563_, v___x_9601_);
                v___x_9603_ = lean_box(0);
                if v_isShared_9570_ == 0 {
                    lean_ctor_set(v___x_9569_, 0, v___x_9603_);
                    v___x_9605_ = v___x_9569_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9606_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9606_, 0, v___x_9603_);
                    v___x_9605_ = v_reuseFailAlloc_9606_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(
    mut v_cls_9612_: *mut LeanObject,
    mut v_msg_9613_: *mut LeanObject,
    mut v___y_9614_: *mut LeanObject,
    mut v___y_9615_: *mut LeanObject,
    mut v___y_9616_: *mut LeanObject,
    mut v___y_9617_: *mut LeanObject,
    mut v___y_9618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9619_: *mut LeanObject = core::ptr::null_mut();
    v_res_9619_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_9612_, v_msg_9613_, v___y_9614_, v___y_9615_, v___y_9616_, v___y_9617_);
    lean_dec(v___y_9617_);
    lean_dec_ref(v___y_9616_);
    lean_dec(v___y_9615_);
    lean_dec_ref(v___y_9614_);
    return v_res_9619_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9620_: *mut LeanObject = core::ptr::null_mut();
    v___x_9620_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_9620_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9622_: *mut LeanObject = core::ptr::null_mut();
    v___x_9621_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9622_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9622_, 0, v___x_9621_);
    return v___x_9622_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9624_: *mut LeanObject = core::ptr::null_mut();
    v___x_9623_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9624_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_9624_, 0, v___x_9623_);
    lean_ctor_set(v___x_9624_, 1, v___x_9623_);
    return v___x_9624_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9630_: *mut LeanObject = core::ptr::null_mut();
    v___x_9628_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
    v___x_9629_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
    v___x_9630_ = l_Lean_Name_append(v___x_9629_, v___x_9628_);
    return v___x_9630_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9633_: *mut LeanObject = core::ptr::null_mut();
    v___x_9632_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
    v___x_9633_ = l_Lean_stringToMessageData(v___x_9632_);
    return v___x_9633_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(
    mut v___x_9634_: *mut LeanObject,
    mut v___x_9635_: u8,
    mut v_name_9636_: *mut LeanObject,
    mut v_argKinds_9637_: *mut LeanObject,
    mut v___x_9638_: *mut LeanObject,
    mut v___y_9639_: *mut LeanObject,
    mut v___y_9640_: *mut LeanObject,
    mut v___y_9641_: *mut LeanObject,
    mut v___y_9642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_9645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_9649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_9650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_9651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_9652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_9653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_9654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_9655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9658_: u8 = 0;
    let mut v___x_9659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_9666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_9667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_9668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_9669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9672_: u8 = 0;
    let mut v___x_9674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9679_: u8 = 0;
    let mut v_unused_9680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9682_: u8 = 0;
    let mut v_unused_9683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_9687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_9688_: u8 = 0;
    let mut v_inheritedTraceOptions_9689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9692_: u8 = 0;
    let mut v___x_9693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9698_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9684_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_9634_, v___y_9642_);
                v_a_9685_ = lean_ctor_get(v___x_9684_, 0);
                lean_inc(v_a_9685_);
                lean_dec_ref(v___x_9684_);
                v___x_9686_ = l_Lean_addDecl(v_a_9685_, v___x_9635_, v___y_9641_, v___y_9642_);
                if lean_obj_tag(v___x_9686_) == 0 {
                    lean_dec_ref_known(v___x_9686_, 1);
                    v_options_9687_ = lean_ctor_get(v___y_9641_, 2);
                    v_hasTrace_9688_ = lean_ctor_get_uint8(
                        v_options_9687_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_9688_ == 0 {
                        v___y_9645_ = v___y_9640_;
                        v___y_9646_ = v___y_9642_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_9689_ = lean_ctor_get(v___y_9641_, 13);
                        v___x_9690_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
                        v___x_9691_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                        v___x_9692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_9689_,
                            v_options_9687_,
                            v___x_9691_,
                        );
                        if v___x_9692_ == 0 {
                            v___y_9645_ = v___y_9640_;
                            v___y_9646_ = v___y_9642_;
                            state = 1;
                            continue;
                        } else {
                            v___x_9693_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                            lean_inc(v_name_9636_);
                            v___x_9694_ = l_Lean_MessageData_ofName(v_name_9636_);
                            v___x_9695_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_9695_, 0, v___x_9693_);
                            lean_ctor_set(v___x_9695_, 1, v___x_9694_);
                            v___x_9696_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
                            v___x_9697_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_9697_, 0, v___x_9695_);
                            lean_ctor_set(v___x_9697_, 1, v___x_9696_);
                            v___x_9698_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_9690_, v___x_9697_, v___y_9639_, v___y_9640_, v___y_9641_, v___y_9642_);
                            if lean_obj_tag(v___x_9698_) == 0 {
                                lean_dec_ref_known(v___x_9698_, 1);
                                v___y_9645_ = v___y_9640_;
                                v___y_9646_ = v___y_9642_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v___x_9638_);
                                lean_dec_ref(v_argKinds_9637_);
                                lean_dec(v_name_9636_);
                                return v___x_9698_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_9638_);
                    lean_dec_ref(v_argKinds_9637_);
                    lean_dec(v_name_9636_);
                    return v___x_9686_;
                }
            }
            1 => {
                v___x_9647_ = lean_st_ref_take(v___y_9646_);
                v_env_9648_ = lean_ctor_get(v___x_9647_, 0);
                v_nextMacroScope_9649_ = lean_ctor_get(v___x_9647_, 1);
                v_ngen_9650_ = lean_ctor_get(v___x_9647_, 2);
                v_auxDeclNGen_9651_ = lean_ctor_get(v___x_9647_, 3);
                v_traceState_9652_ = lean_ctor_get(v___x_9647_, 4);
                v_messages_9653_ = lean_ctor_get(v___x_9647_, 6);
                v_infoState_9654_ = lean_ctor_get(v___x_9647_, 7);
                v_snapshotTasks_9655_ = lean_ctor_get(v___x_9647_, 8);
                v_isSharedCheck_9682_ = (!lean_is_exclusive(v___x_9647_)) as u8;
                if v_isSharedCheck_9682_ == 0 {
                    v_unused_9683_ = lean_ctor_get(v___x_9647_, 5);
                    lean_dec(v_unused_9683_);
                    v___x_9657_ = v___x_9647_;
                    v_isShared_9658_ = v_isSharedCheck_9682_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_9655_);
                    lean_inc(v_infoState_9654_);
                    lean_inc(v_messages_9653_);
                    lean_inc(v_traceState_9652_);
                    lean_inc(v_auxDeclNGen_9651_);
                    lean_inc(v_ngen_9650_);
                    lean_inc(v_nextMacroScope_9649_);
                    lean_inc(v_env_9648_);
                    lean_dec(v___x_9647_);
                    v___x_9657_ = lean_box(0);
                    v_isShared_9658_ = v_isSharedCheck_9682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9659_ = l_Lean_Meta_congrKindsExt;
                v___x_9660_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_9659_,
                    v_env_9648_,
                    v_name_9636_,
                    v_argKinds_9637_,
                );
                v___x_9661_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                if v_isShared_9658_ == 0 {
                    lean_ctor_set(v___x_9657_, 5, v___x_9661_);
                    lean_ctor_set(v___x_9657_, 0, v___x_9660_);
                    v___x_9663_ = v___x_9657_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9681_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 0, v___x_9660_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 1, v_nextMacroScope_9649_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 2, v_ngen_9650_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 3, v_auxDeclNGen_9651_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 4, v_traceState_9652_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 5, v___x_9661_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 6, v_messages_9653_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 7, v_infoState_9654_);
                    lean_ctor_set(v_reuseFailAlloc_9681_, 8, v_snapshotTasks_9655_);
                    v___x_9663_ = v_reuseFailAlloc_9681_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9664_ = lean_st_ref_set(v___y_9646_, v___x_9663_);
                v___x_9665_ = lean_st_ref_take(v___y_9645_);
                v_mctx_9666_ = lean_ctor_get(v___x_9665_, 0);
                v_zetaDeltaFVarIds_9667_ = lean_ctor_get(v___x_9665_, 2);
                v_postponed_9668_ = lean_ctor_get(v___x_9665_, 3);
                v_diag_9669_ = lean_ctor_get(v___x_9665_, 4);
                v_isSharedCheck_9679_ = (!lean_is_exclusive(v___x_9665_)) as u8;
                if v_isSharedCheck_9679_ == 0 {
                    v_unused_9680_ = lean_ctor_get(v___x_9665_, 1);
                    lean_dec(v_unused_9680_);
                    v___x_9671_ = v___x_9665_;
                    v_isShared_9672_ = v_isSharedCheck_9679_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_diag_9669_);
                    lean_inc(v_postponed_9668_);
                    lean_inc(v_zetaDeltaFVarIds_9667_);
                    lean_inc(v_mctx_9666_);
                    lean_dec(v___x_9665_);
                    v___x_9671_ = lean_box(0);
                    v_isShared_9672_ = v_isSharedCheck_9679_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_9672_ == 0 {
                    lean_ctor_set(v___x_9671_, 1, v___x_9638_);
                    v___x_9674_ = v___x_9671_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9678_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9678_, 0, v_mctx_9666_);
                    lean_ctor_set(v_reuseFailAlloc_9678_, 1, v___x_9638_);
                    lean_ctor_set(v_reuseFailAlloc_9678_, 2, v_zetaDeltaFVarIds_9667_);
                    lean_ctor_set(v_reuseFailAlloc_9678_, 3, v_postponed_9668_);
                    lean_ctor_set(v_reuseFailAlloc_9678_, 4, v_diag_9669_);
                    v___x_9674_ = v_reuseFailAlloc_9678_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_9675_ = lean_st_ref_set(v___y_9645_, v___x_9674_);
                v___x_9676_ = lean_box(0);
                v___x_9677_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9677_, 0, v___x_9676_);
                return v___x_9677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(
    mut v___x_9699_: *mut LeanObject,
    mut v___x_9700_: *mut LeanObject,
    mut v_name_9701_: *mut LeanObject,
    mut v_argKinds_9702_: *mut LeanObject,
    mut v___x_9703_: *mut LeanObject,
    mut v___y_9704_: *mut LeanObject,
    mut v___y_9705_: *mut LeanObject,
    mut v___y_9706_: *mut LeanObject,
    mut v___y_9707_: *mut LeanObject,
    mut v___y_9708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_15938__boxed_9709_: u8 = 0;
    let mut v_res_9710_: *mut LeanObject = core::ptr::null_mut();
    v___x_15938__boxed_9709_ = (lean_unbox(v___x_9700_) as u8);
    v_res_9710_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_9699_, v___x_15938__boxed_9709_, v_name_9701_, v_argKinds_9702_, v___x_9703_, v___y_9704_, v___y_9705_, v___y_9706_, v___y_9707_);
    lean_dec(v___y_9707_);
    lean_dec_ref(v___y_9706_);
    lean_dec(v___y_9705_);
    lean_dec_ref(v___y_9704_);
    return v_res_9710_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(
    mut v_a_9711_: *mut LeanObject,
    mut v_a_9712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_9714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_9715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9718_: u8 = 0;
    let mut v___x_9719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_9711_) == 0 {
                    v___x_9713_ = l_List_reverse___redArg(v_a_9712_);
                    return v___x_9713_;
                } else {
                    v_head_9714_ = lean_ctor_get(v_a_9711_, 0);
                    v_tail_9715_ = lean_ctor_get(v_a_9711_, 1);
                    v_isSharedCheck_9724_ = (!lean_is_exclusive(v_a_9711_)) as u8;
                    if v_isSharedCheck_9724_ == 0 {
                        v___x_9717_ = v_a_9711_;
                        v_isShared_9718_ = v_isSharedCheck_9724_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_9715_);
                        lean_inc(v_head_9714_);
                        lean_dec(v_a_9711_);
                        v___x_9717_ = lean_box(0);
                        v_isShared_9718_ = v_isSharedCheck_9724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9719_ = l_Lean_mkLevelParam(v_head_9714_);
                if v_isShared_9718_ == 0 {
                    lean_ctor_set(v___x_9717_, 1, v_a_9712_);
                    lean_ctor_set(v___x_9717_, 0, v___x_9719_);
                    v___x_9721_ = v___x_9717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9723_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9723_, 0, v___x_9719_);
                    lean_ctor_set(v_reuseFailAlloc_9723_, 1, v_a_9712_);
                    v___x_9721_ = v_reuseFailAlloc_9723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_9711_ = v_tail_9715_;
                v_a_9712_ = v___x_9721_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9725_: *mut LeanObject = core::ptr::null_mut();
    v___x_9725_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_9725_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9727_: *mut LeanObject = core::ptr::null_mut();
    v___x_9726_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9727_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9727_, 0, v___x_9726_);
    return v___x_9727_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9731_: *mut LeanObject = core::ptr::null_mut();
    v___x_9728_ = lean_box(1);
    v___x_9729_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_9730_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9731_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_9731_, 0, v___x_9730_);
    lean_ctor_set(v___x_9731_, 1, v___x_9729_);
    lean_ctor_set(v___x_9731_, 2, v___x_9728_);
    return v___x_9731_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9736_: *mut LeanObject = core::ptr::null_mut();
    v___x_9734_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9735_ = lean_unsigned_to_nat(0);
    v___x_9736_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_9736_, 0, v___x_9735_);
    lean_ctor_set(v___x_9736_, 1, v___x_9735_);
    lean_ctor_set(v___x_9736_, 2, v___x_9735_);
    lean_ctor_set(v___x_9736_, 3, v___x_9735_);
    lean_ctor_set(v___x_9736_, 4, v___x_9734_);
    lean_ctor_set(v___x_9736_, 5, v___x_9734_);
    lean_ctor_set(v___x_9736_, 6, v___x_9734_);
    lean_ctor_set(v___x_9736_, 7, v___x_9734_);
    lean_ctor_set(v___x_9736_, 8, v___x_9734_);
    lean_ctor_set(v___x_9736_, 9, v___x_9734_);
    return v___x_9736_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9738_: *mut LeanObject = core::ptr::null_mut();
    v___x_9737_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9738_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_9738_, 0, v___x_9737_);
    lean_ctor_set(v___x_9738_, 1, v___x_9737_);
    lean_ctor_set(v___x_9738_, 2, v___x_9737_);
    lean_ctor_set(v___x_9738_, 3, v___x_9737_);
    lean_ctor_set(v___x_9738_, 4, v___x_9737_);
    lean_ctor_set(v___x_9738_, 5, v___x_9737_);
    return v___x_9738_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9740_: *mut LeanObject = core::ptr::null_mut();
    v___x_9739_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9740_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_9740_, 0, v___x_9739_);
    lean_ctor_set(v___x_9740_, 1, v___x_9739_);
    lean_ctor_set(v___x_9740_, 2, v___x_9739_);
    lean_ctor_set(v___x_9740_, 3, v___x_9739_);
    lean_ctor_set(v___x_9740_, 4, v___x_9739_);
    return v___x_9740_;
}
pub unsafe fn _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9746_: *mut LeanObject = core::ptr::null_mut();
    v___x_9741_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9742_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_9743_ = lean_box(1);
    v___x_9744_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9745_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
    v___x_9746_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_9746_, 0, v___x_9745_);
    lean_ctor_set(v___x_9746_, 1, v___x_9744_);
    lean_ctor_set(v___x_9746_, 2, v___x_9743_);
    lean_ctor_set(v___x_9746_, 3, v___x_9742_);
    lean_ctor_set(v___x_9746_, 4, v___x_9741_);
    return v___x_9746_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(
    mut v_name_9747_: *mut LeanObject,
    mut v___y_9748_: *mut LeanObject,
    mut v___y_9749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pre_9751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_9752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9755_: u8 = 0;
    let mut v___x_9756_: u8 = 0;
    let mut v___x_9757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9759_: u8 = 0;
    let mut v___y_9761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9762_: u8 = 0;
    let mut v___x_9763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9768_: u8 = 0;
    let mut v___x_9769_: u8 = 0;
    let mut v___x_9770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9771_: u8 = 0;
    let mut v___x_9772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9774_: u8 = 0;
    let mut v___x_9775_: u8 = 0;
    let mut v___x_9776_: u8 = 0;
    let mut v___x_9777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9778_: u64 = 0;
    let mut v___x_9779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9790_: u8 = 0;
    let mut v___x_9791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_9807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_9808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argKinds_9809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9812_: u8 = 0;
    let mut v___x_9814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9822_: u8 = 0;
    let mut v_a_9823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9832_: u8 = 0;
    let mut v___y_9834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9835_: u8 = 0;
    let mut v___x_9836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9841_: u8 = 0;
    let mut v___x_9842_: u8 = 0;
    let mut v___x_9843_: u8 = 0;
    let mut v___x_9844_: u8 = 0;
    let mut v___x_9845_: u8 = 0;
    let mut v___x_9846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9847_: u64 = 0;
    let mut v___x_9848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_9867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_9868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argKinds_9869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9872_: u8 = 0;
    let mut v___x_9874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9882_: u8 = 0;
    let mut v___x_9883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9888_: u8 = 0;
    let mut v_unused_9889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9892_: u8 = 0;
    let mut v_a_9893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9895_: u8 = 0;
    let mut v___x_9896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9897_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_name_9747_) == 1 {
                    v_pre_9751_ = lean_ctor_get(v_name_9747_, 0);
                    lean_inc_n(v_pre_9751_, 2);
                    v_str_9752_ = lean_ctor_get(v_name_9747_, 1);
                    v___x_9753_ = lean_st_ref_get(v___y_9749_);
                    v_env_9754_ = lean_ctor_get(v___x_9753_, 0);
                    lean_inc_ref(v_env_9754_);
                    lean_dec(v___x_9753_);
                    v___x_9755_ = 1;
                    v___x_9756_ =
                        l_Lean_Environment_contains(v_env_9754_, v_pre_9751_, v___x_9755_);
                    if v___x_9756_ == 0 {
                        lean_dec_ref_known(v_name_9747_, 2);
                        lean_dec(v_pre_9751_);
                        v___x_9757_ = lean_box((v___x_9756_) as usize);
                        v___x_9758_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_9758_, 0, v___x_9757_);
                        return v___x_9758_;
                    } else {
                        lean_inc_ref(v_str_9752_);
                        v___x_9759_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_9752_);
                        if v___x_9759_ == 0 {
                            v___x_9770_ = l_Lean_Meta_congrSimpSuffix___closed__0;
                            v___x_9771_ = lean_string_dec_eq(v_str_9752_, v___x_9770_);
                            if v___x_9771_ == 0 {
                                lean_dec_ref_known(v_name_9747_, 2);
                                lean_dec(v_pre_9751_);
                                v___x_9772_ = lean_box((v___x_9771_) as usize);
                                v___x_9773_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_9773_, 0, v___x_9772_);
                                return v___x_9773_;
                            } else {
                                v___x_9774_ = 1;
                                v___x_9775_ = 0;
                                v___x_9776_ = 2;
                                v___x_9777_ = lean_alloc_ctor(0, 0, (19) as u32);
                                lean_ctor_set_uint8(v___x_9777_, 0 as u32, v___x_9759_);
                                lean_ctor_set_uint8(v___x_9777_, 1 as u32, v___x_9759_);
                                lean_ctor_set_uint8(v___x_9777_, 2 as u32, v___x_9759_);
                                lean_ctor_set_uint8(v___x_9777_, 3 as u32, v___x_9759_);
                                lean_ctor_set_uint8(v___x_9777_, 4 as u32, v___x_9759_);
                                lean_ctor_set_uint8(v___x_9777_, 5 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 6 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 7 as u32, v___x_9759_);
                                lean_ctor_set_uint8(v___x_9777_, 8 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 9 as u32, v___x_9774_);
                                lean_ctor_set_uint8(v___x_9777_, 10 as u32, v___x_9775_);
                                lean_ctor_set_uint8(v___x_9777_, 11 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 12 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 13 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 14 as u32, v___x_9776_);
                                lean_ctor_set_uint8(v___x_9777_, 15 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 16 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 17 as u32, v___x_9771_);
                                lean_ctor_set_uint8(v___x_9777_, 18 as u32, v___x_9771_);
                                v___x_9778_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(
                                    v___x_9777_,
                                );
                                v___x_9779_ = lean_alloc_ctor(0, 1, (8) as u32);
                                lean_ctor_set(v___x_9779_, 0, v___x_9777_);
                                lean_ctor_set_uint64(
                                    v___x_9779_,
                                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                    v___x_9778_,
                                );
                                v___x_9780_ = lean_box(1);
                                v___x_9781_ = lean_unsigned_to_nat(0);
                                v___x_9782_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                                v___x_9783_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
                                v___x_9784_ = lean_box(0);
                                v___x_9785_ = lean_alloc_ctor(0, 7, (4) as u32);
                                lean_ctor_set(v___x_9785_, 0, v___x_9779_);
                                lean_ctor_set(v___x_9785_, 1, v___x_9780_);
                                lean_ctor_set(v___x_9785_, 2, v___x_9782_);
                                lean_ctor_set(v___x_9785_, 3, v___x_9783_);
                                lean_ctor_set(v___x_9785_, 4, v___x_9784_);
                                lean_ctor_set(v___x_9785_, 5, v___x_9781_);
                                lean_ctor_set(v___x_9785_, 6, v___x_9784_);
                                lean_ctor_set_uint8(
                                    v___x_9785_,
                                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                                    v___x_9759_,
                                );
                                lean_ctor_set_uint8(
                                    v___x_9785_,
                                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                                    v___x_9759_,
                                );
                                lean_ctor_set_uint8(
                                    v___x_9785_,
                                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                                    v___x_9759_,
                                );
                                lean_ctor_set_uint8(
                                    v___x_9785_,
                                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                                    v___x_9755_,
                                );
                                v___x_9786_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                                v___x_9787_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                                v___x_9788_ = lean_st_mk_ref(v___x_9787_);
                                lean_inc(v_pre_9751_);
                                v___x_9794_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_9751_, v___x_9785_, v___x_9788_, v___y_9748_, v___y_9749_);
                                if lean_obj_tag(v___x_9794_) == 0 {
                                    v_a_9795_ = lean_ctor_get(v___x_9794_, 0);
                                    lean_inc(v_a_9795_);
                                    lean_dec_ref_known(v___x_9794_, 1);
                                    v___x_9796_ = l_Lean_ConstantInfo_levelParams(v_a_9795_);
                                    lean_dec(v_a_9795_);
                                    v___x_9797_ = lean_box(0);
                                    lean_inc(v___x_9796_);
                                    v___x_9798_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_9796_, v___x_9797_);
                                    lean_inc(v_pre_9751_);
                                    v___x_9799_ = l_Lean_mkConst(v_pre_9751_, v___x_9798_);
                                    lean_inc_ref(v___x_9799_);
                                    v___x_9800_ = l_Lean_Meta_getFunInfo(
                                        v___x_9799_,
                                        v___x_9784_,
                                        v___x_9785_,
                                        v___x_9788_,
                                        v___y_9748_,
                                        v___y_9749_,
                                    );
                                    if lean_obj_tag(v___x_9800_) == 0 {
                                        v_a_9801_ = lean_ctor_get(v___x_9800_, 0);
                                        lean_inc(v_a_9801_);
                                        lean_dec_ref_known(v___x_9800_, 1);
                                        lean_inc_ref(v___x_9799_);
                                        v___x_9802_ = l_Lean_Meta_getCongrSimpKinds(
                                            v___x_9799_,
                                            v_a_9801_,
                                            v___x_9785_,
                                            v___x_9788_,
                                            v___y_9748_,
                                            v___y_9749_,
                                        );
                                        if lean_obj_tag(v___x_9802_) == 0 {
                                            v_a_9803_ = lean_ctor_get(v___x_9802_, 0);
                                            lean_inc(v_a_9803_);
                                            lean_dec_ref_known(v___x_9802_, 1);
                                            v___x_9804_ = l_Lean_Meta_mkCongrSimpCore_x3f(
                                                v___x_9799_,
                                                v_a_9801_,
                                                v_a_9803_,
                                                v___x_9755_,
                                                v___x_9785_,
                                                v___x_9788_,
                                                v___y_9748_,
                                                v___y_9749_,
                                            );
                                            if lean_obj_tag(v___x_9804_) == 0 {
                                                v_a_9805_ = lean_ctor_get(v___x_9804_, 0);
                                                lean_inc(v_a_9805_);
                                                lean_dec_ref_known(v___x_9804_, 1);
                                                if lean_obj_tag(v_a_9805_) == 1 {
                                                    v_val_9806_ = lean_ctor_get(v_a_9805_, 0);
                                                    lean_inc(v_val_9806_);
                                                    lean_dec_ref_known(v_a_9805_, 1);
                                                    v_type_9807_ = lean_ctor_get(v_val_9806_, 0);
                                                    v_proof_9808_ = lean_ctor_get(v_val_9806_, 1);
                                                    v_argKinds_9809_ =
                                                        lean_ctor_get(v_val_9806_, 2);
                                                    v_isSharedCheck_9822_ =
                                                        (!lean_is_exclusive(v_val_9806_)) as u8;
                                                    if v_isSharedCheck_9822_ == 0 {
                                                        v___x_9811_ = v_val_9806_;
                                                        v_isShared_9812_ = v_isSharedCheck_9822_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_argKinds_9809_);
                                                        lean_inc(v_proof_9808_);
                                                        lean_inc(v_type_9807_);
                                                        lean_dec(v_val_9806_);
                                                        v___x_9811_ = lean_box(0);
                                                        v_isShared_9812_ = v_isSharedCheck_9822_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_a_9805_);
                                                    lean_dec(v___x_9796_);
                                                    lean_dec_ref_known(v___x_9785_, 7);
                                                    lean_dec(v_pre_9751_);
                                                    lean_dec_ref_known(v_name_9747_, 2);
                                                    v_a_9790_ = v___x_9759_;
                                                    state = 3;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v___x_9796_);
                                                lean_dec(v___x_9788_);
                                                lean_dec_ref_known(v___x_9785_, 7);
                                                lean_dec_ref_known(v_name_9747_, 2);
                                                lean_dec(v_pre_9751_);
                                                v_a_9823_ = lean_ctor_get(v___x_9804_, 0);
                                                lean_inc(v_a_9823_);
                                                lean_dec_ref_known(v___x_9804_, 1);
                                                v_a_9767_ = v_a_9823_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_9801_);
                                            lean_dec_ref(v___x_9799_);
                                            lean_dec(v___x_9796_);
                                            lean_dec(v___x_9788_);
                                            lean_dec_ref_known(v___x_9785_, 7);
                                            lean_dec(v_pre_9751_);
                                            lean_dec_ref_known(v_name_9747_, 2);
                                            v_a_9824_ = lean_ctor_get(v___x_9802_, 0);
                                            lean_inc(v_a_9824_);
                                            lean_dec_ref_known(v___x_9802_, 1);
                                            v_a_9767_ = v_a_9824_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v___x_9799_);
                                        lean_dec(v___x_9796_);
                                        lean_dec(v___x_9788_);
                                        lean_dec_ref_known(v___x_9785_, 7);
                                        lean_dec_ref_known(v_name_9747_, 2);
                                        lean_dec(v_pre_9751_);
                                        v_a_9825_ = lean_ctor_get(v___x_9800_, 0);
                                        lean_inc(v_a_9825_);
                                        lean_dec_ref_known(v___x_9800_, 1);
                                        v_a_9767_ = v_a_9825_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_9788_);
                                    lean_dec_ref_known(v___x_9785_, 7);
                                    lean_dec_ref_known(v_name_9747_, 2);
                                    lean_dec(v_pre_9751_);
                                    v_a_9826_ = lean_ctor_get(v___x_9794_, 0);
                                    lean_inc(v_a_9826_);
                                    lean_dec_ref_known(v___x_9794_, 1);
                                    v_a_9767_ = v_a_9826_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            v___x_9827_ = lean_unsigned_to_nat(7);
                            v___x_9828_ = lean_unsigned_to_nat(0);
                            v___x_9829_ = lean_string_utf8_byte_size(v_str_9752_);
                            lean_inc_ref(v_str_9752_);
                            v___x_9830_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_9830_, 0, v_str_9752_);
                            lean_ctor_set(v___x_9830_, 1, v___x_9828_);
                            lean_ctor_set(v___x_9830_, 2, v___x_9829_);
                            v___x_9831_ =
                                l_String_Slice_Pos_nextn(v___x_9830_, v___x_9828_, v___x_9827_);
                            lean_dec_ref_known(v___x_9830_, 3);
                            v___x_9832_ = 0;
                            v___x_9843_ = 1;
                            v___x_9844_ = 0;
                            v___x_9845_ = 2;
                            v___x_9846_ = lean_alloc_ctor(0, 0, (19) as u32);
                            lean_ctor_set_uint8(v___x_9846_, 0 as u32, v___x_9832_);
                            lean_ctor_set_uint8(v___x_9846_, 1 as u32, v___x_9832_);
                            lean_ctor_set_uint8(v___x_9846_, 2 as u32, v___x_9832_);
                            lean_ctor_set_uint8(v___x_9846_, 3 as u32, v___x_9832_);
                            lean_ctor_set_uint8(v___x_9846_, 4 as u32, v___x_9832_);
                            lean_ctor_set_uint8(v___x_9846_, 5 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 6 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 7 as u32, v___x_9832_);
                            lean_ctor_set_uint8(v___x_9846_, 8 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 9 as u32, v___x_9843_);
                            lean_ctor_set_uint8(v___x_9846_, 10 as u32, v___x_9844_);
                            lean_ctor_set_uint8(v___x_9846_, 11 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 12 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 13 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 14 as u32, v___x_9845_);
                            lean_ctor_set_uint8(v___x_9846_, 15 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 16 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 17 as u32, v___x_9759_);
                            lean_ctor_set_uint8(v___x_9846_, 18 as u32, v___x_9759_);
                            v___x_9847_ =
                                l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_9846_);
                            v___x_9848_ = lean_alloc_ctor(0, 1, (8) as u32);
                            lean_ctor_set(v___x_9848_, 0, v___x_9846_);
                            lean_ctor_set_uint64(
                                v___x_9848_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_9847_,
                            );
                            v___x_9849_ = lean_box(1);
                            v___x_9850_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                            v___x_9851_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
                            v___x_9852_ = lean_box(0);
                            v___x_9853_ = lean_alloc_ctor(0, 7, (4) as u32);
                            lean_ctor_set(v___x_9853_, 0, v___x_9848_);
                            lean_ctor_set(v___x_9853_, 1, v___x_9849_);
                            lean_ctor_set(v___x_9853_, 2, v___x_9850_);
                            lean_ctor_set(v___x_9853_, 3, v___x_9851_);
                            lean_ctor_set(v___x_9853_, 4, v___x_9852_);
                            lean_ctor_set(v___x_9853_, 5, v___x_9828_);
                            lean_ctor_set(v___x_9853_, 6, v___x_9852_);
                            lean_ctor_set_uint8(
                                v___x_9853_,
                                (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                                v___x_9832_,
                            );
                            lean_ctor_set_uint8(
                                v___x_9853_,
                                (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                                v___x_9832_,
                            );
                            lean_ctor_set_uint8(
                                v___x_9853_,
                                (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                                v___x_9832_,
                            );
                            lean_ctor_set_uint8(
                                v___x_9853_,
                                (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                                v___x_9755_,
                            );
                            v___x_9854_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                            v___x_9855_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                            v___x_9856_ = lean_st_mk_ref(v___x_9855_);
                            lean_inc(v_pre_9751_);
                            v___x_9857_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_9751_, v___x_9853_, v___x_9856_, v___y_9748_, v___y_9749_);
                            if lean_obj_tag(v___x_9857_) == 0 {
                                v_a_9858_ = lean_ctor_get(v___x_9857_, 0);
                                lean_inc(v_a_9858_);
                                lean_dec_ref_known(v___x_9857_, 1);
                                lean_inc_ref(v_str_9752_);
                                v___x_9859_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_9859_, 0, v_str_9752_);
                                lean_ctor_set(v___x_9859_, 1, v___x_9831_);
                                lean_ctor_set(v___x_9859_, 2, v___x_9829_);
                                v___x_9860_ = l_String_Slice_toNat_x21(v___x_9859_);
                                lean_dec_ref_known(v___x_9859_, 3);
                                v___x_9861_ = l_Lean_ConstantInfo_levelParams(v_a_9858_);
                                lean_dec(v_a_9858_);
                                v___x_9862_ = lean_box(0);
                                lean_inc(v___x_9861_);
                                v___x_9863_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_9861_, v___x_9862_);
                                lean_inc(v_pre_9751_);
                                v___x_9864_ = l_Lean_mkConst(v_pre_9751_, v___x_9863_);
                                v___x_9865_ = l_Lean_Meta_mkHCongrWithArity(
                                    v___x_9864_,
                                    v___x_9860_,
                                    v___x_9853_,
                                    v___x_9856_,
                                    v___y_9748_,
                                    v___y_9749_,
                                );
                                if lean_obj_tag(v___x_9865_) == 0 {
                                    v_a_9866_ = lean_ctor_get(v___x_9865_, 0);
                                    lean_inc(v_a_9866_);
                                    lean_dec_ref_known(v___x_9865_, 1);
                                    v_type_9867_ = lean_ctor_get(v_a_9866_, 0);
                                    v_proof_9868_ = lean_ctor_get(v_a_9866_, 1);
                                    v_argKinds_9869_ = lean_ctor_get(v_a_9866_, 2);
                                    v_isSharedCheck_9892_ = (!lean_is_exclusive(v_a_9866_)) as u8;
                                    if v_isSharedCheck_9892_ == 0 {
                                        v___x_9871_ = v_a_9866_;
                                        v_isShared_9872_ = v_isSharedCheck_9892_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_argKinds_9869_);
                                        lean_inc(v_proof_9868_);
                                        lean_inc(v_type_9867_);
                                        lean_dec(v_a_9866_);
                                        v___x_9871_ = lean_box(0);
                                        v_isShared_9872_ = v_isSharedCheck_9892_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_9861_);
                                    lean_dec(v___x_9856_);
                                    lean_dec_ref_known(v___x_9853_, 7);
                                    lean_dec_ref_known(v_name_9747_, 2);
                                    lean_dec(v_pre_9751_);
                                    v_a_9893_ = lean_ctor_get(v___x_9865_, 0);
                                    lean_inc(v_a_9893_);
                                    lean_dec_ref_known(v___x_9865_, 1);
                                    v_a_9840_ = v_a_9893_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_9856_);
                                lean_dec_ref_known(v___x_9853_, 7);
                                lean_dec(v___x_9831_);
                                lean_dec_ref_known(v_name_9747_, 2);
                                lean_dec(v_pre_9751_);
                                v_a_9894_ = lean_ctor_get(v___x_9857_, 0);
                                lean_inc(v_a_9894_);
                                lean_dec_ref_known(v___x_9857_, 1);
                                v_a_9840_ = v_a_9894_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_name_9747_);
                    v___x_9895_ = 0;
                    v___x_9896_ = lean_box((v___x_9895_) as usize);
                    v___x_9897_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9897_, 0, v___x_9896_);
                    return v___x_9897_;
                }
            }
            1 => {
                if v___y_9762_ == 0 {
                    lean_dec_ref(v___y_9761_);
                    v___x_9763_ = lean_box((v___x_9759_) as usize);
                    v___x_9764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9764_, 0, v___x_9763_);
                    return v___x_9764_;
                } else {
                    v___x_9765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9765_, 0, v___y_9761_);
                    return v___x_9765_;
                }
            }
            2 => {
                v___x_9768_ = l_Lean_Exception_isInterrupt(v_a_9767_);
                if v___x_9768_ == 0 {
                    lean_inc_ref(v_a_9767_);
                    v___x_9769_ = l_Lean_Exception_isRuntime(v_a_9767_);
                    v___y_9761_ = v_a_9767_;
                    v___y_9762_ = v___x_9769_;
                    state = 1;
                    continue;
                } else {
                    v___y_9761_ = v_a_9767_;
                    v___y_9762_ = v___x_9768_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_9791_ = lean_st_ref_get(v___x_9788_);
                lean_dec(v___x_9788_);
                lean_dec(v___x_9791_);
                v___x_9792_ = lean_box((v_a_9790_) as usize);
                v___x_9793_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9793_, 0, v___x_9792_);
                return v___x_9793_;
            }
            4 => {
                lean_inc_ref(v_name_9747_);
                if v_isShared_9812_ == 0 {
                    lean_ctor_set(v___x_9811_, 2, v_type_9807_);
                    lean_ctor_set(v___x_9811_, 1, v___x_9796_);
                    lean_ctor_set(v___x_9811_, 0, v_name_9747_);
                    v___x_9814_ = v___x_9811_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9821_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9821_, 0, v_name_9747_);
                    lean_ctor_set(v_reuseFailAlloc_9821_, 1, v___x_9796_);
                    lean_ctor_set(v_reuseFailAlloc_9821_, 2, v_type_9807_);
                    v___x_9814_ = v_reuseFailAlloc_9821_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v_name_9747_, 2);
                v___x_9815_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_9815_, 0, v_name_9747_);
                lean_ctor_set(v___x_9815_, 1, v___x_9797_);
                v___x_9816_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_9816_, 0, v___x_9814_);
                lean_ctor_set(v___x_9816_, 1, v_proof_9808_);
                lean_ctor_set(v___x_9816_, 2, v___x_9815_);
                v___x_9817_ = lean_box((v___x_9759_) as usize);
                v___f_9818_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_9818_, 0, v___x_9816_);
                lean_closure_set(v___f_9818_, 1, v___x_9817_);
                lean_closure_set(v___f_9818_, 2, v_name_9747_);
                lean_closure_set(v___f_9818_, 3, v_argKinds_9809_);
                lean_closure_set(v___f_9818_, 4, v___x_9786_);
                v___x_9819_ = l_Lean_Meta_realizeConst(
                    v_pre_9751_,
                    v_name_9747_,
                    v___f_9818_,
                    v___x_9785_,
                    v___x_9788_,
                    v___y_9748_,
                    v___y_9749_,
                );
                lean_dec_ref_known(v___x_9785_, 7);
                if lean_obj_tag(v___x_9819_) == 0 {
                    lean_dec_ref_known(v___x_9819_, 1);
                    v_a_9790_ = v___x_9755_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_9788_);
                    v_a_9820_ = lean_ctor_get(v___x_9819_, 0);
                    lean_inc(v_a_9820_);
                    lean_dec_ref_known(v___x_9819_, 1);
                    v_a_9767_ = v_a_9820_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v___y_9835_ == 0 {
                    lean_dec_ref(v___y_9834_);
                    v___x_9836_ = lean_box((v___x_9832_) as usize);
                    v___x_9837_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9837_, 0, v___x_9836_);
                    return v___x_9837_;
                } else {
                    v___x_9838_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9838_, 0, v___y_9834_);
                    return v___x_9838_;
                }
            }
            7 => {
                v___x_9841_ = l_Lean_Exception_isInterrupt(v_a_9840_);
                if v___x_9841_ == 0 {
                    lean_inc_ref(v_a_9840_);
                    v___x_9842_ = l_Lean_Exception_isRuntime(v_a_9840_);
                    v___y_9834_ = v_a_9840_;
                    v___y_9835_ = v___x_9842_;
                    state = 6;
                    continue;
                } else {
                    v___y_9834_ = v_a_9840_;
                    v___y_9835_ = v___x_9841_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v_name_9747_);
                if v_isShared_9872_ == 0 {
                    lean_ctor_set(v___x_9871_, 2, v_type_9867_);
                    lean_ctor_set(v___x_9871_, 1, v___x_9861_);
                    lean_ctor_set(v___x_9871_, 0, v_name_9747_);
                    v___x_9874_ = v___x_9871_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_9891_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9891_, 0, v_name_9747_);
                    lean_ctor_set(v_reuseFailAlloc_9891_, 1, v___x_9861_);
                    lean_ctor_set(v_reuseFailAlloc_9891_, 2, v_type_9867_);
                    v___x_9874_ = v_reuseFailAlloc_9891_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_inc_ref_n(v_name_9747_, 2);
                v___x_9875_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_9875_, 0, v_name_9747_);
                lean_ctor_set(v___x_9875_, 1, v___x_9862_);
                v___x_9876_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_9876_, 0, v___x_9874_);
                lean_ctor_set(v___x_9876_, 1, v_proof_9868_);
                lean_ctor_set(v___x_9876_, 2, v___x_9875_);
                v___x_9877_ = lean_box((v___x_9832_) as usize);
                v___f_9878_ = lean_alloc_closure(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_9878_, 0, v___x_9876_);
                lean_closure_set(v___f_9878_, 1, v___x_9877_);
                lean_closure_set(v___f_9878_, 2, v_name_9747_);
                lean_closure_set(v___f_9878_, 3, v_argKinds_9869_);
                lean_closure_set(v___f_9878_, 4, v___x_9854_);
                v___x_9879_ = l_Lean_Meta_realizeConst(
                    v_pre_9751_,
                    v_name_9747_,
                    v___f_9878_,
                    v___x_9853_,
                    v___x_9856_,
                    v___y_9748_,
                    v___y_9749_,
                );
                lean_dec_ref_known(v___x_9853_, 7);
                if lean_obj_tag(v___x_9879_) == 0 {
                    v_isSharedCheck_9888_ = (!lean_is_exclusive(v___x_9879_)) as u8;
                    if v_isSharedCheck_9888_ == 0 {
                        v_unused_9889_ = lean_ctor_get(v___x_9879_, 0);
                        lean_dec(v_unused_9889_);
                        v___x_9881_ = v___x_9879_;
                        v_isShared_9882_ = v_isSharedCheck_9888_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec(v___x_9879_);
                        v___x_9881_ = lean_box(0);
                        v_isShared_9882_ = v_isSharedCheck_9888_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v___x_9856_);
                    v_a_9890_ = lean_ctor_get(v___x_9879_, 0);
                    lean_inc(v_a_9890_);
                    lean_dec_ref_known(v___x_9879_, 1);
                    v_a_9840_ = v_a_9890_;
                    state = 7;
                    continue;
                }
            }
            10 => {
                v___x_9883_ = lean_st_ref_get(v___x_9856_);
                lean_dec(v___x_9856_);
                lean_dec(v___x_9883_);
                v___x_9884_ = lean_box((v___x_9755_) as usize);
                if v_isShared_9882_ == 0 {
                    lean_ctor_set(v___x_9881_, 0, v___x_9884_);
                    v___x_9886_ = v___x_9881_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_9887_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9887_, 0, v___x_9884_);
                    v___x_9886_ = v_reuseFailAlloc_9887_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_9886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(
    mut v_name_9898_: *mut LeanObject,
    mut v___y_9899_: *mut LeanObject,
    mut v___y_9900_: *mut LeanObject,
    mut v___y_9901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9902_: *mut LeanObject = core::ptr::null_mut();
    v_res_9902_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_9898_, v___y_9899_, v___y_9900_);
    lean_dec(v___y_9900_);
    lean_dec_ref(v___y_9899_);
    return v_res_9902_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_9905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9906_: *mut LeanObject = core::ptr::null_mut();
    v___f_9905_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
    v___x_9906_ = l_Lean_registerReservedNameAction(v___f_9905_);
    return v___x_9906_;
}
pub unsafe fn l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(
    mut v_a_9907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9908_: *mut LeanObject = core::ptr::null_mut();
    v_res_9908_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
    return v_res_9908_;
}
pub unsafe fn l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(
    mut v_msg_9909_: *mut LeanObject,
    mut v___y_9910_: *mut LeanObject,
    mut v___y_9911_: *mut LeanObject,
    mut v___y_9912_: *mut LeanObject,
    mut v___y_9913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830__overap_9916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9917_: *mut LeanObject = core::ptr::null_mut();
    v___f_9915_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0;
    v___x_1830__overap_9916_ = lean_panic_fn_borrowed(v___f_9915_, v_msg_9909_);
    lean_inc(v___y_9913_);
    lean_inc_ref(v___y_9912_);
    lean_inc(v___y_9911_);
    lean_inc_ref(v___y_9910_);
    v___x_9917_ = lean_apply_5(
        v___x_1830__overap_9916_,
        v___y_9910_,
        v___y_9911_,
        v___y_9912_,
        v___y_9913_,
        lean_box(0),
    );
    return v___x_9917_;
}
pub unsafe fn l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(
    mut v_msg_9918_: *mut LeanObject,
    mut v___y_9919_: *mut LeanObject,
    mut v___y_9920_: *mut LeanObject,
    mut v___y_9921_: *mut LeanObject,
    mut v___y_9922_: *mut LeanObject,
    mut v___y_9923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9924_: *mut LeanObject = core::ptr::null_mut();
    v_res_9924_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(
        v_msg_9918_,
        v___y_9919_,
        v___y_9920_,
        v___y_9921_,
        v___y_9922_,
    );
    lean_dec(v___y_9922_);
    lean_dec_ref(v___y_9921_);
    lean_dec(v___y_9920_);
    lean_dec_ref(v___y_9919_);
    return v_res_9924_;
}
pub unsafe fn _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_9926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9931_: *mut LeanObject = core::ptr::null_mut();
    v___x_9926_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2;
    v___x_9927_ = lean_unsigned_to_nat(8);
    v___x_9928_ = lean_unsigned_to_nat(461);
    v___x_9929_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0;
    v___x_9930_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0;
    v___x_9931_ = l_mkPanicMessageWithDecl(
        v___x_9930_,
        v___x_9929_,
        v___x_9928_,
        v___x_9927_,
        v___x_9926_,
    );
    return v___x_9931_;
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(
    mut v_thmName_9932_: *mut LeanObject,
    mut v_levels_9933_: *mut LeanObject,
    mut v___x_9934_: *mut LeanObject,
    mut v_____r_9935_: *mut LeanObject,
    mut v___y_9936_: *mut LeanObject,
    mut v___y_9937_: *mut LeanObject,
    mut v___y_9938_: *mut LeanObject,
    mut v___y_9939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9946_: u8 = 0;
    let mut v___x_9947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_9950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_9951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9952_: u8 = 0;
    let mut v___x_9953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9957_: u8 = 0;
    let mut v___x_9958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9966_: u8 = 0;
    let mut v___x_9967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9972_: u8 = 0;
    let mut v___x_9973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9977_: u8 = 0;
    let mut v_a_9978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9981_: u8 = 0;
    let mut v___x_9983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9985_: u8 = 0;
    let mut v_isSharedCheck_9986_: u8 = 0;
    let mut v_a_9987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9990_: u8 = 0;
    let mut v___x_9992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_thmName_9932_);
                v___x_9941_ = l_Lean_mkConst(v_thmName_9932_, v_levels_9933_);
                lean_inc(v___y_9939_);
                lean_inc_ref(v___y_9938_);
                lean_inc(v___y_9937_);
                lean_inc_ref(v___y_9936_);
                lean_inc_ref(v___x_9941_);
                v___x_9942_ = lean_infer_type(
                    v___x_9941_,
                    v___y_9936_,
                    v___y_9937_,
                    v___y_9938_,
                    v___y_9939_,
                );
                if lean_obj_tag(v___x_9942_) == 0 {
                    v_a_9943_ = lean_ctor_get(v___x_9942_, 0);
                    v_isSharedCheck_9986_ = (!lean_is_exclusive(v___x_9942_)) as u8;
                    if v_isSharedCheck_9986_ == 0 {
                        v___x_9945_ = v___x_9942_;
                        v_isShared_9946_ = v_isSharedCheck_9986_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9943_);
                        lean_dec(v___x_9942_);
                        v___x_9945_ = lean_box(0);
                        v_isShared_9946_ = v_isSharedCheck_9986_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_9941_);
                    lean_dec_ref(v___x_9934_);
                    lean_dec(v_thmName_9932_);
                    v_a_9987_ = lean_ctor_get(v___x_9942_, 0);
                    v_isSharedCheck_9994_ = (!lean_is_exclusive(v___x_9942_)) as u8;
                    if v_isSharedCheck_9994_ == 0 {
                        v___x_9989_ = v___x_9942_;
                        v_isShared_9990_ = v_isSharedCheck_9994_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_9987_);
                        lean_dec(v___x_9942_);
                        v___x_9989_ = lean_box(0);
                        v_isShared_9990_ = v_isSharedCheck_9994_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9947_ = lean_st_ref_get(v___y_9939_);
                v_env_9948_ = lean_ctor_get(v___x_9947_, 0);
                lean_inc_ref(v_env_9948_);
                lean_dec(v___x_9947_);
                v___x_9949_ = l_Lean_Meta_congrKindsExt;
                v_toEnvExtension_9950_ = lean_ctor_get(v___x_9949_, 0);
                v_asyncMode_9951_ = lean_ctor_get(v_toEnvExtension_9950_, 2);
                v___x_9952_ = 0;
                v___x_9953_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                    v___x_9934_,
                    v___x_9949_,
                    v_env_9948_,
                    v_thmName_9932_,
                    v_asyncMode_9951_,
                    v___x_9952_,
                );
                if lean_obj_tag(v___x_9953_) == 1 {
                    v_val_9954_ = lean_ctor_get(v___x_9953_, 0);
                    v_isSharedCheck_9966_ = (!lean_is_exclusive(v___x_9953_)) as u8;
                    if v_isSharedCheck_9966_ == 0 {
                        v___x_9956_ = v___x_9953_;
                        v_isShared_9957_ = v_isSharedCheck_9966_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_9954_);
                        lean_dec(v___x_9953_);
                        v___x_9956_ = lean_box(0);
                        v_isShared_9957_ = v_isSharedCheck_9966_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_9953_);
                    lean_del_object(v___x_9945_);
                    lean_dec(v_a_9943_);
                    lean_dec_ref(v___x_9941_);
                    v___x_9967_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1,
                    );
                    v___x_9968_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(
                        v___x_9967_,
                        v___y_9936_,
                        v___y_9937_,
                        v___y_9938_,
                        v___y_9939_,
                    );
                    if lean_obj_tag(v___x_9968_) == 0 {
                        v_a_9969_ = lean_ctor_get(v___x_9968_, 0);
                        v_isSharedCheck_9977_ = (!lean_is_exclusive(v___x_9968_)) as u8;
                        if v_isSharedCheck_9977_ == 0 {
                            v___x_9971_ = v___x_9968_;
                            v_isShared_9972_ = v_isSharedCheck_9977_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_9969_);
                            lean_dec(v___x_9968_);
                            v___x_9971_ = lean_box(0);
                            v_isShared_9972_ = v_isSharedCheck_9977_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_9978_ = lean_ctor_get(v___x_9968_, 0);
                        v_isSharedCheck_9985_ = (!lean_is_exclusive(v___x_9968_)) as u8;
                        if v_isSharedCheck_9985_ == 0 {
                            v___x_9980_ = v___x_9968_;
                            v_isShared_9981_ = v_isSharedCheck_9985_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_9978_);
                            lean_dec(v___x_9968_);
                            v___x_9980_ = lean_box(0);
                            v_isShared_9981_ = v_isSharedCheck_9985_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_9958_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_9958_, 0, v_a_9943_);
                lean_ctor_set(v___x_9958_, 1, v___x_9941_);
                lean_ctor_set(v___x_9958_, 2, v_val_9954_);
                if v_isShared_9957_ == 0 {
                    lean_ctor_set(v___x_9956_, 0, v___x_9958_);
                    v___x_9960_ = v___x_9956_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9965_, 0, v___x_9958_);
                    v___x_9960_ = v_reuseFailAlloc_9965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9961_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9961_, 0, v___x_9960_);
                if v_isShared_9946_ == 0 {
                    lean_ctor_set(v___x_9945_, 0, v___x_9961_);
                    v___x_9963_ = v___x_9945_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9964_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9964_, 0, v___x_9961_);
                    v___x_9963_ = v_reuseFailAlloc_9964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9963_;
            }
            5 => {
                v___x_9973_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9973_, 0, v_a_9969_);
                if v_isShared_9972_ == 0 {
                    lean_ctor_set(v___x_9971_, 0, v___x_9973_);
                    v___x_9975_ = v___x_9971_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9976_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9976_, 0, v___x_9973_);
                    v___x_9975_ = v_reuseFailAlloc_9976_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9975_;
            }
            7 => {
                if v_isShared_9981_ == 0 {
                    v___x_9983_ = v___x_9980_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9984_, 0, v_a_9978_);
                    v___x_9983_ = v_reuseFailAlloc_9984_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9983_;
            }
            9 => {
                if v_isShared_9990_ == 0 {
                    v___x_9992_ = v___x_9989_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9993_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9993_, 0, v_a_9987_);
                    v___x_9992_ = v_reuseFailAlloc_9993_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_9992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(
    mut v_thmName_9995_: *mut LeanObject,
    mut v_levels_9996_: *mut LeanObject,
    mut v___x_9997_: *mut LeanObject,
    mut v_____r_9998_: *mut LeanObject,
    mut v___y_9999_: *mut LeanObject,
    mut v___y_10000_: *mut LeanObject,
    mut v___y_10001_: *mut LeanObject,
    mut v___y_10002_: *mut LeanObject,
    mut v___y_10003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10004_: *mut LeanObject = core::ptr::null_mut();
    v_res_10004_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(
        v_thmName_9995_,
        v_levels_9996_,
        v___x_9997_,
        v_____r_9998_,
        v___y_9999_,
        v___y_10000_,
        v___y_10001_,
        v___y_10002_,
    );
    lean_dec(v___y_10002_);
    lean_dec_ref(v___y_10001_);
    lean_dec(v___y_10000_);
    lean_dec_ref(v___y_9999_);
    return v_res_10004_;
}
pub unsafe fn _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_10005_: *mut LeanObject = core::ptr::null_mut();
    v___x_10005_ = l_Array_instInhabited(lean_box(0));
    return v___x_10005_;
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArityForConst_x3f(
    mut v_declName_10006_: *mut LeanObject,
    mut v_levels_10007_: *mut LeanObject,
    mut v_numArgs_10008_: *mut LeanObject,
    mut v_a_10009_: *mut LeanObject,
    mut v_a_10010_: *mut LeanObject,
    mut v_a_10011_: *mut LeanObject,
    mut v_a_10012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_10015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10016_: u8 = 0;
    let mut v___x_10017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10022_: u8 = 0;
    let mut v___x_10023_: u8 = 0;
    let mut v___y_10025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10029_: u8 = 0;
    let mut v_a_10030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10034_: u8 = 0;
    let mut v_a_10035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_10037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suffix_10041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmName_10042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10043_: u8 = 0;
    let mut v___x_10044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10049_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10036_ = lean_st_ref_get(v_a_10012_);
                v_env_10037_ = lean_ctor_get(v___x_10036_, 0);
                lean_inc_ref(v_env_10037_);
                lean_dec(v___x_10036_);
                v___x_10038_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once
                    ),
                    _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0,
                );
                v___x_10039_ = l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0;
                v___x_10040_ = l_Nat_reprFast(v_numArgs_10008_);
                v_suffix_10041_ = lean_string_append(v___x_10039_, v___x_10040_);
                lean_dec_ref(v___x_10040_);
                v_thmName_10042_ = l_Lean_Name_str___override(v_declName_10006_, v_suffix_10041_);
                v___x_10043_ = l_Lean_Environment_containsOnBranch(v_env_10037_, v_thmName_10042_);
                lean_dec_ref(v_env_10037_);
                if v___x_10043_ == 0 {
                    lean_inc(v_thmName_10042_);
                    v___x_10044_ =
                        l_Lean_executeReservedNameAction(v_thmName_10042_, v_a_10011_, v_a_10012_);
                    if lean_obj_tag(v___x_10044_) == 0 {
                        lean_dec_ref_known(v___x_10044_, 1);
                        v___x_10045_ = lean_box(0);
                        v___x_10046_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(
                            v_thmName_10042_,
                            v_levels_10007_,
                            v___x_10038_,
                            v___x_10045_,
                            v_a_10009_,
                            v_a_10010_,
                            v_a_10011_,
                            v_a_10012_,
                        );
                        v___y_10025_ = v___x_10046_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_thmName_10042_);
                        lean_dec(v_levels_10007_);
                        v_a_10047_ = lean_ctor_get(v___x_10044_, 0);
                        lean_inc(v_a_10047_);
                        lean_dec_ref_known(v___x_10044_, 1);
                        v_a_10021_ = v_a_10047_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_10048_ = lean_box(0);
                    v___x_10049_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(
                        v_thmName_10042_,
                        v_levels_10007_,
                        v___x_10038_,
                        v___x_10048_,
                        v_a_10009_,
                        v_a_10010_,
                        v_a_10011_,
                        v_a_10012_,
                    );
                    v___y_10025_ = v___x_10049_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_10016_ == 0 {
                    lean_dec_ref(v___y_10015_);
                    v___x_10017_ = lean_box(0);
                    v___x_10018_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_10018_, 0, v___x_10017_);
                    return v___x_10018_;
                } else {
                    v___x_10019_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10019_, 0, v___y_10015_);
                    return v___x_10019_;
                }
            }
            2 => {
                v___x_10022_ = l_Lean_Exception_isInterrupt(v_a_10021_);
                if v___x_10022_ == 0 {
                    lean_inc_ref(v_a_10021_);
                    v___x_10023_ = l_Lean_Exception_isRuntime(v_a_10021_);
                    v___y_10015_ = v_a_10021_;
                    v___y_10016_ = v___x_10023_;
                    state = 1;
                    continue;
                } else {
                    v___y_10015_ = v_a_10021_;
                    v___y_10016_ = v___x_10022_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v___y_10025_) == 0 {
                    v_a_10026_ = lean_ctor_get(v___y_10025_, 0);
                    v_isSharedCheck_10034_ = (!lean_is_exclusive(v___y_10025_)) as u8;
                    if v_isSharedCheck_10034_ == 0 {
                        v___x_10028_ = v___y_10025_;
                        v_isShared_10029_ = v_isSharedCheck_10034_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10026_);
                        lean_dec(v___y_10025_);
                        v___x_10028_ = lean_box(0);
                        v_isShared_10029_ = v_isSharedCheck_10034_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_10035_ = lean_ctor_get(v___y_10025_, 0);
                    lean_inc(v_a_10035_);
                    lean_dec_ref_known(v___y_10025_, 1);
                    v_a_10021_ = v_a_10035_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_a_10030_ = lean_ctor_get(v_a_10026_, 0);
                lean_inc(v_a_10030_);
                lean_dec(v_a_10026_);
                if v_isShared_10029_ == 0 {
                    lean_ctor_set(v___x_10028_, 0, v_a_10030_);
                    v___x_10032_ = v___x_10028_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10033_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10033_, 0, v_a_10030_);
                    v___x_10032_ = v_reuseFailAlloc_10033_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(
    mut v_declName_10050_: *mut LeanObject,
    mut v_levels_10051_: *mut LeanObject,
    mut v_numArgs_10052_: *mut LeanObject,
    mut v_a_10053_: *mut LeanObject,
    mut v_a_10054_: *mut LeanObject,
    mut v_a_10055_: *mut LeanObject,
    mut v_a_10056_: *mut LeanObject,
    mut v_a_10057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10058_: *mut LeanObject = core::ptr::null_mut();
    v_res_10058_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(
        v_declName_10050_,
        v_levels_10051_,
        v_numArgs_10052_,
        v_a_10053_,
        v_a_10054_,
        v_a_10055_,
        v_a_10056_,
    );
    lean_dec(v_a_10056_);
    lean_dec_ref(v_a_10055_);
    lean_dec(v_a_10054_);
    lean_dec_ref(v_a_10053_);
    return v_res_10058_;
}
pub unsafe fn l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(
    mut v_____r_10061_: *mut LeanObject,
    mut v___y_10062_: *mut LeanObject,
    mut v___y_10063_: *mut LeanObject,
    mut v___y_10064_: *mut LeanObject,
    mut v___y_10065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10068_: *mut LeanObject = core::ptr::null_mut();
    v___x_10067_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0;
    v___x_10068_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10068_, 0, v___x_10067_);
    return v___x_10068_;
}
pub unsafe fn l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(
    mut v_____r_10069_: *mut LeanObject,
    mut v___y_10070_: *mut LeanObject,
    mut v___y_10071_: *mut LeanObject,
    mut v___y_10072_: *mut LeanObject,
    mut v___y_10073_: *mut LeanObject,
    mut v___y_10074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10075_: *mut LeanObject = core::ptr::null_mut();
    v_res_10075_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(
        v_____r_10069_,
        v___y_10070_,
        v___y_10071_,
        v___y_10072_,
        v___y_10073_,
    );
    lean_dec(v___y_10073_);
    lean_dec_ref(v___y_10072_);
    lean_dec(v___y_10071_);
    lean_dec_ref(v___y_10070_);
    return v_res_10075_;
}
pub unsafe fn _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_10077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10082_: *mut LeanObject = core::ptr::null_mut();
    v___x_10077_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2;
    v___x_10078_ = lean_unsigned_to_nat(8);
    v___x_10079_ = lean_unsigned_to_nat(478);
    v___x_10080_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0;
    v___x_10081_ =
        l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0;
    v___x_10082_ = l_mkPanicMessageWithDecl(
        v___x_10081_,
        v___x_10080_,
        v___x_10079_,
        v___x_10078_,
        v___x_10077_,
    );
    return v___x_10082_;
}
pub unsafe fn l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(
    mut v_thmName_10083_: *mut LeanObject,
    mut v_levels_10084_: *mut LeanObject,
    mut v___x_10085_: *mut LeanObject,
    mut v_____r_10086_: *mut LeanObject,
    mut v___y_10087_: *mut LeanObject,
    mut v___y_10088_: *mut LeanObject,
    mut v___y_10089_: *mut LeanObject,
    mut v___y_10090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10097_: u8 = 0;
    let mut v___x_10098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_10099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_10101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_10102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10103_: u8 = 0;
    let mut v___x_10104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10108_: u8 = 0;
    let mut v___x_10109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10117_: u8 = 0;
    let mut v___x_10118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10123_: u8 = 0;
    let mut v___x_10124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10128_: u8 = 0;
    let mut v_a_10129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10132_: u8 = 0;
    let mut v___x_10134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10136_: u8 = 0;
    let mut v_isSharedCheck_10137_: u8 = 0;
    let mut v_a_10138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10141_: u8 = 0;
    let mut v___x_10143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_thmName_10083_);
                v___x_10092_ = l_Lean_mkConst(v_thmName_10083_, v_levels_10084_);
                lean_inc(v___y_10090_);
                lean_inc_ref(v___y_10089_);
                lean_inc(v___y_10088_);
                lean_inc_ref(v___y_10087_);
                lean_inc_ref(v___x_10092_);
                v___x_10093_ = lean_infer_type(
                    v___x_10092_,
                    v___y_10087_,
                    v___y_10088_,
                    v___y_10089_,
                    v___y_10090_,
                );
                if lean_obj_tag(v___x_10093_) == 0 {
                    v_a_10094_ = lean_ctor_get(v___x_10093_, 0);
                    v_isSharedCheck_10137_ = (!lean_is_exclusive(v___x_10093_)) as u8;
                    if v_isSharedCheck_10137_ == 0 {
                        v___x_10096_ = v___x_10093_;
                        v_isShared_10097_ = v_isSharedCheck_10137_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10094_);
                        lean_dec(v___x_10093_);
                        v___x_10096_ = lean_box(0);
                        v_isShared_10097_ = v_isSharedCheck_10137_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_10092_);
                    lean_dec_ref(v___x_10085_);
                    lean_dec(v_thmName_10083_);
                    v_a_10138_ = lean_ctor_get(v___x_10093_, 0);
                    v_isSharedCheck_10145_ = (!lean_is_exclusive(v___x_10093_)) as u8;
                    if v_isSharedCheck_10145_ == 0 {
                        v___x_10140_ = v___x_10093_;
                        v_isShared_10141_ = v_isSharedCheck_10145_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_10138_);
                        lean_dec(v___x_10093_);
                        v___x_10140_ = lean_box(0);
                        v_isShared_10141_ = v_isSharedCheck_10145_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10098_ = lean_st_ref_get(v___y_10090_);
                v_env_10099_ = lean_ctor_get(v___x_10098_, 0);
                lean_inc_ref(v_env_10099_);
                lean_dec(v___x_10098_);
                v___x_10100_ = l_Lean_Meta_congrKindsExt;
                v_toEnvExtension_10101_ = lean_ctor_get(v___x_10100_, 0);
                v_asyncMode_10102_ = lean_ctor_get(v_toEnvExtension_10101_, 2);
                v___x_10103_ = 0;
                v___x_10104_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                    v___x_10085_,
                    v___x_10100_,
                    v_env_10099_,
                    v_thmName_10083_,
                    v_asyncMode_10102_,
                    v___x_10103_,
                );
                if lean_obj_tag(v___x_10104_) == 1 {
                    v_val_10105_ = lean_ctor_get(v___x_10104_, 0);
                    v_isSharedCheck_10117_ = (!lean_is_exclusive(v___x_10104_)) as u8;
                    if v_isSharedCheck_10117_ == 0 {
                        v___x_10107_ = v___x_10104_;
                        v_isShared_10108_ = v_isSharedCheck_10117_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_10105_);
                        lean_dec(v___x_10104_);
                        v___x_10107_ = lean_box(0);
                        v_isShared_10108_ = v_isSharedCheck_10117_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_10104_);
                    lean_del_object(v___x_10096_);
                    lean_dec(v_a_10094_);
                    lean_dec_ref(v___x_10092_);
                    v___x_10118_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once
                        ),
                        _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1,
                    );
                    v___x_10119_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(
                        v___x_10118_,
                        v___y_10087_,
                        v___y_10088_,
                        v___y_10089_,
                        v___y_10090_,
                    );
                    if lean_obj_tag(v___x_10119_) == 0 {
                        v_a_10120_ = lean_ctor_get(v___x_10119_, 0);
                        v_isSharedCheck_10128_ = (!lean_is_exclusive(v___x_10119_)) as u8;
                        if v_isSharedCheck_10128_ == 0 {
                            v___x_10122_ = v___x_10119_;
                            v_isShared_10123_ = v_isSharedCheck_10128_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_10120_);
                            lean_dec(v___x_10119_);
                            v___x_10122_ = lean_box(0);
                            v_isShared_10123_ = v_isSharedCheck_10128_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_10129_ = lean_ctor_get(v___x_10119_, 0);
                        v_isSharedCheck_10136_ = (!lean_is_exclusive(v___x_10119_)) as u8;
                        if v_isSharedCheck_10136_ == 0 {
                            v___x_10131_ = v___x_10119_;
                            v_isShared_10132_ = v_isSharedCheck_10136_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_10129_);
                            lean_dec(v___x_10119_);
                            v___x_10131_ = lean_box(0);
                            v_isShared_10132_ = v_isSharedCheck_10136_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_10109_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_10109_, 0, v_a_10094_);
                lean_ctor_set(v___x_10109_, 1, v___x_10092_);
                lean_ctor_set(v___x_10109_, 2, v_val_10105_);
                if v_isShared_10108_ == 0 {
                    lean_ctor_set(v___x_10107_, 0, v___x_10109_);
                    v___x_10111_ = v___x_10107_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10116_, 0, v___x_10109_);
                    v___x_10111_ = v_reuseFailAlloc_10116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_10112_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10112_, 0, v___x_10111_);
                if v_isShared_10097_ == 0 {
                    lean_ctor_set(v___x_10096_, 0, v___x_10112_);
                    v___x_10114_ = v___x_10096_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10115_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10115_, 0, v___x_10112_);
                    v___x_10114_ = v_reuseFailAlloc_10115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10114_;
            }
            5 => {
                v___x_10124_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_10124_, 0, v_a_10120_);
                if v_isShared_10123_ == 0 {
                    lean_ctor_set(v___x_10122_, 0, v___x_10124_);
                    v___x_10126_ = v___x_10122_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_10127_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10127_, 0, v___x_10124_);
                    v___x_10126_ = v_reuseFailAlloc_10127_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_10126_;
            }
            7 => {
                if v_isShared_10132_ == 0 {
                    v___x_10134_ = v___x_10131_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_10135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10135_, 0, v_a_10129_);
                    v___x_10134_ = v_reuseFailAlloc_10135_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_10134_;
            }
            9 => {
                if v_isShared_10141_ == 0 {
                    v___x_10143_ = v___x_10140_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_10144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10144_, 0, v_a_10138_);
                    v___x_10143_ = v_reuseFailAlloc_10144_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_10143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(
    mut v_thmName_10146_: *mut LeanObject,
    mut v_levels_10147_: *mut LeanObject,
    mut v___x_10148_: *mut LeanObject,
    mut v_____r_10149_: *mut LeanObject,
    mut v___y_10150_: *mut LeanObject,
    mut v___y_10151_: *mut LeanObject,
    mut v___y_10152_: *mut LeanObject,
    mut v___y_10153_: *mut LeanObject,
    mut v___y_10154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10155_: *mut LeanObject = core::ptr::null_mut();
    v_res_10155_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(
        v_thmName_10146_,
        v_levels_10147_,
        v___x_10148_,
        v_____r_10149_,
        v___y_10150_,
        v___y_10151_,
        v___y_10152_,
        v___y_10153_,
    );
    lean_dec(v___y_10153_);
    lean_dec_ref(v___y_10152_);
    lean_dec(v___y_10151_);
    lean_dec_ref(v___y_10150_);
    return v_res_10155_;
}
pub unsafe fn _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1() -> *mut LeanObject {
    let mut v___x_10157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10158_: *mut LeanObject = core::ptr::null_mut();
    v___x_10157_ = l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0;
    v___x_10158_ = l_Lean_stringToMessageData(v___x_10157_);
    return v___x_10158_;
}
pub unsafe fn _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_10160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10161_: *mut LeanObject = core::ptr::null_mut();
    v___x_10160_ = l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2;
    v___x_10161_ = l_Lean_stringToMessageData(v___x_10160_);
    return v___x_10161_;
}
pub unsafe fn l_Lean_Meta_mkCongrSimpForConst_x3f(
    mut v_declName_10162_: *mut LeanObject,
    mut v_levels_10163_: *mut LeanObject,
    mut v_a_10164_: *mut LeanObject,
    mut v_a_10165_: *mut LeanObject,
    mut v_a_10166_: *mut LeanObject,
    mut v_a_10167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10174_: u8 = 0;
    let mut v___x_10176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10178_: u8 = 0;
    let mut v_a_10179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10182_: u8 = 0;
    let mut v___x_10184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10186_: u8 = 0;
    let mut v___y_10188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_10191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmName_10197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10200_: u8 = 0;
    let mut v_options_10201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_10202_: u8 = 0;
    let mut v_inheritedTraceOptions_10203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10206_: u8 = 0;
    let mut v___x_10207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10220_: u8 = 0;
    let mut v___x_10222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10224_: u8 = 0;
    let mut v___x_10225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10228_: u8 = 0;
    let mut v___x_10229_: u8 = 0;
    let mut v___y_10231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10234_: u8 = 0;
    let mut v___x_10235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10240_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10190_ = lean_st_ref_get(v_a_10167_);
                v_env_10191_ = lean_ctor_get(v___x_10190_, 0);
                lean_inc_ref(v_env_10191_);
                lean_dec(v___x_10190_);
                v___x_10195_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once
                    ),
                    _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0,
                );
                v___x_10196_ = l_Lean_Meta_congrSimpSuffix___closed__0;
                v_thmName_10197_ = l_Lean_Name_str___override(v_declName_10162_, v___x_10196_);
                v___x_10234_ = l_Lean_Environment_containsOnBranch(v_env_10191_, v_thmName_10197_);
                lean_dec_ref(v_env_10191_);
                if v___x_10234_ == 0 {
                    lean_inc(v_thmName_10197_);
                    v___x_10235_ =
                        l_Lean_executeReservedNameAction(v_thmName_10197_, v_a_10166_, v_a_10167_);
                    if lean_obj_tag(v___x_10235_) == 0 {
                        lean_dec_ref_known(v___x_10235_, 1);
                        v___x_10236_ = lean_box(0);
                        lean_inc(v_thmName_10197_);
                        v___x_10237_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(
                            v_thmName_10197_,
                            v_levels_10163_,
                            v___x_10195_,
                            v___x_10236_,
                            v_a_10164_,
                            v_a_10165_,
                            v_a_10166_,
                            v_a_10167_,
                        );
                        v___y_10231_ = v___x_10237_;
                        state = 12;
                        continue;
                    } else {
                        lean_dec(v_levels_10163_);
                        v_a_10238_ = lean_ctor_get(v___x_10235_, 0);
                        lean_inc(v_a_10238_);
                        lean_dec_ref_known(v___x_10235_, 1);
                        v_a_10227_ = v_a_10238_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___x_10239_ = lean_box(0);
                    lean_inc(v_thmName_10197_);
                    v___x_10240_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(
                        v_thmName_10197_,
                        v_levels_10163_,
                        v___x_10195_,
                        v___x_10239_,
                        v_a_10164_,
                        v_a_10165_,
                        v_a_10166_,
                        v_a_10167_,
                    );
                    v___y_10231_ = v___x_10240_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_10170_) == 0 {
                    v_a_10171_ = lean_ctor_get(v_a_10170_, 0);
                    v_isSharedCheck_10178_ = (!lean_is_exclusive(v_a_10170_)) as u8;
                    if v_isSharedCheck_10178_ == 0 {
                        v___x_10173_ = v_a_10170_;
                        v_isShared_10174_ = v_isSharedCheck_10178_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_10171_);
                        lean_dec(v_a_10170_);
                        v___x_10173_ = lean_box(0);
                        v_isShared_10174_ = v_isSharedCheck_10178_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_10179_ = lean_ctor_get(v_a_10170_, 0);
                    v_isSharedCheck_10186_ = (!lean_is_exclusive(v_a_10170_)) as u8;
                    if v_isSharedCheck_10186_ == 0 {
                        v___x_10181_ = v_a_10170_;
                        v_isShared_10182_ = v_isSharedCheck_10186_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10179_);
                        lean_dec(v_a_10170_);
                        v___x_10181_ = lean_box(0);
                        v_isShared_10182_ = v_isSharedCheck_10186_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_10174_ == 0 {
                    v___x_10176_ = v___x_10173_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10177_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10177_, 0, v_a_10171_);
                    v___x_10176_ = v_reuseFailAlloc_10177_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_10176_;
            }
            4 => {
                if v_isShared_10182_ == 0 {
                    lean_ctor_set_tag(v___x_10181_, 0);
                    v___x_10184_ = v___x_10181_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10185_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10185_, 0, v_a_10179_);
                    v___x_10184_ = v_reuseFailAlloc_10185_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10184_;
            }
            6 => {
                v_a_10189_ = lean_ctor_get(v___y_10188_, 0);
                lean_inc(v_a_10189_);
                lean_dec_ref(v___y_10188_);
                v_a_10170_ = v_a_10189_;
                state = 1;
                continue;
            }
            7 => {
                v___x_10193_ = lean_box(0);
                v___x_10194_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(
                    v___x_10193_,
                    v_a_10164_,
                    v_a_10165_,
                    v_a_10166_,
                    v_a_10167_,
                );
                v___y_10188_ = v___x_10194_;
                state = 6;
                continue;
            }
            8 => {
                if v___y_10200_ == 0 {
                    v_options_10201_ = lean_ctor_get(v_a_10166_, 2);
                    v_hasTrace_10202_ = lean_ctor_get_uint8(
                        v_options_10201_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_10202_ == 0 {
                        lean_dec_ref(v___y_10199_);
                        lean_dec(v_thmName_10197_);
                        state = 7;
                        continue;
                    } else {
                        v_inheritedTraceOptions_10203_ = lean_ctor_get(v_a_10166_, 13);
                        v___x_10204_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
                        v___x_10205_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
                        v___x_10206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_10203_,
                            v_options_10201_,
                            v___x_10205_,
                        );
                        if v___x_10206_ == 0 {
                            lean_dec_ref(v___y_10199_);
                            lean_dec(v_thmName_10197_);
                            state = 7;
                            continue;
                        } else {
                            v___x_10207_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once
                                ),
                                _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1,
                            );
                            v___x_10208_ = l_Lean_MessageData_ofName(v_thmName_10197_);
                            v___x_10209_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_10209_, 0, v___x_10207_);
                            lean_ctor_set(v___x_10209_, 1, v___x_10208_);
                            v___x_10210_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once
                                ),
                                _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3,
                            );
                            v___x_10211_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_10211_, 0, v___x_10209_);
                            lean_ctor_set(v___x_10211_, 1, v___x_10210_);
                            v___x_10212_ = l_Lean_Exception_toMessageData(v___y_10199_);
                            v___x_10213_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_10213_, 0, v___x_10211_);
                            lean_ctor_set(v___x_10213_, 1, v___x_10212_);
                            v___x_10214_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_10204_, v___x_10213_, v_a_10164_, v_a_10165_, v_a_10166_, v_a_10167_);
                            if lean_obj_tag(v___x_10214_) == 0 {
                                v_a_10215_ = lean_ctor_get(v___x_10214_, 0);
                                lean_inc(v_a_10215_);
                                lean_dec_ref_known(v___x_10214_, 1);
                                v___x_10216_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(
                                    v_a_10215_, v_a_10164_, v_a_10165_, v_a_10166_, v_a_10167_,
                                );
                                v___y_10188_ = v___x_10216_;
                                state = 6;
                                continue;
                            } else {
                                v_a_10217_ = lean_ctor_get(v___x_10214_, 0);
                                v_isSharedCheck_10224_ = (!lean_is_exclusive(v___x_10214_)) as u8;
                                if v_isSharedCheck_10224_ == 0 {
                                    v___x_10219_ = v___x_10214_;
                                    v_isShared_10220_ = v_isSharedCheck_10224_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_10217_);
                                    lean_dec(v___x_10214_);
                                    v___x_10219_ = lean_box(0);
                                    v_isShared_10220_ = v_isSharedCheck_10224_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_thmName_10197_);
                    v___x_10225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10225_, 0, v___y_10199_);
                    return v___x_10225_;
                }
            }
            9 => {
                if v_isShared_10220_ == 0 {
                    v___x_10222_ = v___x_10219_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_10223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10223_, 0, v_a_10217_);
                    v___x_10222_ = v_reuseFailAlloc_10223_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_10222_;
            }
            11 => {
                v___x_10228_ = l_Lean_Exception_isInterrupt(v_a_10227_);
                if v___x_10228_ == 0 {
                    lean_inc_ref(v_a_10227_);
                    v___x_10229_ = l_Lean_Exception_isRuntime(v_a_10227_);
                    v___y_10199_ = v_a_10227_;
                    v___y_10200_ = v___x_10229_;
                    state = 8;
                    continue;
                } else {
                    v___y_10199_ = v_a_10227_;
                    v___y_10200_ = v___x_10228_;
                    state = 8;
                    continue;
                }
            }
            12 => {
                if lean_obj_tag(v___y_10231_) == 0 {
                    lean_dec(v_thmName_10197_);
                    v_a_10232_ = lean_ctor_get(v___y_10231_, 0);
                    lean_inc(v_a_10232_);
                    lean_dec_ref_known(v___y_10231_, 1);
                    v_a_10170_ = v_a_10232_;
                    state = 1;
                    continue;
                } else {
                    v_a_10233_ = lean_ctor_get(v___y_10231_, 0);
                    lean_inc(v_a_10233_);
                    lean_dec_ref_known(v___y_10231_, 1);
                    v_a_10227_ = v_a_10233_;
                    state = 11;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(
    mut v_declName_10241_: *mut LeanObject,
    mut v_levels_10242_: *mut LeanObject,
    mut v_a_10243_: *mut LeanObject,
    mut v_a_10244_: *mut LeanObject,
    mut v_a_10245_: *mut LeanObject,
    mut v_a_10246_: *mut LeanObject,
    mut v_a_10247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10248_: *mut LeanObject = core::ptr::null_mut();
    v_res_10248_ = l_Lean_Meta_mkCongrSimpForConst_x3f(
        v_declName_10241_,
        v_levels_10242_,
        v_a_10243_,
        v_a_10244_,
        v_a_10245_,
        v_a_10246_,
    );
    lean_dec(v_a_10246_);
    lean_dec_ref(v_a_10245_);
    lean_dec(v_a_10244_);
    lean_dec_ref(v_a_10243_);
    return v_res_10248_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CongrTheorems(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ReservedNameAction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_instInhabitedCongrArgKind_default =
        _init_l_Lean_Meta_instInhabitedCongrArgKind_default();
    l_Lean_Meta_instInhabitedCongrArgKind = _init_l_Lean_Meta_instInhabitedCongrArgKind();
    res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_congrKindsExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_congrKindsExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CongrTheorems(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CongrTheorems(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ReservedNameAction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Subst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CongrTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_CongrTheorems(builtin);
}
